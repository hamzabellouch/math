import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPeriodizationIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevConjugation
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace OAI

/-! # Poisson summation for the actual twelve-dimensional Fourier lattice

The periodic function is the locally normally convergent sum of Schwartz
translates.  Computing its Fourier coefficients on a fundamental cell and
using the existing multivariate Fourier basis identifies its Fourier series.
-/

open Set MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem unitTorus_integral_eq_frequencyCell (f : UnitAddTorus (Fin 12) → ℂ) :
    (∫ x : UnitAddTorus (Fin 12), f x) =
      ∫ x in frequencyCell, f (unitTorusProjection x) := by
  let A : Set (Fin 12 → ℝ) := Set.pi Set.univ (fun _ => Ico (0 : ℝ) 1)
  let B : Set (Fin 12 → ℝ) := Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1)
  have hB : B = {x : Fin 12 → ℝ | ∀ i, x i ∈ Ioc 0 1} := by
    ext x
    simp [B]
  have hAB : A =ᵐ[volume] B := by
    exact Measure.ae_eq_set_pi (fun _ _ => Ico_ae_eq_Ioc)
  have hcell : (WithLp.ofLp : E → Fin 12 → ℝ) ⁻¹' A = frequencyCell := by
    ext x
    simp only [A, frequencyCell, ZSpan.mem_fundamentalDomain, Set.mem_preimage,
      Set.mem_pi, Set.mem_univ, forall_const,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  calc
    _ = ∫ x in B, f (fun j => (x j : UnitAddCircle)) := by
      rw [hB]
      simpa only [zero_add] using!
        UnitAddTorus.integral_preimage f (fun _ => 0)
    _ = ∫ x in A, f (fun j => (x j : UnitAddCircle)) := setIntegral_congr_set hAB.symm
    _ = _ := by
      have h := (PiLp.volume_preserving_ofLp (Fin 12)).setIntegral_preimage_emb
        (MeasurableEquiv.toLp 2 (Fin 12 → ℝ)).symm.measurableEmbedding
        (fun x : Fin 12 → ℝ => f (fun j => (x j : UnitAddCircle))) A
      simpa only [hcell, unitTorusProjection] using! h.symm

noncomputable def integerFourierCharacter (n : frequencyLattice) : C(E, ℂ) :=
  (UnitAddTorus.mFourier (frequencyCoordinates n)).comp
    ⟨unitTorusProjection, unitTorusProjection_isOpenQuotientMap.continuous⟩

theorem integerFourierCharacter_norm (n : frequencyLattice) (x : E) :
    ‖integerFourierCharacter n x‖ = 1 := by
  simp [integerFourierCharacter, UnitAddTorus.mFourier, norm_prod, fourier_apply,
    Circle.norm_coe]

theorem unitTorusProjection_add_lattice (x : E) (n : frequencyLattice) :
    unitTorusProjection (x + n) = unitTorusProjection x := by
  funext j
  change ((x j + (n : E) j : ℝ) : UnitAddCircle) = (x j : UnitAddCircle)
  rw [AddCircle.coe_add, add_eq_left]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  refine ⟨frequencyCoordinates n j, ?_⟩
  simpa only [zsmul_eq_mul, mul_one] using frequencyCoordinates_coe n j

theorem integerFourierCharacter_periodic (m n : frequencyLattice) (x : E) :
    integerFourierCharacter m (x + n) = integerFourierCharacter m x := by
  change UnitAddTorus.mFourier _ (unitTorusProjection (x + n)) = _
  rw [unitTorusProjection_add_lattice]
  rfl

theorem integerFourierCharacter_exp (n : frequencyLattice) (x : E) :
    integerFourierCharacter n x =
      Complex.exp (((2 * Real.pi * ⟪x, (n : E)⟫ : ℝ) : ℂ) * Complex.I) := by
  simp only [integerFourierCharacter, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    UnitAddTorus.mFourier, unitTorusProjection, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [PiLp.inner_apply, Real.inner_apply, Complex.ofReal_mul,
    Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← frequencyCoordinates_coe n j]
  push_cast
  ring

theorem schwartzPeriodizedTorus_fourierCoeff (K : 𝓢(E, ℂ)) (n : frequencyLattice) :
    UnitAddTorus.mFourierCoeff (schwartzPeriodizedTorus K) (frequencyCoordinates n) =
      𝓕 (K : E → ℂ) (n : E) := by
  have hneg : -frequencyCoordinates n = frequencyCoordinates (-n) := by
    funext j
    exact (frequencyCoordinates_neg n j).symm
  unfold UnitAddTorus.mFourierCoeff
  rw [unitTorus_integral_eq_frequencyCell]
  simp only [schwartzPeriodizedTorus_projection, smul_eq_mul, hneg]
  change (∫ x in frequencyCell, integerFourierCharacter (-n) x * schwartzPeriodization K x) = _
  rw [schwartzPeriodization_twisted_integral K (integerFourierCharacter (-n))
    (integerFourierCharacter_norm (-n)) (fun x m => integerFourierCharacter_periodic (-n) m x)]
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integerFourierCharacter_exp]
  simp only [Submodule.coe_neg, inner_neg_right, smul_eq_mul]
  congr 2
  push_cast
  ring

theorem schwartz_poisson_summation (K : 𝓢(E, ℂ)) (x : E) :
    (∑' n : frequencyLattice, K (x + n)) =
      ∑' n : frequencyLattice, 𝓕 (K : E → ℂ) (n : E) * integerFourierCharacter n x := by
  have hS : Summable (fun n : frequencyLattice => 𝓕 (K : E → ℂ) (n : E)) := by
    apply Summable.of_norm
    simpa only [zero_add, SchwartzMap.fourier_coe] using!
      summable_norm_schwartz_lattice (𝓕 K) (0 : E)
  have hc : Summable (UnitAddTorus.mFourierCoeff (schwartzPeriodizedTorus K)) := by
    apply frequencyCoordinatesEquiv.toEquiv.summable_iff.mp
    change Summable (fun n : frequencyLattice =>
      UnitAddTorus.mFourierCoeff (schwartzPeriodizedTorus K) (frequencyCoordinates n))
    simpa only [frequencyCoordinatesEquiv_apply, schwartzPeriodizedTorus_fourierCoeff] using hS
  have ht := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hc (unitTorusProjection x)
  have heq := (frequencyCoordinatesEquiv.toEquiv.hasSum_iff).mpr ht
  change HasSum (fun n : frequencyLattice =>
    UnitAddTorus.mFourierCoeff (schwartzPeriodizedTorus K) (frequencyCoordinates n) *
      UnitAddTorus.mFourier (frequencyCoordinates n) (unitTorusProjection x)) _ at heq
  simp only [schwartzPeriodizedTorus_fourierCoeff] at heq
  rw [schwartzPeriodizedTorus_projection, schwartzPeriodization_apply] at heq
  exact heq.tsum_eq.symm

end DefocusingNLS

end OAI
