import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialTestPairing
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialMeasure
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPolarTesting
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousAngularProjection

namespace OAI

/-! # Exact radial weak derivatives of the completed homogeneous space

The identity is proved on Schwartz functions by radial integration by parts,
then extended through the faithful Y completion using two bounded functionals.
No classical high derivative of the completed vector is assumed.
-/

open MeasureTheory Set
open scoped SchwartzMap ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem radial_tensor_inner (t : ℝ) (h ψ z : ℂ) :
    inner ℂ ((t : ℂ) * h * star ψ) z = ψ * star h * ((t : ℂ) * z) := by
  rw [RCLike.inner_apply']
  change star ((t : ℂ) * h * star ψ) * z = _
  rw [star_mul, star_mul, star_star]
  have ht : star (t : ℂ) = (t : ℂ) := by simp
  rw [ht]
  ring

/-- Dense-domain version of the exact transposed radial identity. -/
theorem homogeneousRadialTest_Schwartz (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (h : PhysicalUnitSphere → ℂ) (hh : MemLp h 2 physicalSphereMeasure)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ r, r ≤ 0 → ψ r = 0) (f : 𝓢(E, ℂ)) :
    homogeneousRadialTest a N ha ha1 hk h (fun r => ψ r) hh (memLp_radialSchwartz ψ)
        (homogeneousSchwartzEmbedding a N ha ha1 hk f) =
      (-1 : ℂ) ^ N * physicalPolarTest
        (fun p => star (h p.1) * radialTransposedTest N ψ p.2)
        (integrable_linePolarProduct h (radialTransposedTest N ψ)
          (hh.integrable (by norm_num)) (radialTransposedTest N ψ).integrable)
        (homogeneousPhysicalCLM a N ha ha1 hk
          (homogeneousSchwartzEmbedding a N ha ha1 hk f)) := by
  classical
  let u := homogeneousSchwartzEmbedding a N ha ha1 hk f
  let D (j : Fin N → Fin 12) (p : PhysicalUnitSphere × PhysicalPositiveRadius) : ℂ :=
    inner ℂ ((radialTensorCoefficient N j p.1 : ℂ) * h p.1 * star (ψ p.2.1))
      (homogeneousOrderedDerivative N j f (p.2.1 • p.1.1))
  have hi (j : Fin N → Fin 12) : Integrable (D j) physicalPolarMeasure := by
    let W := polarProductTest (fun ω => (radialTensorCoefficient N j ω : ℂ) * h ω)
      (fun r => ψ r) (memLp_radialTensor_test N j h hh) (memLp_radialSchwartz ψ)
    let T := homogeneousPolarDerivative a N ha ha1 hk j u
    apply (L2.integrable_inner (𝕜 := ℂ) W T).congr
    filter_upwards [(memLp_polarProductTest
      (fun ω => (radialTensorCoefficient N j ω : ℂ) * h ω) (fun r => ψ r)
      (memLp_radialTensor_test N j h hh) (memLp_radialSchwartz ψ)).coeFn_toLp,
      homogeneousPolarDerivative_Schwartz_ae a N ha ha1 hk j f] with p hW hT
    change W p = _ at hW
    change T p = _ at hT
    change inner ℂ (W p) (T p) = D j p
    rw [hW, hT]
  have he (j : Fin N → Fin 12) :
      homogeneousRadialTestComponent a N ha ha1 hk j h (fun r => ψ r) hh
        (memLp_radialSchwartz ψ) u = ∫ p, D j p ∂physicalPolarMeasure := by
    change inner ℂ
      (polarProductTest (fun ω => (radialTensorCoefficient N j ω : ℂ) * h ω)
        (fun r => ψ r) (memLp_radialTensor_test N j h hh) (memLp_radialSchwartz ψ))
      (homogeneousPolarDerivative a N ha ha1 hk j u) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_polarProductTest
      (fun ω => (radialTensorCoefficient N j ω : ℂ) * h ω) (fun r => ψ r)
      (memLp_radialTensor_test N j h hh) (memLp_radialSchwartz ψ)).coeFn_toLp,
      homogeneousPolarDerivative_Schwartz_ae a N ha ha1 hk j f] with p hW hT
    change polarProductTest (fun ω => (radialTensorCoefficient N j ω : ℂ) * h ω)
      (fun r => ψ r) (memLp_radialTensor_test N j h hh)
      (memLp_radialSchwartz ψ) p = _ at hW
    change homogeneousPolarDerivative a N ha ha1 hk j u p = _ at hT
    rw [hW, hT]
  have hsum : Integrable (fun p => ∑ j : Fin N → Fin 12, D j p) physicalPolarMeasure :=
    integrable_finsetSum _ (fun j _ => hi j)
  have hpoint (ω : PhysicalUnitSphere) :
      (∫ r : PhysicalPositiveRadius, ∑ j : Fin N → Fin 12, D j (ω, r)
        ∂physicalRadiusMeasure) =
        (-1 : ℂ) ^ N * star (h ω) *
          ∫ r : ℝ, radialTransposedTest N ψ r * f (r • ω.1) := by
    let S : ℝ → ℂ := fun r => ∑ j : Fin N → Fin 12,
      (radialTensorCoefficient N j ω : ℂ) * homogeneousOrderedDerivative N j f (r • ω.1)
    have hd (r : PhysicalPositiveRadius) :
        (∑ j : Fin N → Fin 12, D j (ω, r)) = ψ r * star (h ω) * S r := by
      simp only [D, radial_tensor_inner, S, Finset.mul_sum]
    simp_rw [hd]
    rw [integral_physicalRadiusMeasure (fun r => ψ r * star (h ω) * S r)]
    calc
      (∫ r in Ioi (0 : ℝ), r ^ (11 : ℕ) • (ψ r * star (h ω) * S r)) =
          ∫ r in Ioi (0 : ℝ), star (h ω) * (radialWeightedSchwartzTest ψ r * S r) := by
        apply integral_congr_ae
        filter_upwards [] with r
        simp only [radialWeightedSchwartzTest_apply, Complex.real_smul, Complex.ofReal_pow]
        ring
      _ = ∫ r : ℝ, star (h ω) * (radialWeightedSchwartzTest ψ r * S r) :=
        integral_Ioi_eq_of_zero_nonpositive _ (fun r hr => by simp [hψ r hr])
      _ = star (h ω) * ((-1 : ℂ) ^ N *
          ∫ r : ℝ, radialTransposedTest N ψ r * f (r • ω.1)) := by
        rw [integral_const_mul]
        change star (h ω) * (∫ r : ℝ, radialWeightedSchwartzTest ψ r *
          (∑ j : Fin N → Fin 12, (radialTensorCoefficient N j ω : ℂ) *
            homogeneousOrderedDerivative N j f (r • ω.1))) = _
        rw [schwartz_radial_integral_mul_by_parts]
        rfl
      _ = _ := by ring
  calc
    homogeneousRadialTest a N ha ha1 hk h (fun r => ψ r) hh
        (memLp_radialSchwartz ψ) u =
        ∑ j : Fin N → Fin 12, ∫ p, D j p ∂physicalPolarMeasure := by
      simp only [homogeneousRadialTest, sum_apply, he]
    _ = ∫ p, ∑ j : Fin N → Fin 12, D j p ∂physicalPolarMeasure :=
      (integral_finsetSum _ (fun j _ => hi j)).symm
    _ = ∫ ω, ∫ r, ∑ j : Fin N → Fin 12, D j (ω, r)
        ∂physicalRadiusMeasure ∂physicalSphereMeasure := integral_prod _ hsum
    _ = (-1 : ℂ) ^ N * ∫ ω, star (h ω) *
        (∫ r : ℝ, radialTransposedTest N ψ r * f (r • ω.1))
        ∂physicalSphereMeasure := by
      simp_rw [hpoint, mul_assoc]
      rw [integral_const_mul]
    _ = _ := by
      rw [physicalPolarTest_product h (radialTransposedTest N ψ)
        (hh.integrable (by norm_num)) (radialTransposedTest N ψ).integrable]
      simp only [homogeneousPhysicalCLM_Schwartz]

/-- Exact weak radial differentiation for every vector in the completion. -/
theorem homogeneousRadial_weak_testing (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (h : PhysicalUnitSphere → ℂ) (hh : MemLp h 2 physicalSphereMeasure)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ r, r ≤ 0 → ψ r = 0) (u : HomogeneousY a N) :
    homogeneousRadialTest a N ha ha1 hk h (fun r => ψ r) hh (memLp_radialSchwartz ψ) u =
      (-1 : ℂ) ^ N * physicalPolarTest
        (fun p => star (h p.1) * radialTransposedTest N ψ p.2)
        (integrable_linePolarProduct h (radialTransposedTest N ψ)
          (hh.integrable (by norm_num)) (radialTransposedTest N ψ).integrable)
        (homogeneousPhysicalCLM a N ha ha1 hk u) := by
  let L := homogeneousRadialTest a N ha ha1 hk h (fun r => ψ r) hh (memLp_radialSchwartz ψ)
  let R : HomogeneousY a N →L[ℂ] ℂ := (-1 : ℂ) ^ N •
    (physicalPolarTest (fun p => star (h p.1) * radialTransposedTest N ψ p.2)
      (integrable_linePolarProduct h (radialTransposedTest N ψ)
        (hh.integrable (by norm_num)) (radialTransposedTest N ψ).integrable)).comp
      (homogeneousPhysicalCLM a N ha ha1 hk)
  have heq : L = R := by
    apply DFunLike.coe_injective
    apply (homogeneousSchwartzEmbedding_dense a N ha ha1 hk).equalizer L.continuous R.continuous
    funext f
    exact homogeneousRadialTest_Schwartz a N ha ha1 hk h hh ψ hψ f
  exact congrArg (fun T : HomogeneousY a N →L[ℂ] ℂ => T u) heq

/-- Integral form: the contracted L² derivative is the distributional Nth
radial derivative of the actual angular projection. -/
theorem homogeneousAngularProjection_weak_derivative (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (h : PhysicalUnitSphere → ℂ) (hh : MemLp h 2 physicalSphereMeasure)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ r, r ≤ 0 → ψ r = 0) (u : HomogeneousY a N) :
    (∫ r, ψ r * homogeneousRadialAngularDerivative a N ha ha1 hk h u r
      ∂physicalRadiusMeasure) =
      (-1 : ℂ) ^ N * ∫ r : ℝ, radialTransposedTest N ψ r *
        homogeneousAngularProjection a N ha ha1 hk h u r := by
  rw [← homogeneousRadialTest_apply a N ha ha1 hk h (fun r => ψ r) hh
    (memLp_radialSchwartz ψ) u, homogeneousRadial_weak_testing a N ha ha1 hk h hh ψ hψ u,
    physicalPolarTest_apply]
  congr 1
  let F := homogeneousPhysicalCLM a N ha ha1 hk u
  let K : PhysicalUnitSphere × ℝ → ℂ := fun p => star (h p.1) * radialTransposedTest N ψ p.2
  have hK : Integrable K physicalLinePolarMeasure :=
    integrable_linePolarProduct h (radialTransposedTest N ψ)
      (hh.integrable (by norm_num)) (radialTransposedTest N ψ).integrable
  have hint : Integrable (fun p : PhysicalUnitSphere × ℝ => K p * F (p.2 • p.1.1))
      physicalLinePolarMeasure := by
    apply (hK.norm.mul_const ‖F‖).mono'
      (hK.aestronglyMeasurable.mul
        (F.continuous.comp (continuous_snd.smul continuous_fst.subtype_val)).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖K p * F (p.2 • p.1.1)‖ ≤ ‖K p‖ * ‖F‖
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (BoundedContinuousFunction.norm_coe_le_norm F.toBCF _).trans_eq
      ZeroAtInftyContinuousMap.norm_toBCF_eq_norm
  change (∫ p, K p * F (p.2 • p.1.1) ∂physicalSphereMeasure.prod volume) = _
  rw [integral_prod_symm _ hint]
  apply integral_congr_ae
  filter_upwards [] with r
  change (∫ ω, (star (h ω) * radialTransposedTest N ψ r) * F (r • ω.1)
    ∂physicalSphereMeasure) =
    radialTransposedTest N ψ r *
      (∫ ω, inner ℂ (h ω) (F (r • ω.1)) ∂physicalSphereMeasure)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [RCLike.inner_apply']
  change (star (h ω) * radialTransposedTest N ψ r) * F (r • ω.1) =
    radialTransposedTest N ψ r * (star (h ω) * F (r • ω.1))
  ring

end DefocusingNLS

end OAI
