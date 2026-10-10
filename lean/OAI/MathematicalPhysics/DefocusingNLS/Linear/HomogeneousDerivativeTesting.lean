import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalDerivative
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Data.Fin.Rev

namespace OAI

/-! # Schwartz testing of the completed physical derivatives

The bounded L² derivative on Y is the weak derivative of its faithful
physical representative. The test derivative is written in reverse order,
as required by transposition, and the sign is exactly (-1)^N.
-/

open MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem cZero_point_norm_le (f : C₀(E, ℂ)) (x : E) : ‖f x‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_coe_le_norm f.toBCF x).trans_eq
    ZeroAtInftyContinuousMap.norm_toBCF_eq_norm

private theorem integrable_cZero_test (ψ : 𝓢(E, ℂ)) (f : C₀(E, ℂ)) :
    Integrable (fun x : E => inner ℝ (ψ x) (f x)) := by
  apply (ψ.integrable.norm.const_mul ‖f‖).mono'
    (ψ.continuous.aestronglyMeasurable.inner f.continuous.aestronglyMeasurable)
  filter_upwards [] with x
  calc
    ‖inner ℝ (ψ x) (f x)‖ ≤ ‖ψ x‖ * ‖f x‖ := norm_inner_le_norm _ _
    _ ≤ ‖f‖ * ‖ψ x‖ := by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (cZero_point_norm_le f x) (norm_nonneg (ψ x))

/-- A Schwartz test acts continuously on the physical C0 realization. -/
noncomputable def physicalSchwartzTest (ψ : 𝓢(E, ℂ)) : C₀(E, ℂ) →L[ℝ] ℝ := by
  let L : C₀(E, ℂ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ x : E, inner ℝ (ψ x) (f x)
      map_add' := by
        intro f g
        simp only [ZeroAtInftyContinuousMap.add_apply, inner_add_right]
        exact integral_add (integrable_cZero_test ψ f) (integrable_cZero_test ψ g)
      map_smul' := by
        intro c f
        simp only [ZeroAtInftyContinuousMap.smul_apply, inner_smul_right, smul_eq_mul]
        exact integral_const_mul _ _ }
  refine L.mkContinuous (∫ x : E, ‖ψ x‖) ?_
  intro f
  apply (norm_integral_le_integral_norm (fun x : E => inner ℝ (ψ x) (f x))).trans
  calc
    (∫ x : E, ‖inner ℝ (ψ x) (f x)‖) ≤ ∫ x : E, ‖f‖ * ‖ψ x‖ := by
      apply integral_mono (integrable_cZero_test ψ f).norm (ψ.integrable.norm.const_mul ‖f‖)
      intro x
      exact (norm_inner_le_norm _ _).trans
        (by simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (cZero_point_norm_le f x) (norm_nonneg (ψ x)))
    _ = (∫ x : E, ‖ψ x‖) * ‖f‖ := by rw [integral_const_mul, mul_comm]

@[simp] theorem physicalSchwartzTest_apply (ψ : 𝓢(E, ℂ)) (f : C₀(E, ℂ)) :
    physicalSchwartzTest ψ f = ∫ x : E, inner ℝ (ψ x) (f x) := rfl

/-- The transposed ordered derivative has the reversed list of directions. -/
theorem schwartz_iteratedDerivative_testing (N : ℕ) (v : Fin N → E)
    (ψ f : 𝓢(E, ℂ)) :
    (∫ x : E, inner ℝ (ψ x) ((∂^{v} f) x)) =
      (-1 : ℝ) ^ N * ∫ x : E, inner ℝ ((∂^{fun i => v (Fin.rev i)} ψ) x) (f x) := by
  induction N generalizing ψ f with
  | zero => simp
  | succ N ih =>
      rw [iteratedLineDerivOp_succ_left]
      have hibp := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
        (μ := (volume : Measure E)) ψ (∂^{Fin.tail v} f) (innerSL ℝ) (v 0)
      change (∫ x : E, inner ℝ (ψ x) ((∂_{v 0} (∂^{Fin.tail v} f)) x)) =
        -(∫ x : E, inner ℝ ((∂_{v 0} ψ) x) ((∂^{Fin.tail v} f) x)) at hibp
      rw [hibp]
      rw [ih (Fin.tail v) (∂_{v 0} ψ) f]
      have ht : (∂^{fun i => v (Fin.rev i)} ψ) =
          ∂^{fun i => Fin.tail v (Fin.rev i)} (∂_{v 0} ψ) := by
        rw [iteratedLineDerivOp_succ_right]
        simp only [Fin.rev_last]
        congr 1
        funext i
        simp only [Fin.init_def, Fin.tail_def, Fin.rev_castSucc]
      rw [ht, pow_succ]
      ring

/-- Completed ordered derivatives satisfy the exact weak integration-by-parts
identity against every Schwartz test. -/
theorem homogeneousPhysicalDerivative_testing (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (j : Fin N → Fin 12) (ψ : 𝓢(E, ℂ)) (u : HomogeneousY a N) :
    inner ℝ (ψ.toLp 2 volume) (homogeneousPhysicalDerivative a N ha ha1 hk j u) =
      (-1 : ℝ) ^ N * ∫ x : E,
        inner ℝ ((∂^{fun i => (EuclideanSpace.basisFun (Fin 12) ℝ) (j (Fin.rev i))} ψ) x)
          (homogeneousPhysicalCLM a N ha ha1 hk u x) := by
  let test := ∂^{fun i => (EuclideanSpace.basisFun (Fin 12) ℝ) (j (Fin.rev i))} ψ
  let L : HomogeneousY a N →L[ℝ] ℝ :=
    (innerSL ℝ (ψ.toLp 2 volume)).comp
      ((homogeneousPhysicalDerivative a N ha ha1 hk j).restrictScalars ℝ)
  let R : HomogeneousY a N →L[ℝ] ℝ :=
    ((-1 : ℝ) ^ N) • (physicalSchwartzTest test).comp
      ((homogeneousPhysicalCLM a N ha ha1 hk).restrictScalars ℝ)
  have hLR : L = R := by
    apply DFunLike.coe_injective
    apply (homogeneousSchwartzEmbedding_dense a N ha ha1 hk).equalizer L.continuous R.continuous
    funext f
    change L (homogeneousSchwartzEmbedding a N ha ha1 hk f) =
      R (homogeneousSchwartzEmbedding a N ha ha1 hk f)
    have hleft : L (homogeneousSchwartzEmbedding a N ha ha1 hk f) =
        ∫ x : E, inner ℝ (ψ x) (homogeneousOrderedDerivative N j f x) := by
      change inner ℝ (ψ.toLp 2 volume)
        (homogeneousPhysicalDerivative a N ha ha1 hk j
          (homogeneousSchwartzEmbedding a N ha ha1 hk f)) = _
      rw [homogeneousPhysicalDerivative_Schwartz, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [SchwartzMap.coeFn_toLp ψ 2 volume,
        SchwartzMap.coeFn_toLp (homogeneousOrderedDerivative N j f) 2 volume] with x hx hy
      change inner ℝ (ψ.toLp 2 volume x)
        ((homogeneousOrderedDerivative N j f).toLp 2 volume x) = _
      rw [hx, hy]
    rw [hleft]
    change (∫ x : E, inner ℝ (ψ x)
      ((∂^{fun i => (EuclideanSpace.basisFun (Fin 12) ℝ) (j i)} f) x)) = _
    rw [schwartz_iteratedDerivative_testing]
    change (-1 : ℝ) ^ N * (∫ x : E, inner ℝ (test x) (f x)) =
      (-1 : ℝ) ^ N * ∫ x : E, inner ℝ (test x)
        (homogeneousPhysicalCLM a N ha ha1 hk
          (homogeneousSchwartzEmbedding a N ha ha1 hk f) x)
    simp only [homogeneousPhysicalCLM_Schwartz]
  have h := congrArg (fun T : HomogeneousY a N →L[ℝ] ℝ => T u) hLR
  exact h

end DefocusingNLS

end OAI
