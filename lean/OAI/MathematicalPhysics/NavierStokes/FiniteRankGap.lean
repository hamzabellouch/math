import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# Finite-rank gap and determinant perturbations

The coercivity argument for the moment matrix in *Stationary instability and nonuniqueness
for axisymmetric swirl-free Navier–Stokes*, Section 2, gives a lower norm bound in terms of
the residual map. Perturbations smaller than this bound preserve injectivity and, in finite
dimensions over the reals, the sign of the determinant.
-/

noncomputable section

namespace StationaryNS

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The moment matrix `I + BC`, expressed without choosing coordinates. -/
def momentMatrix (B : E →L[ℝ] F) (C : F →L[ℝ] E) : F →L[ℝ] F :=
  ContinuousLinearMap.id ℝ F + B.comp C

/-- The algebraic least-singular-value estimate for the moment matrix. The residual map `R`
and the coercivity hypothesis give a lower norm bound without a finite-dimensional assumption. -/
theorem finite_rank_gap (B : E →L[ℝ] F) (C : F →L[ℝ] E)
    (R : F →L[ℝ] E →L[ℝ] ℝ) {ε β δ : ℝ}
    (hε : 0 < ε) (hB : ‖B‖ ≤ β) (hR : ‖R‖ ≤ δ)
    (hcoercive : ∀ y, ε * ‖C y‖ ^ 2 ≤ R (momentMatrix B C y) (C y)) (y : F) :
    ε / (ε + β * δ) * ‖y‖ ≤ ‖momentMatrix B C y‖ := by
  have hβ : 0 ≤ β := (norm_nonneg B).trans hB
  have hδ : 0 ≤ δ := (norm_nonneg R).trans hR
  have hpair : R (momentMatrix B C y) (C y) ≤
      δ * ‖momentMatrix B C y‖ * ‖C y‖ := by
    calc
      R (momentMatrix B C y) (C y) ≤ |R (momentMatrix B C y) (C y)| := le_abs_self _
      _ = ‖R (momentMatrix B C y) (C y)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖R (momentMatrix B C y)‖ * ‖C y‖ := (R _).le_opNorm _
      _ ≤ (‖R‖ * ‖momentMatrix B C y‖) * ‖C y‖ := by
        gcongr
        exact R.le_opNorm _
      _ ≤ δ * ‖momentMatrix B C y‖ * ‖C y‖ := by gcongr
  have hC : ε * ‖C y‖ ≤ δ * ‖momentMatrix B C y‖ := by
    by_cases hz : ‖C y‖ = 0
    · simp only [hz, mul_zero]
      positivity
    · have hp : 0 < ‖C y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      apply (mul_le_mul_iff_of_pos_right hp).mp
      nlinarith [hcoercive y]
  have htriangle : ‖y‖ ≤ ‖momentMatrix B C y‖ + β * ‖C y‖ := by
    have hid : y = momentMatrix B C y - B (C y) := by
      simp [momentMatrix]
    calc
      ‖y‖ = ‖momentMatrix B C y - B (C y)‖ := congrArg norm hid
      _ ≤ ‖momentMatrix B C y‖ + ‖B (C y)‖ := norm_sub_le _ _
      _ ≤ ‖momentMatrix B C y‖ + β * ‖C y‖ :=
        add_le_add_right ((B.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hB (norm_nonneg _))) _
  have hden : 0 < ε + β * δ := add_pos_of_pos_of_nonneg hε (mul_nonneg hβ hδ)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_le_mul_of_nonneg_left htriangle hε.le,
    mul_le_mul_of_nonneg_left hC hβ]

/-- A perturbation smaller than a lower norm bound is injective, in any dimension. -/
theorem injective_of_perturbation (J P : E →L[ℝ] E) {γ : ℝ}
    (hgap : ∀ x, γ * ‖x‖ ≤ ‖J x‖) (hpert : ‖P - J‖ < γ) :
    Function.Injective P := by
  intro x y hxy
  have hz : P (x - y) = 0 := by simp only [map_sub, hxy, sub_self]
  have hdiff : ‖(P - J) (x - y)‖ = ‖J (x - y)‖ := by
    simp only [sub_apply, hz, zero_sub, norm_neg]
  have hupper : ‖J (x - y)‖ ≤ ‖P - J‖ * ‖x - y‖ := by
    simpa only [hdiff] using (P - J).le_opNorm (x - y)
  have hnorm : ‖x - y‖ = 0 := by
    nlinarith [hgap (x - y), norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The straight segment to a perturbation smaller than a lower norm bound remains injective. -/
theorem injective_segment (J P : E →L[ℝ] E) {γ : ℝ}
    (hgap : ∀ x, γ * ‖x‖ ≤ ‖J x‖) (hpert : ‖P - J‖ < γ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Function.Injective (J + t • (P - J)) := by
  apply injective_of_perturbation J _ hgap
  calc
    ‖J + t • (P - J) - J‖ = ‖t • (P - J)‖ := by congr 1; abel
    _ = t * ‖P - J‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    _ ≤ ‖P - J‖ := by nlinarith [norm_nonneg (P - J), ht.2]
    _ < γ := hpert

/-- A continuous real function that never vanishes on the unit interval has the same strict
sign at its endpoints. -/
theorem same_sign_endpoints {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc 0 1))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0) : 0 < f 0 * f 1 := by
  have hzero : f 0 ≠ 0 := hne 0 (by norm_num)
  rcases lt_or_gt_of_ne hzero with hneg | hpos
  · have hneg1 : f 1 < 0 := by
      by_contra hn
      have hnonneg : 0 ≤ f 1 := le_of_not_gt hn
      obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
        hcont (show 0 ∈ Set.Icc (f 0) (f 1) from ⟨hneg.le, hnonneg⟩)
      exact hne t ht hft
    exact mul_pos_of_neg_of_neg hneg hneg1
  · have hpos1 : 0 < f 1 := by
      by_contra hn
      have hnonpos : f 1 ≤ 0 := le_of_not_gt hn
      obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
        hcont (show 0 ∈ Set.Icc (f 1) (f 0) from ⟨hnonpos, hpos.le⟩)
      exact hne t ht hft
    exact mul_pos hpos hpos1

/-- Finite-dimensional real determinant signs are preserved by perturbations smaller than
a lower norm bound. -/
theorem determinant_sign_of_perturbation [FiniteDimensional ℝ E]
    (J P : E →L[ℝ] E) {γ : ℝ}
    (hgap : ∀ x, γ * ‖x‖ ≤ ‖J x‖) (hpert : ‖P - J‖ < γ) :
    0 < J.det * P.det := by
  let f : ℝ → ℝ := fun t => (J + t • (P - J)).det
  have hcont : Continuous f :=
    ContinuousLinearMap.continuous_det.comp (continuous_const.add
      (continuous_id.smul continuous_const))
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0 := by
    intro t ht hzero
    have hker : (J + t • (P - J)).toLinearMap.ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr (injective_segment J P hgap hpert ht)
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) hker
  have hsign := same_sign_endpoints hcont.continuousOn hne
  simpa [f] using hsign

end StationaryNS

end

end OAI
