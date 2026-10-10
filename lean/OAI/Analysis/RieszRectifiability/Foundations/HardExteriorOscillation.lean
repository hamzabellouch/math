import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.TruncationIntegrability
import OAI.Analysis.RieszRectifiability.Kernel.VectorKernelFarDifference

namespace OAI

/-!
# Exterior oscillation of hard truncations

Global upper growth controls the integral of a bounded density times a far-field
kernel difference. For an L² density supported outside a ball, this gives the
corresponding oscillation estimate for the exact hard-truncated transform.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem bounded_exterior_kernel_difference {d : ℕ} (n : ℕ) (G M : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (f : Ambient d → ℝ) (hfm : AEStronglyMeasurable f μ) (hM : 0 ≤ M)
    (a x : Ambient d) (R : ℝ) (hR : 0 < R) (hx : 2 * dist x a ≤ R)
    (hfM : ∀ y ∈ closedExterior a R, |f y| ≤ M) :
    IntegrableOn (fun y => f y • (kernel n x y - kernel n a y)) (closedExterior a R) μ ∧
      ‖∫ y in closedExterior a R, f y • (kernel n x y - kernel n a y) ∂μ‖ ≤
        (M * vectorKernelFarConstant n * dist x a) * (2 * (G * 2 ^ n / R)) := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have ht := inverseDistancePow_closedExterior_integrable_and_bound n G μ hg a R hR
  let K := M * vectorKernelFarConstant n * dist x a
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hM (vectorKernelFarConstant_pos n).le) dist_nonneg
  have hmeas : AEStronglyMeasurable
      (fun y => f y • (kernel n x y - kernel n a y)) (μ.restrict (closedExterior a R)) :=
    hfm.restrict.smul ((kernel_measurable_right n x).aestronglyMeasurable.sub
      (kernel_measurable_right n a).aestronglyMeasurable)
  have hpoint : ∀ᵐ y ∂μ.restrict (closedExterior a R),
      ‖f y • (kernel n x y - kernel n a y)‖ ≤ K * inverseDistancePow (n + 1) a y := by
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
    have hdist : R ≤ dist a y := hy
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ M * (vectorKernelFarConstant n * dist x a * inverseDistancePow (n + 1) a y) :=
        mul_le_mul (hfM y hy)
          (vector_kernel_far_difference n a x y (hR.trans_le hdist) (hx.trans hdist))
          (norm_nonneg _) hM
      _ = _ := by dsimp [K]; ring
  have hi := (ht.1.const_mul K).mono' hmeas hpoint
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y in closedExterior a R, K * inverseDistancePow (n + 1) a y ∂μ :=
      norm_integral_le_of_norm_le (ht.1.const_mul K) hpoint
    _ = K * ∫ y in closedExterior a R, inverseDistancePow (n + 1) a y ∂μ :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left ht.2 hK

theorem truncated_eq_exterior_integral_of_support {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (a x : Ambient d)
    (R ε : ℝ) (hx : 2 * dist x a ≤ R) (hε : ε < R / 2)
    (hs : ∀ y, f y ≠ 0 → R ≤ dist a y) :
    truncated n μ ε f x = ∫ y in closedExterior a R, f y • kernel n x y ∂μ := by
  have hzero (y : Ambient d) (hy : ¬ ε < dist x y) : f y = 0 := by
    by_contra hfy
    have hd := hs y hfy
    have htri := dist_triangle a x y
    rw [dist_comm a x] at htri
    linarith
  unfold truncated
  calc
    _ = ∫ y, f y • kernel n x y ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hzero y hy, zero_smul])
    _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      have hf : f y = 0 := by
        by_contra hfy
        exact hy (hs y hfy)
      rw [hf, zero_smul])).symm

theorem hard_truncated_exterior_difference_bound {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G M : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) (hM : 0 ≤ M)
    (hfM : ∀ y, |f y| ≤ M) (a x : Ambient d) (R ε : ℝ)
    (hR : 0 < R) (hε : 0 < ε) (hεR : ε < R / 2) (hx : 2 * dist x a ≤ R)
    (hs : ∀ y, f y ≠ 0 → R ≤ dist a y) :
    ‖truncated n μ ε f x - truncated n μ ε f a‖ ≤
      (M * vectorKernelFarConstant n * dist x a) * (2 * (G * 2 ^ n / R)) := by
  have hsep (b : Ambient d) (hb : 2 * dist b a ≤ R) :
      closedExterior a R ⊆ {y | ε < dist b y} := by
    intro y hy
    have hd : R ≤ dist a y := hy
    have ht := dist_triangle a b y
    rw [dist_comm a b] at ht
    change ε < dist b y
    linarith
  have hia : IntegrableOn (fun y => f y • kernel n a y) (closedExterior a R) μ :=
    (truncation_integrable_of_globalGrowth n hn G μ hg f hf a ε hε).mono_set
      (hsep a (by simp; positivity))
  have hix : IntegrableOn (fun y => f y • kernel n x y) (closedExterior a R) μ :=
    (truncation_integrable_of_globalGrowth n hn G μ hg f hf x ε hε).mono_set (hsep x hx)
  rw [truncated_eq_exterior_integral_of_support n μ f a x R ε hx hεR hs,
    truncated_eq_exterior_integral_of_support n μ f a a R ε (by simp; positivity) hεR hs,
    ← integral_sub hix hia]
  simp only [← smul_sub]
  exact (bounded_exterior_kernel_difference n G M μ hg f hf.aestronglyMeasurable hM
    a x R hR hx (fun y _ => hfM y)).2

end

end RieszRectifiability

end OAI
