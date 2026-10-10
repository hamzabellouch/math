import OAI.Analysis.IrrationalRotation.Model.FieldWeightedShift
import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal
import OAI.Analysis.IrrationalRotation.Analysis.ExponentialDecay
import OAI.Analysis.IrrationalRotation.Product.ProductNorm

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
  (ha : ∀ x, ‖a x‖ ≤ C)
  (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)

theorem fieldOperator_ae (f : Lp Hilbert 2 μ) :
    fieldOperator a C hC ha hm f =ᵐ[μ] fun x => operator (a x) (f x) := by
  filter_upwards [fieldShift_ae 1 (fieldDiagonal a C hC ha hm f),
    fieldDiagonal_ae a C hC ha hm f] with x hs hd
  change ((shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
    (fieldDiagonal a C hC ha hm f)) x = operator (a x) (f x)
  rw [hs, hd]
  rfl

theorem fieldOperator_pow_ae (n : ℕ) (f : Lp Hilbert 2 μ) :
    ((fieldOperator a C hC ha hm)^n) f =ᵐ[μ]
      fun x => ((operator (a x))^n) (f x) := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    filter_upwards [fieldOperator_ae a C hC ha hm
      (((fieldOperator a C hC ha hm)^n) f), ih] with x hx hn
    simpa only [pow_succ', mul_apply_eq_comp, hn] using hx

theorem norm_fieldOperator_pow_le (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hprod : ∀ᵐ x ∂μ, ∀ k : ℤ,
      ‖∏ j ∈ Finset.range n, a x (k + j)‖ ≤ B) :
    ‖(fieldOperator a C hC ha hm)^n‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fieldOperator_pow_ae a C hC ha hm n f, hprod] with x hx hb
  rw [hx]
  exact ((operator (a x))^n).le_of_opNorm_le
    (norm_operator_pow_le (a x) n hB hb) (f x)

theorem fieldOperator_norm_quasinilpotent
    (hdecay : ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop,
      ∀ᵐ x ∂μ, ∀ k : ℤ, ‖∏ j ∈ Finset.range n, a x (k+j)‖ ≤
        Real.exp (-r * (n : ℝ))) :
    Tendsto (fun n : ℕ => ‖(fieldOperator a C hC ha hm)^n‖ ^
      (1 / (n : ℝ))) atTop (𝓝 0) := by
  apply Invariant233.norm_quasinilpotent_of_exponential_decay
  intro r hr
  filter_upwards [hdecay r hr] with n hn
  exact norm_fieldOperator_pow_le a C hC ha hm n (Real.exp_nonneg _) hn

theorem fieldOperator_norm_quasinilpotent_of_prefix_bounds
    (loss rate : ℕ → ℝ)
    (hbound : ∀ q n : ℕ, 0 < n → ∀ᵐ x ∂μ, ∀ k : ℤ,
      ‖∏ j ∈ Finset.range n, a x (k+j)‖ ≤
        Real.exp (loss q - (n : ℝ) * rate q))
    (hrate : ∀ b : ℝ, ∃ q, b < rate q) :
    Tendsto (fun n : ℕ => ‖(fieldOperator a C hC ha hm)^n‖ ^
      (1 / (n : ℝ))) atTop (𝓝 0) := by
  apply Invariant233.ProductNorm.tendsto_root_zero_of_exponential_bounds
    (fun n => ‖(fieldOperator a C hC ha hm)^n‖) loss rate
    (fun _ => norm_nonneg _) _ hrate
  intro q n hn
  exact norm_fieldOperator_pow_le a C hC ha hm n (Real.exp_nonneg _) (hbound q n hn)

theorem fieldOperator_eq_zero_iff [IsFiniteMeasure μ] :
    fieldOperator a C hC ha hm = 0 ↔ a =ᵐ[μ] 0 := by
  constructor
  · intro h
    have hk : ∀ k : ℤ, ∀ᵐ x ∂μ, a x k = 0 := by
      intro k
      let f : Lp Hilbert 2 μ := Lp.const 2 μ (lp.single 2 k 1)
      filter_upwards [fieldOperator_ae a C hC ha hm f,
        Lp.coeFn_const 2 μ (lp.single 2 k (1 : ℂ) : Hilbert), Lp.coeFn_zero Hilbert 2 μ]
        with x hx hc hz
      change f x = lp.single 2 k 1 at hc
      change (0 : Lp Hilbert 2 μ) x = 0 at hz
      simp only [h, zero_apply] at hx
      rw [hz, hc] at hx
      have hv := congrArg (fun v : Hilbert => v (k+1)) hx.symm
      simpa [operator_apply] using hv
    filter_upwards [ae_all_iff.mpr hk] with x hx
    apply lp.ext
    funext k
    exact hx k
  · intro h
    ext f
    filter_upwards [fieldOperator_ae a C hC ha hm f, h, Lp.coeFn_zero Hilbert 2 μ]
      with x hx ha0 hz
    change fieldOperator a C hC ha hm f x = (0 : Lp Hilbert 2 μ) x
    simp only [Pi.zero_apply] at ha0 hz
    rw [hx, ha0, (operator_eq_zero_iff 0).2 rfl, zero_apply]
    exact hz.symm

theorem fieldOperator_ne_zero_of_coordinate [IsFiniteMeasure μ] [NeZero μ]
    (k : ℤ) (hpos : ∀ᵐ x ∂μ, a x k ≠ 0) : fieldOperator a C hC ha hm ≠ 0 := by
  intro h
  have hz := (fieldOperator_eq_zero_iff a C hC ha hm).1 h
  obtain ⟨x, hx, hp⟩ := (hz.and hpos).exists
  exact hp (by rw [hx]; rfl)

end Invariant233.WeightedShift

end

end OAI
