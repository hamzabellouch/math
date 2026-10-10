import OAI.Combinatorics.GraphThreshold.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace OAI

/-! Exact intersection counting for a finite, weighted spread family.

No injectivity of the label map and no strict positivity of individual weights
is required. The fixed target is an arbitrary finite set, and may be empty.
-/

noncomputable section

open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

/-- The spread bound also holds for the empty test set, by normalization. -/
theorem IsSpread.containment_le {μ : FiniteLaw B} {A : B → Finset X} {a : ℝ}
    (hs : IsSpread μ A a) (J : Finset X) :
    μ.prob (fun c => J ⊆ A c) ≤ a ^ J.card := by
  classical
  by_cases hJ : J.Nonempty
  · exact hs J hJ
  · have hJ' : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    simp [hJ', FiniteLaw.prob, μ.total]

/-- If the intersection has at least `r` points, it contains an `r`-set
from the target. This is the weighted finite union bound. -/
theorem intersection_card_ge_le_subsets (μ : FiniteLaw B) (A : B → Finset X)
    (T : Finset X) (r : ℕ) :
    μ.prob (fun c => r ≤ (A c ∩ T).card) ≤
      ∑ J ∈ T.powersetCard r, μ.prob (fun c => J ⊆ A c) := by
  classical
  unfold FiniteLaw.prob
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro c hc
  by_cases hcr : r ≤ (A c ∩ T).card
  · rw [ite_eq_left hcr]
    obtain ⟨J, hJ, hJr⟩ := Finset.exists_subset_card_eq hcr
    have hJA : J ⊆ A c := hJ.trans Finset.inter_subset_left
    have hJT : J ⊆ T := hJ.trans Finset.inter_subset_right
    have hm : J ∈ T.powersetCard r := Finset.mem_powersetCard.mpr ⟨hJT, hJr⟩
    have hsingle := Finset.single_le_sum
      (f := fun J : Finset X => if J ⊆ A c then μ.weight c else 0)
      (fun J _ => by split_ifs <;>
        first | exact μ.nonneg c | exact le_rfl) hm
    have hsingle' : μ.weight c ≤
        ∑ J ∈ T.powersetCard r, if J ⊆ A c then μ.weight c else 0 := by
      simpa only [ite_eq_left hJA] using hsingle
    refine hsingle'.trans_eq ?_
    apply Finset.sum_congr rfl
    intro L hL
    by_cases hLA : L ⊆ A c <;> simp [hLA]
  · rw [ite_eq_right hcr]
    exact Finset.sum_nonneg fun J _ => by
      split_ifs <;> first | exact μ.nonneg c | exact le_rfl

/-- Exact binomial count of potential witnesses bounds the intersection tail. -/
theorem intersection_card_ge_le_target {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (T : Finset X) (r : ℕ) :
    μ.prob (fun c => r ≤ (A c ∩ T).card) ≤
      (T.card.choose r : ℝ) * a ^ r := by
  classical
  calc
    μ.prob (fun c => r ≤ (A c ∩ T).card) ≤
        ∑ J ∈ T.powersetCard r, μ.prob (fun c => J ⊆ A c) :=
      intersection_card_ge_le_subsets μ A T r
    _ ≤ ∑ J ∈ T.powersetCard r, a ^ r := by
      apply Finset.sum_le_sum
      intro J hJ
      simpa [(Finset.mem_powersetCard.mp hJ).2] using hs.containment_le J
    _ = (T.card.choose r : ℝ) * a ^ r := by simp

/-- Uniform capacity version, including `r = 0` and empty target sets. -/
theorem intersection_card_ge_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) (r : ℕ) :
    μ.prob (fun c => r ≤ (A c ∩ T).card) ≤
      (m.choose r : ℝ) * a ^ r := by
  apply (intersection_card_ge_le_target hs T r).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha r)
  exact_mod_cast Nat.choose_le_choose r hT

/-- The exact intersection histogram is bounded by the same binomial count. -/
theorem intersection_card_eq_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) (r : ℕ) :
    μ.prob (fun c => (A c ∩ T).card = r) ≤
      (m.choose r : ℝ) * a ^ r := by
  classical
  apply le_trans _ (intersection_card_ge_le hs ha hT r)
  unfold FiniteLaw.prob
  apply Finset.sum_le_sum
  intro c hc
  by_cases hcr : (A c ∩ T).card = r
  · simp [hcr]
  · simp only [ite_eq_right hcr]
    split_ifs <;> first | exact μ.nonneg c | exact le_rfl

/-- Reindex any function of the intersection by the exact finite histogram. -/
theorem expectation_intersection_eq_sum (μ : FiniteLaw B) (A : B → Finset X)
    {m : ℕ} {T : Finset X} (hT : T.card ≤ m) (g : ℕ → ℝ) :
    μ.expectation (fun c => g (A c ∩ T).card) =
      ∑ r ∈ Finset.range (m + 1),
        μ.prob (fun c => (A c ∩ T).card = r) * g r := by
  classical
  unfold FiniteLaw.expectation FiniteLaw.prob
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  have hcm : (A c ∩ T).card ∈ Finset.range (m + 1) := by
    apply Finset.mem_range.mpr
    have hct := Finset.card_le_card (Finset.inter_subset_right (s₁ := A c) (s₂ := T))
    omega
  simp [hcm]

/-- Any nonnegative function of the intersection admits a binomial majorant. -/
theorem expectation_intersection_le_binomial {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) (g : ℕ → ℝ) (hg : ∀ r, 0 ≤ g r) :
    μ.expectation (fun c => g (A c ∩ T).card) ≤
      ∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ) * a ^ r * g r := by
  rw [expectation_intersection_eq_sum μ A hT g]
  exact Finset.sum_le_sum fun r _ =>
    mul_le_mul_of_nonneg_right (intersection_card_eq_le hs ha hT r) (hg r)

/-- A predicate can truncate the intersection generating function arbitrarily. -/
theorem intersection_truncated_moment_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) {t : ℝ} (ht : 0 ≤ t)
    (Q : ℕ → Prop) [DecidablePred Q] :
    μ.expectation (fun c => if Q (A c ∩ T).card then t ^ (A c ∩ T).card else 0) ≤
      ∑ r ∈ Finset.range (m + 1),
        if Q r then (m.choose r : ℝ) * (a * t) ^ r else 0 := by
  calc
    _ ≤ ∑ r ∈ Finset.range (m + 1),
        (m.choose r : ℝ) * a ^ r * (if Q r then t ^ r else 0) := by
      apply expectation_intersection_le_binomial hs ha hT
        (fun r => if Q r then t ^ r else 0)
      intro r
      split_ifs <;> first | exact pow_nonneg ht r | exact le_rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hQ : Q r <;> simp [hQ, mul_pow, mul_assoc]

/-- Raw-sum form of the truncated moment estimate. -/
theorem intersection_truncated_sum_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) {t : ℝ} (ht : 0 ≤ t)
    (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ c, if Q (A c ∩ T).card then μ.weight c * t ^ (A c ∩ T).card else 0) ≤
      ∑ r ∈ Finset.range (m + 1),
        if Q r then (m.choose r : ℝ) * (a * t) ^ r else 0 := by
  simpa only [FiniteLaw.expectation, mul_ite, mul_zero] using
    intersection_truncated_moment_le hs ha hT ht Q

/-- The full generating-function bound needs only a nonnegative argument. -/
theorem intersection_moment_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    μ.expectation (fun c => t ^ (A c ∩ T).card) ≤ (1 + a * t) ^ m := by
  calc
    _ ≤ ∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ) * a ^ r * t ^ r :=
      expectation_intersection_le_binomial hs ha hT _ (fun r => pow_nonneg ht r)
    _ = (1 + a * t) ^ m := by
      rw [add_comm 1 (a * t), add_pow]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [one_pow, mul_one, mul_pow]
      ring

/-- Inverse-parameter moment used by the resampling density estimate. -/
theorem intersection_inverse_moment_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) {ρ : ℝ} (hρ : 0 < ρ) :
    μ.expectation (fun c => (ρ⁻¹) ^ (A c ∩ T).card) ≤ (1 + a / ρ) ^ m := by
  simpa only [div_eq_mul_inv] using
    intersection_moment_le hs ha hT (inv_nonneg.mpr hρ.le)

/-- Raw-sum form of the inverse-parameter moment. -/
theorem intersection_inverse_sum_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) {ρ : ℝ} (hρ : 0 < ρ) :
    (∑ c, μ.weight c * (ρ⁻¹) ^ (A c ∩ T).card) ≤ (1 + a / ρ) ^ m :=
  intersection_inverse_moment_le hs ha hT hρ

/-- Inverse-parameter truncated moment, retaining an arbitrary tail predicate. -/
theorem intersection_inverse_truncated_sum_le
    {μ : FiniteLaw B} {A : B → Finset X} {a : ℝ}
    (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) {ρ : ℝ} (hρ : 0 < ρ)
    (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ c, if Q (A c ∩ T).card then μ.weight c * (ρ⁻¹) ^ (A c ∩ T).card else 0) ≤
      ∑ r ∈ Finset.range (m + 1),
        if Q r then (m.choose r : ℝ) * (a / ρ) ^ r else 0 := by
  simpa only [div_eq_mul_inv] using
    intersection_truncated_sum_le hs ha hT (inv_nonneg.mpr hρ.le) Q

end LeanBlast.SecondKahnKalai

end

end OAI
