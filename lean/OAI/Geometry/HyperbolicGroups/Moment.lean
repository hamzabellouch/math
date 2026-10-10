import Mathlib
import OAI.Geometry.HyperbolicGroups.Random

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α : Type*} [Fintype α]

def variance (μ : FiniteLaw α) (f : α → ℝ) : ℝ :=
  μ.expect (fun a => (f a - μ.expect f) ^ 2)

lemma variance_nonneg (μ : FiniteLaw α) (f : α → ℝ) : 0 ≤ μ.variance f :=
  μ.expect_nonneg (fun _ => sq_nonneg _)

lemma variance_eq (μ : FiniteLaw α) (f : α → ℝ) :
    μ.variance f = μ.expect (fun a => f a ^ 2) - μ.expect f ^ 2 := by
  unfold variance
  simp_rw [sub_sq, show ∀ a, 2 * f a * μ.expect f = (2 * μ.expect f) * f a by intro a; ring]
  rw [μ.expect_add, μ.expect_sub, μ.expect_mul, μ.expect_const]
  ring

lemma expect_abs_sub_le (μ : FiniteLaw α) (f : α → ℝ) :
    μ.expect (fun a => |f a - μ.expect f|) ≤ Real.sqrt (μ.variance f) := by
  simpa only [sq_abs, variance] using μ.expect_le_sqrt (fun a => |f a - μ.expect f|)

lemma markov (μ : FiniteLaw α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) {c : ℝ}
    (hc : 0 < c) : μ.prob (fun a => c ≤ f a) ≤ μ.expect f / c := by
  classical
  apply (le_div_iff₀ hc).mpr
  rw [prob]
  calc
    _ = μ.expect (fun a => c * if c ≤ f a then 1 else 0) := by
      rw [μ.expect_mul]; ring
    _ ≤ μ.expect f := μ.expect_mono fun a => by
      split_ifs with h <;> simp_all

lemma chebyshev (μ : FiniteLaw α) (f : α → ℝ) {c : ℝ} (hc : 0 < c) :
    μ.prob (fun a => c ≤ |f a - μ.expect f|) ≤ μ.variance f / c ^ 2 := by
  classical
  have he (a : α) : c ≤ |f a - μ.expect f| ↔ c ^ 2 ≤ (f a - μ.expect f) ^ 2 := by
    rw [← sq_abs (f a - μ.expect f)]
    exact (sq_le_sq₀ hc.le (abs_nonneg _)).symm
  simp_rw [he]
  exact μ.markov _ (fun _ => sq_nonneg _) (sq_pos_of_pos hc)

end FiniteLaw

namespace TableModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A]

def candidateCount (support : R → Finset F) (C : Finset (F → A))
    (w : Entry (A := A) support → Bool) : ℕ := (C.filter (IsMatch support w)).card

omit [Fintype F] in
lemma expect_candidateCount (support : R → Finset F) (p : R → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (C : Finset (F → A)) :
    (law support p hp).expect (fun w => (candidateCount support C w : ℝ)) =
      C.card * ∏ r, p r := by
  classical
  have he (w : Entry (A := A) support → Bool) :
      (candidateCount support C w : ℝ) = ∑ σ ∈ C, if IsMatch support w σ then 1 else 0 := by
    simp [candidateCount]
  simp_rw [he]
  unfold FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ σ ∈ C, (∏ r, p r) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact prob_isMatch support p hp σ
    _ = _ := by simp

omit [Fintype F] in
lemma expect_candidateCount_sq (support : R → Finset F) (p : R → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (C : Finset (F → A)) :
    (law support p hp).expect (fun w => (candidateCount support C w : ℝ) ^ 2) =
      ∑ σ ∈ C, ∑ τ ∈ C,
        (law support p hp).prob (fun w => IsMatch support w σ ∧ IsMatch support w τ) := by
  classical
  have hc (w : Entry (A := A) support → Bool) :
      (candidateCount support C w : ℝ) ^ 2 =
      ∑ σ ∈ C, ∑ τ ∈ C, if IsMatch support w σ ∧ IsMatch support w τ then 1 else 0 := by
    have hcount : (candidateCount support C w : ℝ) =
        ∑ σ ∈ C, if IsMatch support w σ then 1 else 0 := by simp [candidateCount]
    rw [hcount, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    by_cases hσ : IsMatch support w σ <;> by_cases hτ : IsMatch support w τ <;> simp [hσ, hτ]
  simp_rw [hc]
  unfold FiniteLaw.prob FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_comm]

/-- Arbitrary fixed named fields, not pairwise-distinct numerical letters. -/
def pinCandidates (P : Finset F) (ξ : F → A) : Finset (F → A) :=
  Finset.univ.filter (fun σ => ∀ i ∈ P, σ i = ξ i)

lemma card_pinCandidates (P : Finset F) (ξ : F → A) :
    ((pinCandidates P ξ).card : ℝ) = (Fintype.card A : ℝ) ^ (Fintype.card F - P.card) := by
  rw [← sum_coincidence ξ P]
  simp [pinCandidates]

lemma sum_pin_coincidence (P W : Finset F) {σ ξ : F → A}
    (hσ : σ ∈ pinCandidates P ξ) :
    (∑ τ ∈ pinCandidates P ξ, if ∀ i ∈ W, σ i = τ i then (1 : ℝ) else 0) =
      (Fintype.card A : ℝ) ^ (Fintype.card F - (W ∪ P).card) := by
  classical
  have hp := (Finset.mem_filter.mp hσ).2
  rw [← sum_coincidence σ (W ∪ P)]
  unfold pinCandidates
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro τ _
  have he : (∀ i ∈ P, τ i = ξ i) ∧ (∀ i ∈ W, σ i = τ i) ↔
      ∀ i ∈ W ∪ P, τ i = σ i := by
    constructor
    · rintro ⟨h1,h2⟩ i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact (h2 i hi).symm
      · exact (h1 i hi).trans (hp i hi).symm
    · intro h
      exact ⟨fun i hi => (h i (Finset.mem_union_right W hi)).trans (hp i hi),
        fun i hi => (h i (Finset.mem_union_left P hi)).symm⟩
  rw [← ite_and]
  simp only [he]

lemma sum_pin_inverse_overlap (support : R → Finset F) (p : R → ℝ)
    (P : Finset F) {σ ξ : F → A} (hσ : σ ∈ pinCandidates P ξ) :
    (∑ τ ∈ pinCandidates P ξ, (∏ r ∈ overlapRows support σ τ, p r)⁻¹) =
      ∑ J : Finset R, (Fintype.card A : ℝ) ^
        (Fintype.card F - (J.biUnion support ∪ P).card) *
        ∏ r ∈ J, ((p r)⁻¹ - 1) := by
  classical
  simp_rw [inverse_overlap_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [← sum_pin_coincidence P (J.biUnion support) hσ, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro τ _
  split_ifs <;> simp_all

/-- Exact second moment, uniform in all pinned values. -/
lemma expect_pinCount_sq (support : R → Finset F) (p : R → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (hpos : ∀ r, 0 < p r)
    (P : Finset F) (ξ : F → A) :
    (law support p hp).expect (fun w => (candidateCount support (pinCandidates P ξ) w : ℝ) ^ 2) =
      (∏ r, p r) ^ 2 * (Fintype.card A : ℝ) ^ (Fintype.card F - P.card) *
      ∑ J : Finset R, (Fintype.card A : ℝ) ^
        (Fintype.card F - (J.biUnion support ∪ P).card) *
        ∏ r ∈ J, ((p r)⁻¹ - 1) := by
  classical
  rw [expect_candidateCount_sq]
  simp_rw [prob_pair support p hp hpos, div_eq_mul_inv, ← Finset.mul_sum]
  calc
    _ = (∏ r, p r) ^ 2 * ∑ σ ∈ pinCandidates P ξ,
        ∑ J : Finset R, (Fintype.card A : ℝ) ^
          (Fintype.card F - (J.biUnion support ∪ P).card) *
          ∏ r ∈ J, ((p r)⁻¹ - 1) := by
      congr 1
      apply Finset.sum_congr rfl
      intro σ hσ
      exact sum_pin_inverse_overlap support p P hσ
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_pinCandidates]; ring

/-- Every nonempty row overlap, and only those overlaps, contributes to variance. -/
lemma variance_pinCount (support : R → Finset F) (p : R → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (hpos : ∀ r, 0 < p r)
    (P : Finset F) (ξ : F → A) :
    (law support p hp).variance (fun w => (candidateCount support (pinCandidates P ξ) w : ℝ)) =
      (∏ r, p r) ^ 2 * (Fintype.card A : ℝ) ^ (Fintype.card F - P.card) *
      ∑ J ∈ (Finset.univ : Finset (Finset R)).erase ∅, (Fintype.card A : ℝ) ^
        (Fintype.card F - (J.biUnion support ∪ P).card) *
        ∏ r ∈ J, ((p r)⁻¹ - 1) := by
  rw [FiniteLaw.variance_eq, expect_pinCount_sq support p hp hpos,
    expect_candidateCount, card_pinCandidates]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset R))]
  simp only [Finset.biUnion_empty, Finset.empty_union, Finset.prod_empty, mul_one]
  ring

end TableModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
