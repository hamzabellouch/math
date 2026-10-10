import OAI.Combinatorics.GraphThreshold.LocalFailureNumerics
import OAI.Combinatorics.GraphThreshold.ResamplingEvents
import OAI.Combinatorics.GraphThreshold.SpreadCounting
import OAI.Combinatorics.GraphThreshold.FiniteProbability
import OAI.Combinatorics.GraphThreshold.ResamplingDensity

namespace OAI

/-! # Local failure of the actual resampling experiment -/

noncomputable section

open Finset

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B]

omit [Fintype X] [Fintype B] in
private theorem target_subset_iff_required_subset (A : B → Finset X)
    (W : Finset X) (c b : B) :
    A b ⊆ resamplingY A W c ↔ A b \ A c ⊆ W := by
  constructor
  · intro h x hx
    rcases Finset.mem_union.mp (h (Finset.mem_sdiff.mp hx).1) with hW | hc
    · exact hW
    · exact ((Finset.mem_sdiff.mp hx).2 hc).elim
  · intro h x hx
    by_cases hc : x ∈ A c
    · exact Finset.mem_union.mpr (Or.inr hc)
    · exact Finset.mem_union.mpr (Or.inl (h (Finset.mem_sdiff.mpr ⟨hx, hc⟩)))

omit [Fintype X] [Fintype B] in
private theorem fragment_subset_inter_of_target_subset (A : B → Finset X)
    (W : Finset X) (c b : B) (h : A b ⊆ resamplingY A W c) :
    A b \ W ⊆ A c ∩ A b := by
  intro x hx
  obtain ⟨hb, hW⟩ := Finset.mem_sdiff.mp hx
  rcases Finset.mem_union.mp (h hb) with hxW | hc
  · exact (hW hxW).elim
  · exact Finset.mem_inter.mpr ⟨hc, hb⟩

omit [Fintype X] [Fintype B] in
private theorem inverse_power_card_cancel (A : B → Finset X) {ρ : ℝ}
    (hρ : 0 < ρ) (c b : B) :
    (ρ⁻¹) ^ (A b).card * ρ ^ (A b \ A c).card =
      (ρ⁻¹) ^ (A c ∩ A b).card := by
  have hc : (A b).card = (A b \ A c).card + (A c ∩ A b).card := by
    simpa only [Finset.inter_comm] using (Finset.card_sdiff_add_card_inter (A b) (A c)).symm
  rw [hc, pow_add]
  calc
    ((ρ⁻¹) ^ (A b \ A c).card * (ρ⁻¹) ^ (A c ∩ A b).card) *
        ρ ^ (A b \ A c).card =
      ((ρ⁻¹) ^ (A b \ A c).card * ρ ^ (A b \ A c).card) *
        (ρ⁻¹) ^ (A c ∩ A b).card := by ring
    _ = (ρ⁻¹) ^ (A c ∩ A b).card := by simp [inv_pow, hρ.ne']

omit [Fintype X] in
/-- At a large denominator, the actual large-fragment weight is bounded by
an intersection-tail indicator and the required-coordinate indicator. -/
theorem resampling_large_fragment_term_le (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) (W : Finset X) (c b : B) :
    (if Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W c) ∧
          m / 2 < (A b \ W).card then resamplingWeight ν A ρ W (c, b) else 0) ≤
      if m < 2 * (A c ∩ A b).card ∧ A b \ A c ⊆ W then
        Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b * (ρ⁻¹) ^ (A b).card
      else 0 := by
  classical
  have hrhs : 0 ≤
      if m < 2 * (A c ∩ A b).card ∧ A b \ A c ⊆ W then
        Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b * (ρ⁻¹) ^ (A b).card
      else 0 := by
    split_ifs
    · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (ν.nonneg c))
        (ν.nonneg b)) (pow_nonneg (inv_nonneg.mpr hρ.le) _)
    · exact le_rfl
  by_cases he : Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W c) ∧
      m / 2 < (A b \ W).card
  · rw [ite_eq_left he]
    by_cases hs : A b ⊆ resamplingY A W c
    · have hfrag := Finset.card_le_card (fragment_subset_inter_of_target_subset A W c b hs)
      have hlarge : m < 2 * (A c ∩ A b).card := by omega
      have hreq := (target_subset_iff_required_subset A W c b).mp hs
      rw [ite_eq_left ⟨hlarge, hreq⟩]
      have hZpos : 0 < resamplingZ ν A ρ (resamplingY A W c) :=
        (Real.exp_pos _).trans_le he.1
      have hscale : 1 ≤ Real.exp (10 * (m : ℝ)) *
          resamplingZ ν A ρ (resamplingY A W c) := by
        calc
          1 = Real.exp (10 * (m : ℝ)) * Real.exp (-10 * (m : ℝ)) := by
            rw [← Real.exp_add]; simp
          _ ≤ _ := mul_le_mul_of_nonneg_left he.1 (Real.exp_pos _).le
      have hnum : 0 ≤ ν.weight b * (ρ⁻¹) ^ (A b).card :=
        mul_nonneg (ν.nonneg b) (pow_nonneg (inv_nonneg.mpr hρ.le) _)
      have hdiv : (ν.weight b * (ρ⁻¹) ^ (A b).card) /
          resamplingZ ν A ρ (resamplingY A W c) ≤
          Real.exp (10 * (m : ℝ)) * (ν.weight b * (ρ⁻¹) ^ (A b).card) := by
        apply (div_le_iff₀ hZpos).mpr
        nlinarith [mul_le_mul_of_nonneg_left hscale hnum]
      unfold resamplingWeight resamplingTargetWeight
      rw [resamplingNumerator, ite_eq_left hs]
      calc
        ν.weight c * ((ν.weight b * (ρ⁻¹) ^ (A b).card) /
            resamplingZ ν A ρ (resamplingY A W c)) ≤
          ν.weight c * (Real.exp (10 * (m : ℝ)) *
            (ν.weight b * (ρ⁻¹) ^ (A b).card)) :=
          mul_le_mul_of_nonneg_left hdiv (ν.nonneg c)
        _ = _ := by ring
    · rw [resamplingWeight_eq_zero_of_not_subset ν A ρ W c b hs]
      exact hrhs
  · rw [ite_eq_right he]
    exact hrhs

private theorem local_bernoulliExpectation_sum {ι : Type*} [Fintype ι]
    (ρ : ℝ) (f : ι → Finset X → ℝ) :
    bernoulliExpectation ρ (fun W => ∑ i, f i W) =
      ∑ i, bernoulliExpectation ρ (f i) := by
  simp only [bernoulliExpectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem resampling_large_fragment_pair_bound (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) (c b : B) :
    bernoulliExpectation ρ (fun W =>
      if Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W c) ∧
          m / 2 < (A b \ W).card then resamplingWeight ν A ρ W (c, b) else 0) ≤
      if m < 2 * (A c ∩ A b).card then
        Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b * (ρ⁻¹) ^ (A c ∩ A b).card
      else 0 := by
  classical
  let μ : FiniteLaw (Finset X) := bernoulliLaw ρ hρ.le hρ1.le
  by_cases hlarge : m < 2 * (A c ∩ A b).card
  · rw [ite_eq_left hlarge]
    calc
      _ ≤ μ.expectation (fun W =>
          (Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b * (ρ⁻¹) ^ (A b).card) *
            (if A b \ A c ⊆ W then 1 else 0)) := by
        apply μ.expectation_mono
        intro W
        simpa only [hlarge, true_and, mul_ite, mul_one, mul_zero] using
          resampling_large_fragment_term_le ν A hρ m W c b
      _ = (Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b * (ρ⁻¹) ^ (A b).card) *
          ρ ^ (A b \ A c).card := by
        rw [FiniteLaw.expectation_smul]
        congr 1
        change bernoulliExpectation ρ (fun W => if A b \ A c ⊆ W then 1 else 0) = _
        rw [← bernoulliProbability_subset ρ (A b \ A c)]
        simp only [bernoulliExpectation, bernoulliProbability, mul_ite, mul_one, mul_zero]
        apply Finset.sum_congr rfl
        intro W _
        by_cases hW : A b \ A c ⊆ W <;> simp [hW]
      _ = Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b *
          ((ρ⁻¹) ^ (A b).card * ρ ^ (A b \ A c).card) := by ring
      _ = _ := by rw [inverse_power_card_cancel A hρ c b]
  · rw [ite_eq_right hlarge]
    calc
      _ ≤ μ.expectation (fun _ => 0) := by
        apply μ.expectation_mono
        intro W
        simpa only [hlarge, false_and, ite_false] using
          resampling_large_fragment_term_le ν A hρ m W c b
      _ = 0 := μ.expectation_const 0

theorem resampling_large_fragment_bound (ν : FiniteLaw B) (A : B → Finset X)
    {ρ a : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (m : ℕ) (hsize : ∀ b, (A b).card ≤ m) (hspread : IsSpread ν A a)
    (ha : 0 ≤ a) (hratio : a / ρ ≤ Real.exp (-50)) :
    bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob
      (fun cb => Real.exp (-10 * (m : ℝ)) ≤
          resamplingZ ν A ρ (resamplingY A W cb.1) ∧
        m / 2 < (A cb.2 \ W).card)) ≤
      Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) := by
  classical
  have hpair (b : B) :
      (∑ c, bernoulliExpectation ρ (fun W =>
        if Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W c) ∧
            m / 2 < (A b \ W).card then resamplingWeight ν A ρ W (c, b) else 0)) ≤
      (Real.exp (10 * (m : ℝ)) * ν.weight b) * largeIntersectionTail m (a / ρ) := by
    calc
      _ ≤ ∑ c, if m < 2 * (A c ∩ A b).card then
          Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b *
            (ρ⁻¹) ^ (A c ∩ A b).card else 0 := by
        apply Finset.sum_le_sum
        intro c _
        exact resampling_large_fragment_pair_bound ν A hρ hρ1 m c b
      _ = (Real.exp (10 * (m : ℝ)) * ν.weight b) *
          ∑ c, if m < 2 * (A c ∩ A b).card then
            ν.weight c * (ρ⁻¹) ^ (A c ∩ A b).card else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        split_ifs <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (intersection_inverse_truncated_sum_le hspread ha (hsize b) hρ
          (fun r => m < 2 * r))
        (mul_nonneg (Real.exp_pos _).le (ν.nonneg b))
  calc
    _ = ∑ b, ∑ c, bernoulliExpectation ρ (fun W =>
        if Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W c) ∧
            m / 2 < (A b \ W).card then resamplingWeight ν A ρ W (c, b) else 0) := by
      simp only [FiniteLaw.prob, resamplingLaw_weight, Fintype.sum_prod_type]
      conv_lhs => arg 2; ext W; rw [Finset.sum_comm]
      rw [local_bernoulliExpectation_sum]
      simp_rw [local_bernoulliExpectation_sum]
      apply Finset.sum_congr rfl
      intro target _
      apply Finset.sum_congr rfl
      intro source _
      congr 1
      funext drawn
      split_ifs <;> rfl
    _ ≤ ∑ b, (Real.exp (10 * (m : ℝ)) * ν.weight b) * largeIntersectionTail m (a / ρ) :=
      Finset.sum_le_sum (fun b _ => hpair b)
    _ = Real.exp (10 * (m : ℝ)) * largeIntersectionTail m (a / ρ) := by
      calc
        _ = (Real.exp (10 * (m : ℝ)) * largeIntersectionTail m (a / ρ)) *
            ∑ b, ν.weight b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by rw [ν.total, mul_one]
    _ ≤ Real.exp (10 * (m : ℝ)) * ((2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (largeIntersectionTail_le (div_nonneg ha hρ.le) hratio)
        (Real.exp_pos _).le
    _ = _ := by ring

/-- The density identity bounds the probability of a small denominator by
the cutoff itself. -/
theorem resampling_small_density_bound (ν : FiniteLaw B) (A : B → Finset X)
    {ρ τ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 ≤ τ) :
    bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob
      (fun cb => resamplingZ ν A ρ (resamplingY A W cb.1) < τ)) ≤ τ := by
  classical
  rw [resampling_density_prob ν A hν hρ (fun Y => resamplingZ ν A ρ Y < τ)]
  let μ : FiniteLaw (Finset X) := bernoulliLaw ρ hρ.le hρ1.le
  change μ.expectation _ ≤ τ
  calc
    _ ≤ μ.expectation (fun _ => τ) := by
      apply μ.expectation_mono
      intro Y
      split_ifs with hY
      · exact hY.le
      · exact hτ
    _ = τ := μ.expectation_const τ

theorem local_failure_bound (ν : FiniteLaw B) (A : B → Finset X)
    {ρ a : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (m : ℕ) (hm : 1 ≤ m) (hsize : ∀ b, (A b).card ≤ m)
    (hspread : IsSpread ν A a) (ha : 0 ≤ a) (hratio : a / ρ ≤ Real.exp (-50)) :
    bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob
      (fun cb => LocalFailure ν A ρ m W cb.1 cb.2)) ≤ Real.exp (-9 * (m : ℝ)) := by
  classical
  let μ : FiniteLaw (Finset X) := bernoulliLaw ρ hρ.le hρ1.le
  let low (W : Finset X) (cb : B × B) : Prop :=
    resamplingZ ν A ρ (resamplingY A W cb.1) < Real.exp (-10 * (m : ℝ))
  let big (W : Finset X) (cb : B × B) : Prop :=
    Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W cb.1) ∧
      m / 2 < (A cb.2 \ W).card
  have hpoint (W : Finset X) :
      (resamplingLaw ν A ρ W hν hρ).prob (fun cb => LocalFailure ν A ρ m W cb.1 cb.2) ≤
      (resamplingLaw ν A ρ W hν hρ).prob (low W) +
        (resamplingLaw ν A ρ W hν hρ).prob (big W) := by
    apply le_trans ((resamplingLaw ν A ρ W hν hρ).prob_mono (Q := fun cb => low W cb ∨ big W cb) ?_)
      ((resamplingLaw ν A ρ W hν hρ).prob_union_le (low W) (big W))
    intro cb hcb
    rcases (localFailure_iff ν A ρ m W cb.1 cb.2).mp hcb with hlow | hfrag
    · exact Or.inl hlow
    · by_cases hl : low W cb
      · exact Or.inl hl
      · exact Or.inr ⟨le_of_not_gt hl, hfrag⟩
  calc
    _ ≤ μ.expectation (fun W => (resamplingLaw ν A ρ W hν hρ).prob (low W) +
        (resamplingLaw ν A ρ W hν hρ).prob (big W)) := μ.expectation_mono hpoint
    _ = μ.expectation (fun W => (resamplingLaw ν A ρ W hν hρ).prob (low W)) +
        μ.expectation (fun W => (resamplingLaw ν A ρ W hν hρ).prob (big W)) :=
      μ.expectation_add _ _
    _ ≤ Real.exp (-10 * (m : ℝ)) +
        Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) :=
      add_le_add (resampling_small_density_bound ν A hν hρ hρ1 (Real.exp_pos _).le)
        (resampling_large_fragment_bound ν A hν hρ hρ1 m hsize hspread ha hratio)
    _ ≤ Real.exp (-9 * (m : ℝ)) := local_failure_exponential_combine hm

theorem local_failure_probability_bound (ν : FiniteLaw B) (A : B → Finset X)
    {ρ a : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (m : ℕ) (hm : 1 ≤ m) (hsize : ∀ b, (A b).card ≤ m)
    (hspread : IsSpread ν A a) (ha : 0 ≤ a) (hratio : a / ρ ≤ Real.exp (-50)) :
    (resamplingExperimentLaw ν A ρ hν hρ hρ1.le).prob
      (fun ω => LocalFailure ν A ρ m ω.1 ω.2.1 ω.2.2) ≤ Real.exp (-9 * (m : ℝ)) := by
  classical
  have heq : (resamplingExperimentLaw ν A ρ hν hρ hρ1.le).prob
      (fun ω => LocalFailure ν A ρ m ω.1 ω.2.1 ω.2.2) =
      bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob
        (fun cb => LocalFailure ν A ρ m W cb.1 cb.2)) := by
    simp only [FiniteLaw.prob, resamplingExperimentLaw, Fintype.sum_prod_type,
      bernoulliExpectation, resamplingLaw_weight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro W _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : LocalFailure ν A ρ m W c b <;> simp [h]
  rw [heq]
  exact local_failure_bound ν A hν hρ hρ1 m hm hsize hspread ha hratio

omit [Fintype X] in

theorem localFailure_iff_real (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) (W : Finset X) (c b : B) :
    LocalFailure ν A ρ m W c b ↔
      resamplingZ ν A ρ (resamplingY A W c) < Real.exp (-10 * (m : ℝ)) ∨
        (m : ℝ) / 2 < ((A b \ W).card : ℝ) := by
  rw [localFailure_iff_twice]
  apply or_congr Iff.rfl
  constructor
  · intro h
    have h' : (m : ℝ) < 2 * ((A b \ W).card : ℝ) := by exact_mod_cast h
    linarith
  · intro h
    have h' : (m : ℝ) < 2 * ((A b \ W).card : ℝ) := by linarith
    exact_mod_cast h'

theorem local_failure_source_form (ν : FiniteLaw B) (A : B → Finset X)
    {ρ a : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (m : ℕ) (hm : 1 ≤ m) (hsize : ∀ b, (A b).card ≤ m)
    (hspread : IsSpread ν A a) (ha : 0 ≤ a) (hratio : a / ρ ≤ Real.exp (-50)) :
    (resamplingExperimentLaw ν A ρ hν hρ hρ1.le).prob
      (fun ω => resamplingZ ν A ρ (resamplingY A ω.1 ω.2.1) <
          Real.exp (-10 * (m : ℝ)) ∨
        (m : ℝ) / 2 < ((A ω.2.2 \ ω.1).card : ℝ)) ≤ Real.exp (-9 * (m : ℝ)) := by
  simpa only [localFailure_iff_real] using
    local_failure_probability_bound ν A hν hρ hρ1 m hm hsize hspread ha hratio

end LeanBlast.SecondKahnKalai

end

end OAI
