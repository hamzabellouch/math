import Mathlib
import OAI.Geometry.HyperbolicGroups.Moment

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace BernoulliCandidates
variable {V S I A : Type*} [Fintype V] [Fintype S] [Fintype I] [Fintype A]
  [DecidableEq V] [DecidableEq S] [DecidableEq I] [DecidableEq A]

/-- Row positions of a candidate may belong to the same array. Actual trials,
not row positions, are the independent Bernoulli variables. -/
def Present (row : (V → A) → S → I) (w : I → Bool) (σ : V → A) : Prop :=
  ∀ s, w (row σ s) = true

instance (row : (V → A) → S → I) (w : I → Bool) (σ : V → A) :
    Decidable (Present row w σ) := inferInstanceAs (Decidable (∀ position, w (row σ position) = true))

def count (row : (V → A) → S → I) (C : Finset (V → A)) (w : I → Bool) : ℕ :=
  (C.filter (Present row w)).card

def shared (row : (V → A) → S → I) (σ τ : V → A) : Finset S :=
  Finset.univ.filter (fun s => ∃ r, row τ s = row σ r)

omit [Fintype V] [Fintype I] [Fintype A] [DecidableEq V] [DecidableEq S] [DecidableEq A] in
lemma shared_image (row : (V → A) → S → I) (σ τ : V → A) :
    (Finset.univ.image (row σ)) ∩ (Finset.univ.image (row τ)) =
      (shared row σ τ).image (row τ) := by
  classical
  ext i
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
    shared, Finset.mem_filter]
  constructor
  · rintro ⟨⟨r,hr⟩,⟨s,hs⟩⟩
    exact ⟨s, ⟨r, hs.trans hr.symm⟩, hs⟩
  · rintro ⟨s, ⟨r,he⟩,hs⟩
    exact ⟨⟨r, he.symm.trans hs⟩,⟨s,hs⟩⟩

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq S] [DecidableEq A] in
lemma prob_present (row : (V → A) → S → I) (p : I → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (σ : V → A)
    (hi : Function.Injective (row σ)) :
    (FiniteLaw.bernoulliProduct p hp).prob (fun w => Present row w σ) =
      ∏ s, p (row σ s) := by
  classical
  have he (w : I → Bool) : Present row w σ ↔
      ∀ i ∈ Finset.univ.image (row σ), w i = true := by
    simp [Present]
  simp only [FiniteLaw.prob, he]
  rw [FiniteLaw.bernoulliProduct_all,
    Finset.prod_image (fun _ _ _ _ h => hi h)]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq S] [DecidableEq A] in
lemma prob_pair (row : (V → A) → S → I) (p : I → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (σ τ : V → A)
    (hσ : Function.Injective (row σ)) (hτ : Function.Injective (row τ))
    (hpos : ∀ s, 0 < p (row τ s)) :
    (FiniteLaw.bernoulliProduct p hp).prob (fun w => Present row w σ ∧ Present row w τ) =
      (∏ s, p (row σ s)) * (∏ s, p (row τ s)) *
        (∏ s ∈ shared row σ τ, p (row τ s))⁻¹ := by
  classical
  have he (w : I → Bool) : Present row w σ ∧ Present row w τ ↔
      ∀ i ∈ Finset.univ.image (row σ) ∪ Finset.univ.image (row τ), w i = true := by
    simp only [Present, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hσ, hτ⟩ i (⟨r, hr⟩ | ⟨r, hr⟩)
      · simpa only [← hr] using hσ r
      · simpa only [← hr] using hτ r
    · intro hh
      exact ⟨fun r => hh _ (Or.inl ⟨r, rfl⟩), fun r => hh _ (Or.inr ⟨r, rfl⟩)⟩
  have hov : (∏ i ∈ (Finset.univ.image (row σ)) ∩ (Finset.univ.image (row τ)), p i) =
      ∏ s ∈ shared row σ τ, p (row τ s) := by
    rw [shared_image, Finset.prod_image (fun _ _ _ _ h => hτ h)]
  have hne : (∏ s ∈ shared row σ τ, p (row τ s)) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun s _ => hpos s))
  apply (eq_mul_inv_iff_mul_eq₀ hne).mpr
  simp only [FiniteLaw.prob, he]
  rw [FiniteLaw.bernoulliProduct_all, ← hov, Finset.prod_union_inter,
    Finset.prod_image (fun _ _ _ _ h => hσ h),
    Finset.prod_image (fun _ _ _ _ h => hτ h)]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq S] [DecidableEq A] in
lemma expect_count (row : (V → A) → S → I) (p : I → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (C : Finset (V → A))
    (hi : ∀ σ ∈ C, Function.Injective (row σ)) (q : S → ℝ)
    (hq : ∀ σ ∈ C, ∀ s, p (row σ s) = q s) :
    (FiniteLaw.bernoulliProduct p hp).expect (fun w => (count row C w : ℝ)) =
      C.card * ∏ s, q s := by
  classical
  have he (w : I → Bool) : (count row C w : ℝ) =
      ∑ σ ∈ C, if Present row w σ then 1 else 0 := by simp [count]
  simp_rw [he]
  unfold FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ σ ∈ C, ∏ s, q s := by
      apply Finset.sum_congr rfl
      intro σ hσ
      change (FiniteLaw.bernoulliProduct p hp).prob _ = _
      rw [prob_present row p hp σ (hi σ hσ)]
      simp_rw [hq σ hσ]
    _ = _ := by simp

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq S] [DecidableEq A] in
lemma variance_count (row : (V → A) → S → I) (p : I → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (C : Finset (V → A))
    (hi : ∀ σ ∈ C, Function.Injective (row σ)) (q : S → ℝ) (hpos : ∀ s, 0 < q s)
    (hq : ∀ σ ∈ C, ∀ s, p (row σ s) = q s) :
    (FiniteLaw.bernoulliProduct p hp).variance (fun w => (count row C w : ℝ)) =
      (∏ s, q s) ^ 2 * ∑ σ ∈ C, ∑ τ ∈ C, ((∏ s ∈ shared row σ τ, q s)⁻¹ - 1) := by
  classical
  have hc (w : I → Bool) : (count row C w : ℝ) ^ 2 =
      ∑ σ ∈ C, ∑ τ ∈ C, if Present row w σ ∧ Present row w τ then 1 else 0 := by
    have hc : (count row C w : ℝ) = ∑ σ ∈ C, if Present row w σ then 1 else 0 := by simp [count]
    rw [hc, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    by_cases hσ : Present row w σ <;> by_cases hτ : Present row w τ <;> simp [hσ,hτ]
  have hs : (FiniteLaw.bernoulliProduct p hp).expect (fun w => (count row C w : ℝ) ^ 2) =
      (∏ s, q s) ^ 2 * ∑ σ ∈ C, ∑ τ ∈ C, (∏ s ∈ shared row σ τ, q s)⁻¹ := by
    simp_rw [hc]
    unfold FiniteLaw.expect
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro τ hτ
    change (FiniteLaw.bernoulliProduct p hp).prob _ = _
    rw [prob_pair row p hp σ τ (hi σ hσ) (hi τ hτ)
      (fun s => by rw [hq τ hτ]; exact hpos s)]
    simp_rw [hq σ hσ, hq τ hτ]
    ring
  rw [FiniteLaw.variance_eq, hs, expect_count row p hp C hi q hq]
  simp_rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

/-- A fixed, finite overcount of all nonempty matching types. Types with
incompatible coordinate constraints simply have zero realizations. -/
abbrev OverlapType (S : Type*) [Fintype S] := {J : Finset S // J.Nonempty} × (S → S)

def OverlapEvent (row : (V → A) → S → I) (σ τ : V → A) (o : OverlapType S) : Prop :=
  ∀ s ∈ o.1.val, row τ s = row σ (o.2 s)

instance (row : (V → A) → S → I) (σ τ : V → A) (o : OverlapType S) :
    Decidable (OverlapEvent row σ τ o) := inferInstanceAs (Decidable (∀ s ∈ o.1.val, _))

omit [Fintype V] [Fintype I] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma inverse_overlap_le (row : (V → A) → S → I) (σ τ : V → A)
    (q : S → ℝ) (hq : ∀ s, 0 < q s) :
    (∏ s ∈ shared row σ τ, q s)⁻¹ - 1 ≤
      ∑ o : OverlapType S, if OverlapEvent row σ τ o then (∏ s ∈ o.1.val, q s)⁻¹ else 0 := by
  classical
  have hn (o : OverlapType S) :
      0 ≤ if OverlapEvent row σ τ o then (∏ s ∈ o.1.val, q s)⁻¹ else 0 := by
    split_ifs
    · exact inv_nonneg.mpr (Finset.prod_nonneg fun s _ => (hq s).le)
    · norm_num
  by_cases he : (shared row σ τ).Nonempty
  · let f (s : S) : S := if hs : ∃ r, row τ s = row σ r then Classical.choose hs else s
    let o : OverlapType S := (⟨shared row σ τ, he⟩, f)
    have ho : OverlapEvent row σ τ o := by
      intro s hs
      have hh : ∃ r, row τ s = row σ r := (Finset.mem_filter.mp hs).2
      exact by simpa [o,f,hh] using Classical.choose_spec hh
    have hsingle := Finset.single_le_sum (fun o _ => hn o) (Finset.mem_univ o)
    simp only [ho, ↓reduceIte] at hsingle
    exact (sub_le_self _ zero_le_one).trans hsingle
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp only [Finset.prod_empty, inv_one, sub_self]
    exact Finset.sum_nonneg fun o _ => hn o

omit [Fintype I] in
/-- Once one admissible second assignment is fixed, every other realization of
an overlap type agrees with it on the union of the selected row supports. This
is a counting fact, not an independence claim about different coordinate fields. -/
lemma overlap_assignment_count (row : (V → A) → S → I) (support : S → Finset V)
    (read : ∀ σ τ s, row σ s = row τ s → ∀ v ∈ support s, σ v = τ v)
    (C : Finset (V → A)) (σ : V → A) (o : OverlapType S) :
    (∑ τ ∈ C, if OverlapEvent row σ τ o then (1 : ℝ) else 0) ≤
      (Fintype.card A : ℝ) ^ (Fintype.card V - (o.1.val.biUnion support).card) := by
  classical
  by_cases he : ∃ τ ∈ C, OverlapEvent row σ τ o
  · obtain ⟨τ₀,hτ₀,he₀⟩ := he
    rw [← TableModel.sum_coincidence τ₀ (o.1.val.biUnion support)]
    calc
      _ ≤ ∑ τ ∈ C, if ∀ v ∈ o.1.val.biUnion support, τ v = τ₀ v then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro τ _
        by_cases hh : OverlapEvent row σ τ o
        · have hread : ∀ v ∈ o.1.val.biUnion support, τ v = τ₀ v := by
            intro v hv
            obtain ⟨s,hs,hv⟩ := Finset.mem_biUnion.mp hv
            exact read τ τ₀ s ((hh s hs).trans (he₀ s hs).symm) v hv
          rw [ite_eq_left hh, ite_eq_left hread]
        · simp only [hh, ↓reduceIte]
          split_ifs <;> norm_num
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
        (fun _ _ _ => by split_ifs <;> norm_num)
  · have hz : ∀ τ ∈ C, ¬OverlapEvent row σ τ o := by simpa using he
    simp only [Finset.sum_eq_zero (fun τ hτ => ite_eq_right (hz τ hτ))]
    positivity

end BernoulliCandidates
end HyperbolicObstruction
end
end

section

end
end

end OAI
