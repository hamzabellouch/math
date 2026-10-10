import OAI.NumberTheory.CubicMoment.Estimates.PrimeStoppingSplit

namespace OAI

/-! The stopped crossing tests with one prime left free. A distinguished
prime enters by its actual norm; a selected-bin prime leaves every
surrogate prefix unchanged while its bin is fixed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largestPrimePredicate (code : Eisenstein → ℕ) (s : Finset Eisenstein)
    (p : Eisenstein) : Prop :=
  ∀ q ∈ s, normNat q < normNat p ∨ (normNat q = normNat p ∧ code q ≤ code p)

/-- A fixed-order tie rule changes the lower norm interval at just the
single norm of the largest complementary prime. -/
lemma largestPrimePredicate_away_tie (code : Eisenstein → ℕ)
    (s : Finset Eisenstein) (p : Eisenstein) (hne : normNat p ≠ s.sup normNat) :
    largestPrimePredicate code s p ↔ s.sup normNat < normNat p := by
  constructor
  · intro h
    have hs : s.sup normNat ≤ normNat p := by
      apply Finset.sup_le
      intro q hq
      rcases h q hq with hlt | he
      · exact hlt.le
      · exact he.1.le
    exact lt_of_le_of_ne hs hne.symm
  · intro h q hq
    exact Or.inl ((Finset.le_sup (f := normNat) hq).trans_lt h)

lemma crossing_norm_interval {a S ell Z x : ℝ} (ha : 0 < a)
    (hS : 0 < S) (hell : 0 < ell) :
    (a*x*S/ell < Z ∧ Z ≤ a*x*S) ↔
      Z/(a*S) ≤ x ∧ x < Z*ell/(a*S) := by
  have hAS : 0 < a*S := mul_pos ha hS
  have he : a*x*S = x*(a*S) := by ring
  rw [he]
  constructor
  · rintro ⟨hu,hl⟩
    exact ⟨(div_le_iff₀ hAS).mpr (by nlinarith),
      (lt_div_iff₀ hAS).mpr ((div_lt_iff₀ hell).mp hu)⟩
  · rintro ⟨hl,hu⟩
    exact ⟨(div_lt_iff₀ hell).mpr ((lt_div_iff₀ hAS).mp hu),
      (div_le_iff₀ hAS).mp hl⟩

lemma distinguished_prime_crossing_interval {r p : Eisenstein}
    (hr : r ≠ 0) {S ell Z : ℝ} (hS : 0 < S) (hell : 0 < ell) :
    (norm (r*p)*S/ell < Z ∧ Z ≤ norm (r*p)*S) ↔
      Z/(norm r*S) ≤ norm p ∧ norm p < Z*ell/(norm r*S) := by
  rw [norm_mul_eq]
  exact crossing_norm_interval (norm_pos_of_ne_zero hr) hS hell

lemma product_norm_interval {r p : Eisenstein} (hr : r ≠ 0) (A B : ℝ) :
    (A ≤ norm (r*p) ∧ norm (r*p) ≤ B) ↔
      A/norm r ≤ norm p ∧ norm p ≤ B/norm r := by
  rw [norm_mul_eq]
  have h := norm_pos_of_ne_zero hr
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨(div_le_iff₀ h).mpr (by nlinarith),
      (le_div_iff₀ h).mpr (by nlinarith)⟩
  · rintro ⟨ha,hb⟩
    constructor
    · nlinarith [(div_le_iff₀ h).mp ha]
    · nlinarith [(le_div_iff₀ h).mp hb]

lemma primeSurrogate_insert_same_bin (s : Finset Eisenstein)
    (b : Eisenstein → ℕ) (ell : ℕ → ℝ) {p q : Eisenstein}
    (hp : p ∉ s) (hq : q ∉ s) (hb : b p = b q) :
    primeSurrogate (insert p s) b ell = primeSurrogate (insert q s) b ell := by
  simp only [primeSurrogate,Finset.prod_insert hp,Finset.prod_insert hq,hb]

lemma primeSurrogate_prefix_insert_same_bin (s : Finset Eisenstein)
    (b : Eisenstein → ℕ) (ell : ℕ → ℝ) {p q : Eisenstein}
    (hp : p ∉ s) (hq : q ∉ s) (hb : b p = b q) (j : ℕ) :
    primeSurrogate (primeBinPrefix (insert p s) b j) b ell =
      primeSurrogate (primeBinPrefix (insert q s) b j) b ell := by
  by_cases hj : b p < j
  · have hqj : b q < j := by simpa only [←hb] using hj
    have hp' : p ∉ primeBinPrefix s b j := fun h => hp (Finset.mem_filter.mp h).1
    have hq' : q ∉ primeBinPrefix s b j := fun h => hq (Finset.mem_filter.mp h).1
    simp only [primeBinPrefix,Finset.filter_insert,hj,hqj,ite_true]
    exact primeSurrogate_insert_same_bin _ b ell hp' hq' hb
  · have hqj : ¬b q < j := by simpa only [←hb] using hj
    simp only [primeBinPrefix,Finset.filter_insert,hj,hqj,ite_false]

lemma primeBin_card_insert_same_bin (s : Finset Eisenstein)
    (b : Eisenstein → ℕ) {p q : Eisenstein}
    (hp : p ∉ s) (hq : q ∉ s) (hb : b p = b q) (j : ℕ) :
    (primeBin (insert p s) b j).card = (primeBin (insert q s) b j).card := by
  by_cases hj : b p = j
  · have hqj : b q = j := hb.symm.trans hj
    have hp' : p ∉ s.filter (fun r => b r = j) := fun h => hp (Finset.mem_filter.mp h).1
    have hq' : q ∉ s.filter (fun r => b r = j) := fun h => hq (Finset.mem_filter.mp h).1
    simp only [primeBin,Finset.filter_insert,hj,hqj,ite_true,
      Finset.card_insert_of_notMem hp',Finset.card_insert_of_notMem hq']
  · have hqj : ¬b q = j := fun h => hj (hb.trans h)
    simp only [primeBin,Finset.filter_insert,hj,hqj,ite_false]

end CubicFirstMoment

end

end OAI
