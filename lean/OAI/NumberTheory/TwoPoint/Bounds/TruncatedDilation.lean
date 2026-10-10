import OAI.NumberTheory.TwoPoint.Bounds.SmoothDivisorDecomposition
import OAI.NumberTheory.TwoPoint.Bounds.DivisibilityPrefix

namespace OAI

/-! A fixed dilation is approximated by finitely many smooth-divisor
components. The discarded values lie in a literal smooth-divisor tail. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def smoothDilationTerm (q : ℕ) (f : ℕ → ℂ) (a n : ℕ) : ℂ :=
  if a.primeFactors ⊆ q.primeFactors ∧ a ∣ n then
    f (q * a) * coprimeRestriction q f (n / a) else 0

lemma smoothDilationTerm_eq_zero (q n a : ℕ) (f : ℕ → ℂ)
    (hq : 0 < q) (hn : 0 < n) (ha : a ≠ primeSmoothPart q.primeFactors n) :
    smoothDilationTerm q f a n = 0 := by
  unfold smoothDilationTerm coprimeRestriction
  split_ifs with has hc
  · exact False.elim (ha (primeSmoothPart_unique q n a hq hn has.2 has.1 hc))
  · exact mul_zero _
  · rfl

lemma smoothDilationTerm_at_part {f : ℕ → ℂ} (hf : Multiplicative f)
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    smoothDilationTerm q f (primeSmoothPart q.primeFactors n) n = f (q * n) := by
  let a := primeSmoothPart q.primeFactors n
  let r := primeRoughPart q.primeFactors n
  have ha : 0 < a := primeSmoothPart_pos _ _ hn
  have hr : 0 < r := primeRoughPart_pos _ _ hn
  have he : a * r = n := primeSmoothPart_mul_primeRoughPart _ _ hn
  have hc : q.Coprime r := primeRoughPart_coprime q n hq
  have hac := coprime_of_primeFactors_subset ha (primeSmoothPart_support _ _) hc
  have hd : a ∣ n := ⟨r, he.symm⟩
  have hquot : n / a = r := by rw [← he, Nat.mul_div_cancel_left _ ha]
  change smoothDilationTerm q f a n = _
  rw [smoothDilationTerm, ite_eq_left ⟨primeSmoothPart_support _ _, hd⟩,
    hquot, coprimeRestriction, ite_eq_left hc,
    ← hf (q * a) r (Nat.mul_pos hq ha) hr (hc.mul_left hac)]
  congr 1
  rw [mul_assoc, he]

noncomputable def truncatedDilation (q : ℕ) (f : ℕ → ℂ) (K n : ℕ) : ℂ :=
  if primeSmoothPart q.primeFactors n ≤ K then f (q * n) else 0

lemma truncatedDilation_eq_sum {f : ℕ → ℂ} (hf : Multiplicative f)
    (q n K : ℕ) (hq : 0 < q) (hn : 0 < n) :
    truncatedDilation q f K n = ∑ a ∈ Icc 1 K, smoothDilationTerm q f a n := by
  let a := primeSmoothPart q.primeFactors n
  have ha : 0 < a := primeSmoothPart_pos _ _ hn
  have hsum : (∑ b ∈ Icc 1 K, smoothDilationTerm q f b n) =
      if a ∈ Icc 1 K then smoothDilationTerm q f a n else 0 := by
    by_cases hak : a ∈ Icc 1 K
    · rw [ite_eq_left hak]
      apply sum_eq_single a
      · intro b _ hba
        exact smoothDilationTerm_eq_zero q n b f hq hn hba
      · exact fun h => False.elim (h hak)
    · rw [ite_eq_right hak]
      apply sum_eq_zero
      intro b hb
      apply smoothDilationTerm_eq_zero q n b f hq hn
      intro hba
      change b = a at hba
      exact hak (hba ▸ hb)
  rw [hsum, smoothDilationTerm_at_part hf q n hq hn]
  have ha1 : 1 ≤ a := ha
  change (if a ≤ K then f (q * n) else 0) = _
  simp only [mem_Icc, ha1, true_and]

lemma norm_truncatedDilation_error {f : ℕ → ℂ} (hf : OneBounded f)
    (q n K : ℕ) (hq : 0 < q) (hn : 0 < n) :
    ‖f (q * n) - truncatedDilation q f K n‖ ≤
      if K < primeSmoothPart q.primeFactors n then (1 : ℝ) else 0 := by
  unfold truncatedDilation
  by_cases hs : primeSmoothPart q.primeFactors n ≤ K
  · simp only [hs, ite_true, sub_self, norm_zero, Nat.not_lt.mpr hs, ite_false, le_refl]
  · simp only [hs, ite_false, sub_zero, Nat.lt_of_not_ge hs, ite_true]
    exact hf _ (Nat.mul_pos hq hn)

lemma smoothPart_tail_indicator (q n K : ℕ) (hn : 0 < n) :
    (if K < primeSmoothPart q.primeFactors n then (1 : ℝ) else 0) ≤
      ∑ a ∈ (Icc (K + 1) n).filter (fun a => a.primeFactors ⊆ q.primeFactors),
        if a ∣ n then (1 : ℝ) else 0 := by
  split_ifs with htail
  · let a := primeSmoothPart q.primeFactors n
    have hd : a ∣ n := ⟨primeRoughPart q.primeFactors n,
      (primeSmoothPart_mul_primeRoughPart _ _ hn).symm⟩
    have hm : a ∈ (Icc (K + 1) n).filter (fun a => a.primeFactors ⊆ q.primeFactors) := by
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨htail, Nat.le_of_dvd hn hd⟩,
        primeSmoothPart_support _ _⟩
    have h := single_le_sum (f := fun b : ℕ => if b ∣ n then (1 : ℝ) else 0)
      (fun b _ => by split_ifs <;> positivity) hm
    simpa only [ite_eq_left hd] using h
  · exact sum_nonneg (fun _ _ => by split_ifs <;> positivity)

end TwoPointCorrelations

end OAI
