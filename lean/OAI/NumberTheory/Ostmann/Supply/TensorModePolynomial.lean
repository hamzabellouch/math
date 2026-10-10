import OAI.NumberTheory.Ostmann.Supply.TensorModeDecomposition

namespace OAI

noncomputable section
namespace Ostmann.Supply.TensorModes
open TensorOperators
open Finset
open scoped TensorProduct BigOperators

section Coefficients
variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tensorPolynomial_apply (c : (ℕ × ℕ) →₀ (E →L[ℂ] F))
    (d : (ℕ × ℕ) →₀ (G →L[ℂ] H)) (ij : ℕ × ℕ) :
    tensorPolynomial c d ij = ∑ ab ∈ c.support, ∑ kl ∈ d.support,
      if (ab.1+kl.1, ab.2+kl.2) = ij then TensorProduct.mapL (c ab) (d kl) else 0 := by
  simp only [tensorPolynomial, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]

end Coefficients

section Family
variable {E F : ℕ → FiniteHilbertSpace}
variable (c : ∀ i, (ℕ × ℕ) →₀ (augmentedSpace (E i) →L[ℂ] augmentedSpace (F i)))

theorem coefficient_high_output_zero (n : ℕ)
    (hzero : ∀ i < n, (centeredPart (F i)).comp (c i (0,0)) = 0)
    (ij : ℕ × ℕ) (s : Finset ℕ) (hs : s ⊆ range n) (hcard : ij.1+ij.2 < s.card) :
    (exactMode F n s).comp (tensorFamilyPolynomial c n ij) = 0 := by
  induction n generalizing ij s with
  | zero =>
    have hs0 : s = ∅ := by simpa using hs
    subst s
    simp at hcard
  | succ n ih =>
    have hzerop : ∀ i < n, (centeredPart (F i)).comp (c i (0,0)) = 0 :=
      fun i hi => hzero i (by omega)
    change (TensorProduct.mapL (exactMode F n s)
      (if n ∈ s then centeredPart (F n) else scalarPart (F n))).comp
        (tensorPolynomial (tensorFamilyPolynomial c n) (c n) ij) = 0
    rw [tensorPolynomial_apply, ContinuousLinearMap.comp_finsetSum]
    apply sum_eq_zero
    intro ab hab
    rw [ContinuousLinearMap.comp_finsetSum]
    apply sum_eq_zero
    intro kl hkl
    by_cases hij : (ab.1+kl.1, ab.2+kl.2) = ij
    · rw [ite_eq_left hij]
      have hfst := congrArg Prod.fst hij
      have hsnd := congrArg Prod.snd hij
      dsimp at hfst hsnd
      rw [← TensorProduct.mapL_comp]
      by_cases hn : n ∈ s
      · rw [ite_eq_left hn]
        by_cases hk0 : kl = (0,0)
        · subst kl
          rw [hzero n (by omega), TensorProduct.mapL_zero_right]
        · have hkpos : 1 ≤ kl.1+kl.2 := by rcases kl with ⟨k,l⟩; simp only [Prod.mk.injEq] at hk0; omega
          have hsub : s.erase n ⊆ range n := by
            intro i hi
            obtain ⟨hin, his⟩ := mem_erase.mp hi
            have hir := mem_range.mp (hs his)
            exact mem_range.mpr (by omega)
          have hc := card_erase_add_one hn
          have hprev : ab.1+ab.2 < (s.erase n).card := by omega
          rw [← exactMode_erase_top F n s, ih hzerop ab (s.erase n) hsub hprev,
            TensorProduct.mapL_zero_left]
      · rw [ite_eq_right hn]
        have hsub : s ⊆ range n := by
          intro i hi
          have hir := mem_range.mp (hs hi)
          have hin : i ≠ n := fun h => hn (h ▸ hi)
          exact mem_range.mpr (by omega)
        have hprev : ab.1+ab.2 < s.card := by omega
        rw [ih hzerop ab s hsub hprev, TensorProduct.mapL_zero_left]
    · rw [ite_eq_right hij]
      simp

theorem coefficient_high_input_zero (n : ℕ)
    (hzero : ∀ i < n, (c i (0,0)).comp (centeredPart (E i)) = 0)
    (ij : ℕ × ℕ) (s : Finset ℕ) (hs : s ⊆ range n) (hcard : ij.1+ij.2 < s.card) :
    (tensorFamilyPolynomial c n ij).comp (exactMode E n s) = 0 := by
  induction n generalizing ij s with
  | zero =>
    have hs0 : s = ∅ := by simpa using hs
    subst s
    simp at hcard
  | succ n ih =>
    have hzerop : ∀ i < n, (c i (0,0)).comp (centeredPart (E i)) = 0 :=
      fun i hi => hzero i (by omega)
    change (tensorPolynomial (tensorFamilyPolynomial c n) (c n) ij).comp
      (TensorProduct.mapL (exactMode E n s)
        (if n ∈ s then centeredPart (E n) else scalarPart (E n))) = 0
    rw [tensorPolynomial_apply, ContinuousLinearMap.finsetSum_comp]
    apply sum_eq_zero
    intro ab hab
    rw [ContinuousLinearMap.finsetSum_comp]
    apply sum_eq_zero
    intro kl hkl
    by_cases hij : (ab.1+kl.1, ab.2+kl.2) = ij
    · rw [ite_eq_left hij]
      have hfst := congrArg Prod.fst hij
      have hsnd := congrArg Prod.snd hij
      dsimp at hfst hsnd
      rw [← TensorProduct.mapL_comp]
      by_cases hn : n ∈ s
      · rw [ite_eq_left hn]
        by_cases hk0 : kl = (0,0)
        · subst kl
          rw [hzero n (by omega), TensorProduct.mapL_zero_right]
        · have hkpos : 1 ≤ kl.1+kl.2 := by rcases kl with ⟨k,l⟩; simp only [Prod.mk.injEq] at hk0; omega
          have hsub : s.erase n ⊆ range n := by
            intro i hi
            obtain ⟨hin, his⟩ := mem_erase.mp hi
            have hir := mem_range.mp (hs his)
            exact mem_range.mpr (by omega)
          have hc := card_erase_add_one hn
          have hprev : ab.1+ab.2 < (s.erase n).card := by omega
          rw [← exactMode_erase_top E n s, ih hzerop ab (s.erase n) hsub hprev,
            TensorProduct.mapL_zero_left]
      · rw [ite_eq_right hn]
        have hsub : s ⊆ range n := by
          intro i hi
          have hir := mem_range.mp (hs hi)
          have hin : i ≠ n := fun h => hn (h ▸ hi)
          exact mem_range.mpr (by omega)
        have hprev : ab.1+ab.2 < s.card := by omega
        rw [ih hzerop ab s hsub hprev, TensorProduct.mapL_zero_left]
    · rw [ite_eq_right hij]
      simp

theorem rectangularTruncation_lowModes (n K : ℕ)
    (hout : ∀ i < n, (centeredPart (F i)).comp (c i (0,0)) = 0)
    (hin : ∀ i < n, (c i (0,0)).comp (centeredPart (E i)) = 0) :
    BivariateTruncation.rectangularTruncation (tensorFamilyPolynomial c n) K =
      ((lowModes F n (2*K)).comp
        (BivariateTruncation.rectangularTruncation (tensorFamilyPolynomial c n) K)).comp
          (lowModes E n (2*K)) := by
  have hleft : (lowModes F n (2*K)).comp
      (BivariateTruncation.rectangularTruncation (tensorFamilyPolynomial c n) K) =
      BivariateTruncation.rectangularTruncation (tensorFamilyPolynomial c n) K := by
    apply lowModes_comp_of_high_zero
    intro s hs hcard
    rw [BivariateTruncation.rectangularTruncation, ContinuousLinearMap.comp_finsetSum]
    apply sum_eq_zero
    intro ij hij
    have hi := (mem_filter.mp hij).2.1
    have hj := (mem_filter.mp hij).2.2
    exact coefficient_high_output_zero c n hout ij s hs (by omega)
  have hright : (BivariateTruncation.rectangularTruncation (tensorFamilyPolynomial c n) K).comp
      (lowModes E n (2*K)) =
      BivariateTruncation.rectangularTruncation (tensorFamilyPolynomial c n) K := by
    apply comp_lowModes_of_high_zero
    intro s hs hcard
    rw [BivariateTruncation.rectangularTruncation, ContinuousLinearMap.finsetSum_comp]
    apply sum_eq_zero
    intro ij hij
    have hi := (mem_filter.mp hij).2.1
    have hj := (mem_filter.mp hij).2.2
    exact coefficient_high_input_zero c n hin ij s hs (by omega)
  rw [hleft, hright]

end Family
end Ostmann.Supply.TensorModes

end

end OAI
