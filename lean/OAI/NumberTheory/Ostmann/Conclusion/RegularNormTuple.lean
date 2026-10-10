import OAI.NumberTheory.Ostmann.Conclusion.RegularNormPointwise
import OAI.NumberTheory.Ostmann.Construction.ActualRows
import OAI.NumberTheory.Ostmann.Construction.FavorableGiant

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open scoped BigOperators
open Ostmann.Construction Ostmann.Arithmetic.PrimeCellReplacement

theorem supported_regular_small_pairwise (p q : ℕ) (s : ℤ) (small : List SmallSlot)
    (outside : List ℕ) (hs : (State.mk s p q small).Coprime outside) :
    Pairwise (fun i j : Fin small.length => small[i].value.Coprime small[j].value) := by
  have hl : (small.map SmallSlot.value).Pairwise Nat.Coprime :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_append.mp hs).1).2).2
  have hl' : small.Pairwise (fun a b => a.value.Coprime b.value) := List.pairwise_map.mp hl
  have hh := List.pairwise_iff_getElem.mp hl'
  intro i j hij
  by_cases hlt : i.val<j.val
  · exact hh i.val j.val i.isLt j.isLt hlt
  · have hji : j.val < i.val := by omega
    exact Nat.Coprime.symm (by
      exact hh j.val i.val j.isLt i.isLt hji)

theorem exists_actual_regular_tuple_bound :
    ∃ dAP K L₀ : ℝ, 0<dAP ∧ 0<K ∧ 1≤L₀ ∧
      ∀ (d : Decomposition) (P : Finset ℕ) (c : ℝ), L₀+1≤c → 2≤c →
      ∀ (hZ : 0<logCellMass c ∅) (small : List SmallSlot),
      (∀ z∈small, Nat.Prime z.value) →
      (logCellMass c ∅)⁻¹≤2*c →
      (Pairwise (fun i j : Fin small.length => small[i].value.Coprime small[j].value) →
        ((regularSmallModulus small : ℕ) : ℝ)/(regularSmallModulus small).totient≤2) →
      (regularSmallModulus small : ℝ)≤Real.exp (dAP*(c-1)^(1/3 : ℝ)) →
      2*K*c*(regularSmallModulus small)*Real.exp (-dAP*(c-1)^(1/3 : ℝ))≤1 →
      ∀ (outside : List ℕ) (s : ℤ) (q : ℕ),
      (logCellPrior c ∅ hZ).mean (fun p =>
        ‖supportedRegularTransform (residueTransform d) (favorableGiantResidueTransform d P)
          outside (State.mk s p.val q small)‖^2)≤18 := by
  obtain ⟨dAP,K,L₀,hd,hK,hL,hbound⟩ := exists_regular_logCell_test_bound
  refine ⟨dAP,K,L₀,hd,hK,hL,?_⟩
  intro d P c hc hc2 hZ small hprime hZinv hratio hmod herr outside s q
  let : ∀ i : Fin small.length, Fact small[i].value.Prime :=
    fun i => ⟨hprime _ (List.getElem_mem i.isLt)⟩
  let : NeZero (regularSmallModulus small) := ⟨Finset.prod_ne_zero_iff.mpr
    (fun i _ => (hprime _ (List.getElem_mem i.isLt)).ne_zero)⟩
  by_cases hex : ∃ p : LogCellSample c ∅,
      (State.mk s p.val q small).Coprime outside
  · obtain ⟨p,hp⟩ := hex
    have hcop := supported_regular_small_pairwise p.val q s small outside hp
    refine ((logCellPrior c ∅ hZ).mean_mono (fun p =>
      supportedRegularTransform_sq_le_unitTest _ _
        (favorableGiantResidueTransform_norm_le d P) outside s p.val q small hcop)).trans ?_
    apply hbound c hc hc2 (regularSmallModulus small) hZ hZinv (hratio hcop) hmod herr
    · exact regularSmallUnitTest_nonneg _ _ _ _ _ _
    · apply regularSmallUnitTest_sum_le
      · intro i
        rw [residueTransform_eq]
        exact Supply.additiveTransform_zero _
      · intro i
        exact residueTransform_sq_sum d _ (hprime _ (List.getElem_mem i.isLt))
  · have heq : (logCellPrior c ∅ hZ).mean (fun p =>
        ‖supportedRegularTransform (residueTransform d) (favorableGiantResidueTransform d P)
          outside (State.mk s p.val q small)‖^2)=0 := by
      unfold FinitePrior.mean
      apply Finset.sum_eq_zero
      intro p hp
      have hfalse : ¬((State.mk s p.val q small).Coprime outside ∧ s≠0) :=
        fun h => hex ⟨p,h.1⟩
      simp only [supportedRegularTransform,ite_eq_right hfalse,norm_zero,
        zero_pow (by decide : 2≠0),mul_zero]
    rw [heq]
    norm_num

end Ostmann.Conclusion

end

end OAI
