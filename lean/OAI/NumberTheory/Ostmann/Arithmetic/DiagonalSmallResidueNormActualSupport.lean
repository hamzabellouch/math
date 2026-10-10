import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNormActualProduct
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryResidueRegular

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.DiagonalSmallResidueNorm
open Construction
open scoped BigOperators

structure SmallUnitData (D P q : ℕ) (outerU xs : List SmallSlot) (v : ℤ) : Prop where
  frequency : ∀ i : Fin xs.length, IsUnit (v : ZMod xs[i].value)
  denominator : ∀ i : Fin xs.length,
    IsUnit (coefficientDenominator D outerU xs xs[i].value : ZMod xs[i].value)
  giant : ∀ i, IsUnit (q : ZMod (smallPrime xs outerU i))
  outer : ∀ i : Fin outerU.length, IsUnit (P : ZMod outerU[i].value)
  coprime : Pairwise (fun i j => (smallPrime xs outerU i).Coprime (smallPrime xs outerU j))

theorem pairwise_slot_values {xs : List SmallSlot}
    (h : (xs.map SmallSlot.value).Pairwise Nat.Coprime) :
    Pairwise (fun i j : Fin xs.length => xs[i].value.Coprime xs[j].value) := by
  have hf : (List.ofFn (fun i : Fin xs.length => xs[i].value)).Pairwise Nat.Coprime := by
    have he : List.ofFn (fun i : Fin xs.length => xs[i].value) =
        xs.map SmallSlot.value := List.ofFn_getElem_eq_map xs SmallSlot.value
    rw [he]
    exact h
  have hh := List.pairwise_ofFn.mp hf
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hh hij
  · exact (hh hji).symm

theorem smallUnitData_of_pairwise (P q : ℕ) (outerU xs : List SmallSlot)
    (outside : List ℕ) (v : ℤ)
    [∀ i, Fact (smallPrime xs outerU i).Prime]
    (hpair : (P :: q :: (outerU.map SmallSlot.value ++ xs.map SmallSlot.value ++ outside)).Pairwise Nat.Coprime)
    (hv : v ≠ 0) (hlarge : ∀ i : Fin xs.length, v.natAbs < xs[i].value) :
    SmallUnitData outside.prod P q outerU xs v := by
  obtain ⟨hP, hrest⟩ := List.pairwise_cons.mp hpair
  obtain ⟨hq, hall⟩ := List.pairwise_cons.mp hrest
  obtain ⟨hsmall, houtside, hcross⟩ := List.pairwise_append.mp hall
  obtain ⟨hU, hxs, hUx⟩ := List.pairwise_append.mp hsmall
  have hmemx (i : Fin xs.length) : xs[i].value ∈ xs.map SmallSlot.value :=
    List.mem_map.mpr ⟨xs[i], List.getElem_mem i.isLt, rfl⟩
  have hmemU (i : Fin outerU.length) : outerU[i].value ∈ outerU.map SmallSlot.value :=
    List.mem_map.mpr ⟨outerU[i], List.getElem_mem i.isLt, rfl⟩
  constructor
  · intro i
    let : Fact xs[i].value.Prime := inferInstanceAs (Fact (smallPrime xs outerU (.inl i)).Prime)
    exact isUnit_iff_ne_zero.mpr (HistoryResidueRegular.intCast_ne_zero_of_natAbs_lt hv (hlarge i))
  · intro i
    have hD : outside.prod.Coprime xs[i].value := by
      apply Nat.coprime_list_prod_left_iff.mpr
      intro n hn
      exact (hcross _ (List.mem_append_right _ (hmemx i)) n hn).symm
    have hU' : (smallProduct outerU).Coprime xs[i].value := by
      apply Nat.coprime_list_prod_left_iff.mpr
      intro n hn
      exact hUx n hn _ (hmemx i)
    have hR : (smallProduct xs / xs[i].value).Coprime xs[i].value :=
      coprime_prod_div_of_pairwise hxs (hmemx i)
        (show (smallPrime xs outerU (.inl i)).Prime from Fact.out).pos
    exact (ZMod.isUnit_iff_coprime _ _).mpr ((hD.mul_left hU').mul_left hR)
  · intro i
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    cases i with
    | inl i => exact hq _ (List.mem_append_left _ (List.mem_append_right _ (hmemx i)))
    | inr i => exact hq _ (List.mem_append_left _ (List.mem_append_left _ (hmemU i)))
  · intro i
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    exact hP _ (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_left _ (hmemU i))))
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact pairwise_slot_values hxs (fun he => hij (congrArg Sum.inl he))
      | inr j => exact (hUx _ (hmemU j) _ (hmemx i)).symm
    | inr i =>
      cases j with
      | inl j => exact hUx _ (hmemU i) _ (hmemx j)
      | inr j => exact pairwise_slot_values hU (fun he => hij (congrArg Sum.inr he))

theorem smallUnitData_of_state (a : State) (outerU xs : List SmallSlot)
    (outside : List ℕ) [∀ i, Fact (smallPrime xs outerU i).Prime]
    (hslots : a.small.Perm (outerU ++ xs)) (hcop : a.Coprime outside)
    (hv : a.frequency ≠ 0)
    (hlarge : ∀ i : Fin xs.length, a.frequency.natAbs < xs[i].value) :
    SmallUnitData outside.prod a.giantPlus a.giantMinus outerU xs a.frequency := by
  have he : a.values.Perm (a.giantPlus :: a.giantMinus ::
      (outerU.map SmallSlot.value ++ xs.map SmallSlot.value)) := by
    simpa only [State.values, List.map_append] using
      List.Perm.cons a.giantPlus (List.Perm.cons a.giantMinus (hslots.map SmallSlot.value))
  apply smallUnitData_of_pairwise a.giantPlus a.giantMinus outerU xs outside a.frequency
    _ hv hlarge
  simpa only [List.cons_append] using
    ((he.append_right outside).pairwise_iff Nat.Coprime.symm).mp hcop

end Ostmann.Arithmetic.DiagonalSmallResidueNorm

end

end OAI
