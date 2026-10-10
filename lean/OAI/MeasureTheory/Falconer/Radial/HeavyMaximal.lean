import OAI.MeasureTheory.Falconer.Radial.HeavySelection
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

/-! # A finite maximal family of heavy sets

Every heavy set has a substantial intersection with a chosen representative.
The next geometric step turns that intersection into containment in a thicker
hyperplane neighborhood.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem maximal_heavy_family {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (U : Set ι) (A : ι → Set X)
    (hA : ∀ i ∈ U, MeasurableSet (A i)) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (hheavy : ∀ i ∈ U, ENNReal.ofReal m ≤ μ (A i)) :
    ∃ S : Finset ι, (∀ i ∈ S, i ∈ U) ∧ (S.card:ℝ) ≤ 2/m ∧
      ∀ i ∈ U, ∃ j ∈ S, ENNReal.ofReal (m^2/2) < μ (A i ∩ A j) := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Finset ι, S.card = n ∧
    (∀ i ∈ S, i ∈ U) ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      μ (A i ∩ A j) ≤ ENNReal.ofReal (m^2/2)
  let B := Nat.ceil (2/m)
  have hbound (n : ℕ) (hn : P n) : n ≤ B := by
    obtain ⟨S,rfl,hS,hpair⟩ := hn
    have hb := heavy_pairwise_card_bound μ S A (fun i hi => hA i (hS i hi)) hm
      (fun i hi => hheavy i (hS i hi)) hpair
    exact_mod_cast hb.trans (Nat.le_ceil (2/m))
  have hP0 : P 0 := ⟨∅,by simp,by simp,by simp⟩
  obtain ⟨S,hcard,hS,hpair⟩ := Nat.findGreatest_spec (Nat.zero_le B) hP0
  refine ⟨S,hS,heavy_pairwise_card_bound μ S A (fun i hi => hA i (hS i hi)) hm
    (fun i hi => hheavy i (hS i hi)) hpair,?_⟩
  intro i hi
  by_contra hnone
  have hsmall (j : ι) (hj : j ∈ S) : μ (A i ∩ A j) ≤ ENNReal.ofReal (m^2/2) := by
    exact le_of_not_gt (fun h => hnone ⟨j,hj,h⟩)
  have his : i ∉ S := by
    intro his
    have hstrict : ENNReal.ofReal (m^2/2) < ENNReal.ofReal m :=
      (ENNReal.ofReal_lt_ofReal_iff hm).mpr (by nlinarith)
    have hh := hsmall i his
    rw [inter_self] at hh
    exact (not_lt_of_ge hh) (hstrict.trans_le (hheavy i hi))
  have hins : P ((insert i S).card) := by
    refine ⟨insert i S,rfl,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact hS j hj
    · intro j hj k hk hjk
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j
        rcases Finset.mem_insert.mp hk with hki | hkS
        · exact (hjk hki.symm).elim
        · exact hsmall k hkS
      · rcases Finset.mem_insert.mp hk with hki | hkS
        · subst k
          simpa only [inter_comm] using hsmall j hjS
        · exact hpair j hjS k hkS hjk
  have hmax := Nat.le_findGreatest (hbound _ hins) hins
  rw [Finset.card_insert_of_notMem his,hcard] at hmax
  omega

end Falconer

end OAI
