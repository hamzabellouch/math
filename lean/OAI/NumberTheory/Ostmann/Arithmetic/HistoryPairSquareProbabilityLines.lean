import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSquareProbabilityLaws
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeLineFamilies
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeMixedLineFamiliesRepeated

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairSquareProbability
open HistoryCRTIntegration

lemma probability_eq_natCard {α : Type*} [Fintype α] (P : α→Prop) :
    probability P=(Nat.card {x : α // P x}:ℝ)/Fintype.card α := by
  simp only [probability,Nat.card_eq_fintype_card,Fintype.card_subtype]

variable {ι : Type*} [Fintype ι] (p : ℕ) [Fact p.Prime] (A B : ι→ℤ)

lemma base_unit_iff (z : UnitPair p) :
    Base p Finset.univ A B (((z.1:ZMod p).val:ℤ)) (((z.2:ZMod p).val:ℤ))↔
      PrimeLineFamilies.CommonZero (fun i => (A i:ZMod p)) (fun i => (B i:ZMod p)) z := by
  simp only [Base,PrimeLineFamilies.CommonZero,Finset.mem_univ,forall_const,
    ←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_add,Int.cast_mul,Int.cast_natCast,
    ZMod.natCast_zmod_val]

lemma base_mixed_iff (z : MixedPair p) :
    Base p Finset.univ A B ((z.1.val:ℤ)) (((z.2:ZMod p).val:ℤ))↔
      PrimeMixedLineFamilies.CommonZero (fun i => (A i:ZMod p)) (fun i => (B i:ZMod p)) z := by
  simp only [Base,PrimeMixedLineFamilies.CommonZero,Finset.mem_univ,forall_const,
    ←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_add,Int.cast_mul,Int.cast_natCast,
    ZMod.natCast_zmod_val]

theorem unitBaseProbability_eq_lines :
    unitBaseProbability p Finset.univ A B=
      PrimeLineFamilies.probability p (fun i => (A i:ZMod p)) (fun i => (B i:ZMod p)) := by
  rw [unitBaseProbability,probability_eq_natCard,PrimeLineFamilies.probability]
  apply congrArg (fun n : ℕ => (n:ℝ)/Fintype.card (UnitPair p))
  exact Nat.card_congr (Equiv.subtypeEquivRight (base_unit_iff p A B))

theorem mixedBaseProbability_eq_lines :
    mixedBaseProbability p Finset.univ A B=
      PrimeMixedLineFamilies.probability p (fun i => (A i:ZMod p)) (fun i => (B i:ZMod p)) := by
  rw [mixedBaseProbability,probability_eq_natCard,PrimeMixedLineFamilies.probability]
  apply congrArg (fun n : ℕ => (n:ℝ)/Fintype.card (MixedPair p))
  exact Nat.card_congr (Equiv.subtypeEquivRight (base_mixed_iff p A B))

end Ostmann.Arithmetic.HistoryPairSquareProbability

end

end OAI
