import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.MarkingClassDomains

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section

abbrev SlotClass := Fin 7 ⊕ (Fin 7 ⊕ (Fin 5 × Fin 5))

lemma slotClass_card : Fintype.card SlotClass=39 := by decide

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N : ℕ}
local instance slotPointDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance slotDualDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
local instance slotDualDualDE : DecidableEq (ℙ K (Dual K (Dual K V))) := Classical.decEq _

def classValid (width : ℝ) (m : UnionTranscript (Fin N) (FlagPair K V))
    (i : Fin N) : SlotClass → Prop
  | .inl b => ∃ u,Real.log (Nat.card K) ≤ u ∧ u ≤ 4*Real.log (Nat.card K) ∧
      ForwardCaps (markingDomain m i) u ∧ BandCondition (Real.log (Nat.card K)) width u b
  | .inr (.inl b) => ∃ u,Real.log (Nat.card K) ≤ u ∧ u ≤ 4*Real.log (Nat.card K) ∧
      ReverseCaps (markingDomain m i) u ∧ BandCondition (Real.log (Nat.card K)) width u b
  | .inr (.inr (r,s)) => (m.1 i).1.1.1=r ∧ (m.1 i).1.1.2=s ∧
      (m.1 i).1.2.1=true ∧ (m.1 i).1.2.2=true ∧ 5 < r.val+s.val

omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))]

theorem exists_valid_class (hdim : finrank K V=5) (width : ℝ) (hw : 0 ≤ width)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty) : ∃ c,classValid width m i c := by
  rcases marking_domain_dichotomy hdim m i hne with h | h | h
  · obtain ⟨u,hu,hu',hc⟩:=h
    obtain ⟨b,hb⟩:=exists_reciprocal_band hw hu hu'
    exact ⟨.inl b,u,hu,hu',hc,hb⟩
  · obtain ⟨u,hu,hu',hc⟩:=h
    obtain ⟨b,hb⟩:=exists_reciprocal_band hw hu hu'
    exact ⟨.inr (.inl b),u,hu,hu',hc,hb⟩
  · exact ⟨.inr (.inr ((m.1 i).1.1.1,(m.1 i).1.1.2)),rfl,rfl,h⟩

def markingClass (hdim : finrank K V=5) (width : ℝ) (hw : 0 ≤ width)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) : SlotClass :=
  if hne : (markingDomain m i).Nonempty then (exists_valid_class hdim width hw m i hne).choose
  else .inl 0

lemma markingClass_valid (hdim : finrank K V=5) (width : ℝ) (hw : 0 ≤ width)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty) : classValid width m i (markingClass hdim width hw m i) := by
  simp only [markingClass,dite_eq_left hne]
  exact (exists_valid_class hdim width hw m i hne).choose_spec

end
end SharpRamseyFive.Marking

end OAI
