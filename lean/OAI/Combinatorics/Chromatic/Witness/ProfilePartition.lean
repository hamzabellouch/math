import Mathlib
import OAI.Combinatorics.Chromatic.Walls.LaurentGradedFibers
import OAI.Combinatorics.Chromatic.Witness.GraphDecoratedHistories
import OAI.Combinatorics.Chromatic.Histories.AnchorEmptyMask

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators
open Classical
noncomputable section
variable {A:Type*} [Fintype A] {n:ℕ}

def profilePartition (μ:A →₀ ℕ) (hμ:μ.degree=n):Nat.Partition n:=
  Nat.Partition.ofSums n (Finset.univ.val.map μ) (by
    change (∑i:A,μ i)=n
    rw [←Finsupp.degree_eq_sum]
    exact hμ)

lemma esymmPart_profile {B R:Type*} [Fintype B] [CommSemiring R]
    (μ:A →₀ ℕ) (hμ:μ.degree=n) :
    MvPolynomial.esymmPart B R (profilePartition μ hμ)=∏i:A,MvPolynomial.esymm B R (μ i) := by
  have H:∀l:Multiset ℕ,((l.filter (·≠0)).map (MvPolynomial.esymm B R)).prod=
      (l.map (MvPolynomial.esymm B R)).prod:=by
    intro l
    induction l using Multiset.induction_on with
    | empty=>simp
    | cons k l ih=>
      by_cases hk:k=0
      · subst k; simp [MvPolynomial.esymm_zero,ih]
      · simp [hk,ih]
  unfold MvPolynomial.esymmPart profilePartition
  rw [Nat.Partition.ofSums_parts,H,Multiset.map_map]
  rfl
end
end ElementaryPositivity

end
section
namespace ElementaryPositivity.ExactMasks
open Classical
noncomputable section
instance requiredFintype {A I:Type*} [Fintype A] [DecidableEq I] (mask:A → Finset I) (J:Finset I) :
    Fintype (Required mask J):=inferInstanceAs (Fintype {a:A // J⊆mask a})
instance exactFintype {A I:Type*} [Fintype A] [DecidableEq I] (mask:A → Finset I) (J:Finset I) :
    Fintype (Exact mask J):=inferInstanceAs (Fintype {a:A // mask a=J})
end
end ElementaryPositivity.ExactMasks
namespace ElementaryPositivity.TriangularDynamics
open Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

def requiredHistoryMatching (J:Finset (Fin (n-1))) :
    ExactMasks.GradedEquiv
      (fun w:ExactMasks.Required G.wordMask J=>G.graphInversions w.val)
      (fun w:ExactMasks.Required (decoratedMask G) J=>decoratedEnergy G w.val) :=
  LaurentPositive.gradedEquivOfEnergySum G.edgeCount _ _ (required_energy_sum G J)

def exactHistoryMatching (J:Finset (Fin (n-1))) :
    ExactMasks.GradedEquiv
      (fun w:ExactMasks.Exact G.wordMask J=>G.graphInversions w.val)
      (fun w:ExactMasks.Exact (decoratedMask G) J=>decoratedEnergy G w.val) := by
  letI:Encodable (Equiv.Perm (Fin n)):=Fintype.toEncodable _
  exact ExactMasks.refine G.wordMask (decoratedMask G) G.graphInversions (decoratedEnergy G)
    (requiredHistoryMatching G) J

def admissibleExactEquiv : {w:Equiv.Perm (Fin n) // G.Admissible w} ≃ ExactMasks.Exact G.wordMask ∅ where
  toFun w:=⟨w.val,(G.wordMask_empty w.val).mpr w.property⟩
  invFun w:=⟨w.val,(G.wordMask_empty w.val).mp w.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

def emptyDecoratedEquiv : ExactMasks.Exact (decoratedMask G) ∅ ≃ DecoratedLeaf G where
  toFun w:=w.val.1
  invFun d:=⟨⟨d,((emptyAnchorEquiv.{0,1} (historyProfile G d.1) (historyProfile_degree G d.1)).symm PUnit.unit.{1}).val⟩,
    ((emptyAnchorEquiv.{0,1} (historyProfile G d.1) (historyProfile_degree G d.1)).symm PUnit.unit.{1}).property⟩
  left_inv w:=by
    rcases w with ⟨⟨d,w⟩,hw⟩
    have H: (emptyAnchorEquiv.{0,1} (historyProfile G d.1) (historyProfile_degree G d.1)).symm PUnit.unit.{1}=
        (⟨w,hw⟩:EmptyAnchor (n:=n) (historyProfile G d.1)):=
      (emptyAnchorEquiv.{0,1} (historyProfile G d.1) (historyProfile_degree G d.1)).symm_apply_apply ⟨w,hw⟩
    apply Subtype.ext
    exact congrArg (fun z:EmptyAnchor (n:=n) (historyProfile G d.1)=> (⟨d,z.val⟩:DecoratedWord G)) H
  right_inv _:=rfl

def admissibleHistoryEquiv : {w:Equiv.Perm (Fin n) // G.Admissible w} ≃ DecoratedLeaf G:=
  (admissibleExactEquiv G).trans ((exactHistoryMatching G ∅).val.trans (emptyDecoratedEquiv G))

lemma admissibleHistoryEquiv_energy (w:{w:Equiv.Perm (Fin n) // G.Admissible w}) :
    leafEnergy G (admissibleHistoryEquiv G w)=G.graphInversions w.val:=
  (exactHistoryMatching G ∅).property (admissibleExactEquiv G w)

def leafPartition (d:DecoratedLeaf G):Nat.Partition n:=
  profilePartition (historyProfile G d.1) (historyProfile_degree G d.1)

def admissiblePartition (w:{w:Equiv.Perm (Fin n) // G.Admissible w}):Nat.Partition n:=
  leafPartition G (admissibleHistoryEquiv G w)
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
