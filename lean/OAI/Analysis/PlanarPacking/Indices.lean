import OAI.Analysis.PlanarPacking.Cardinal

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

def node1 : Node := ⟨1,by norm_num [residues]⟩
def node3 : Node := ⟨3,by norm_num [residues]⟩
def node4 : Node := ⟨4,by norm_num [residues]⟩
def jNode : Fin 6 → Node := ![node1,node3,node4,node1,node3,node4]
def jDeriv : Fin 6 → Bool := ![false,false,false,true,true,true]
def node7 : Node := ⟨7,by norm_num [residues]⟩
def node9 : Node := ⟨9,by norm_num [residues]⟩
def node12 : Node := ⟨12,by norm_num [residues]⟩
def node13 : Node := ⟨13,by norm_num [residues]⟩
def node15 : Node := ⟨15,by norm_num [residues]⟩
def node16 : Node := ⟨16,by norm_num [residues]⟩
def lNode : Fin 12 → Node := ![node7,node9,node12,node13,node15,node16,node7,node9,node12,node13,node15,node16]
def lDeriv : Fin 12 → Bool := ![false,false,false,false,false,false,true,true,true,true,true,true]
open scoped BigOperators
def eNode : Fin 48 → Node := ![⟨7,by norm_num [residues]⟩,⟨9,by norm_num [residues]⟩,⟨12,by norm_num [residues]⟩,⟨13,by norm_num [residues]⟩,⟨15,by norm_num [residues]⟩,⟨16,by norm_num [residues]⟩,⟨19,by norm_num [residues]⟩,⟨21,by norm_num [residues]⟩,⟨24,by norm_num [residues]⟩,⟨25,by norm_num [residues]⟩,⟨27,by norm_num [residues]⟩,⟨28,by norm_num [residues]⟩,⟨31,by norm_num [residues]⟩,⟨33,by norm_num [residues]⟩,⟨36,by norm_num [residues]⟩,⟨37,by norm_num [residues]⟩,⟨39,by norm_num [residues]⟩,⟨40,by norm_num [residues]⟩,⟨43,by norm_num [residues]⟩,⟨45,by norm_num [residues]⟩,⟨48,by norm_num [residues]⟩,⟨49,by norm_num [residues]⟩,⟨51,by norm_num [residues]⟩,⟨52,by norm_num [residues]⟩,⟨55,by norm_num [residues]⟩,⟨57,by norm_num [residues]⟩,⟨60,by norm_num [residues]⟩,⟨61,by norm_num [residues]⟩,⟨63,by norm_num [residues]⟩,⟨64,by norm_num [residues]⟩,⟨67,by norm_num [residues]⟩,⟨69,by norm_num [residues]⟩,⟨72,by norm_num [residues]⟩,⟨73,by norm_num [residues]⟩,⟨75,by norm_num [residues]⟩,⟨76,by norm_num [residues]⟩,⟨79,by norm_num [residues]⟩,⟨81,by norm_num [residues]⟩,⟨84,by norm_num [residues]⟩,⟨85,by norm_num [residues]⟩,⟨87,by norm_num [residues]⟩,⟨88,by norm_num [residues]⟩,⟨91,by norm_num [residues]⟩,⟨93,by norm_num [residues]⟩,⟨96,by norm_num [residues]⟩,⟨97,by norm_num [residues]⟩,⟨99,by norm_num [residues]⟩,⟨100,by norm_num [residues]⟩]
def centralIndex (i : Fin 6) : Node × Bool := (jNode i,jDeriv i)
def exteriorIndex (i : Fin 48 × Fin 2) : Node × Bool := (eNode i.1,decide (i.2.val=1))
abbrev FiniteIndex := Fin 6 ⊕ (Fin 48 × Fin 2)
def finiteIndex : FiniteIndex → Node × Bool := Sum.elim centralIndex exteriorIndex
def lowExteriorIndex (i : Fin 12) : Node × Bool := (lNode i,lDeriv i)
lemma centralIndex_injective : Function.Injective centralIndex := by decide +kernel
lemma exteriorIndex_injective : Function.Injective exteriorIndex := by decide +kernel
lemma finiteIndex_injective : Function.Injective finiteIndex := by decide +kernel
lemma lowExteriorIndex_injective : Function.Injective lowExteriorIndex := by decide +kernel
lemma centralIndex_bound (i : Fin 6) : (centralIndex i).1.val ≤ 4 := by revert i; decide +kernel
lemma exteriorIndex_bound (i : Fin 48 × Fin 2) : 4 < (exteriorIndex i).1.val ∧ (exteriorIndex i).1.val ≤ 100 := by revert i; decide +kernel
lemma finiteIndex_bound (i : FiniteIndex) : (finiteIndex i).1.val ≤ 100 := by revert i; decide +kernel
lemma lowExteriorIndex_bound (i : Fin 12) : 4 < (lowExteriorIndex i).1.val ∧ (lowExteriorIndex i).1.val ≤ 16 := by revert i; decide +kernel
lemma finiteIndex_cover_check : ∀ n : Fin 101, 0<n.val ∧ n.val%12∈residues → ∀ d : Bool,
    ∃ i : FiniteIndex, (finiteIndex i).1.val=n.val ∧ (finiteIndex i).2=d := by decide +kernel
lemma finiteIndex_range (n : Node) (d : Bool) : (∃ i, finiteIndex i = (n,d)) ↔ n.val ≤ 100 := by
  constructor
  · rintro ⟨i,hi⟩
    have hh := finiteIndex_bound i
    simpa only [hi] using hh
  · intro hn
    obtain ⟨i,hin,hid⟩ := finiteIndex_cover_check ⟨n.val,Nat.lt_succ_of_le hn⟩ n.prop d
    exact ⟨i,Prod.ext (Subtype.ext hin) hid⟩
lemma exteriorIndex_cover_check : ∀ n : Fin 101, 4<n.val ∧ n.val%12∈residues → ∀ d : Bool,
    ∃ i : Fin 48 × Fin 2, (exteriorIndex i).1.val=n.val ∧ (exteriorIndex i).2=d := by decide +kernel
lemma exteriorIndex_range (n : Node) (d : Bool) : (∃ i, exteriorIndex i = (n,d)) ↔ 4<n.val ∧ n.val ≤ 100 := by
  constructor
  · rintro ⟨i,hi⟩
    have hh := exteriorIndex_bound i
    simpa only [hi] using hh
  · rintro ⟨hn,hm⟩
    obtain ⟨i,hin,hid⟩ := exteriorIndex_cover_check ⟨n.val,Nat.lt_succ_of_le hm⟩ ⟨hn,n.prop.2⟩ d
    exact ⟨i,Prod.ext (Subtype.ext hin) hid⟩
lemma lowExteriorIndex_cover_check : ∀ n : Fin 17, 4<n.val ∧ n.val%12∈residues → ∀ d : Bool,
    ∃ i : Fin 12, (lowExteriorIndex i).1.val=n.val ∧ (lowExteriorIndex i).2=d := by decide +kernel
lemma lowExteriorIndex_range (n : Node) (d : Bool) : (∃ i, lowExteriorIndex i = (n,d)) ↔ 4<n.val ∧ n.val ≤ 16 := by
  constructor
  · rintro ⟨i,hi⟩
    have hh := lowExteriorIndex_bound i
    simpa only [hi] using hh
  · rintro ⟨hn,hm⟩
    obtain ⟨i,hin,hid⟩ := lowExteriorIndex_cover_check ⟨n.val,Nat.lt_succ_of_le hm⟩ ⟨hn,n.prop.2⟩ d
    exact ⟨i,Prod.ext (Subtype.ext hin) hid⟩
end SharpPlanar.Numerical

end OAI
