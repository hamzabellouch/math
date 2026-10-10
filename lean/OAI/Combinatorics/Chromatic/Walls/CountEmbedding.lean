import Mathlib
import OAI.Combinatorics.Chromatic.Walls.StringStrip

namespace OAI

section
namespace ElementaryPositivity.SignedMultiplicity
noncomputable section
variable {A B : Type*} (e : A ↪ B) (even : B → Prop)

def embedCount (f : CountSelection (fun a=>even (e a))) : CountSelection even :=
  ⟨f.val.embDomain e,by
    intro b hb
    by_cases H : b∈Set.range e
    · obtain ⟨a,rfl⟩:=H
      rw [Finsupp.embDomain_apply_self]
      exact f.property a hb
    · rw [Finsupp.embDomain_of_notMem_range _ _ _ H]
      exact Nat.zero_le _⟩

lemma embedCount_injective : Function.Injective (embedCount e even) := by
  intro f g H
  apply Subtype.ext
  exact Finsupp.embDomain_injective e (congrArg Subtype.val H)

lemma embedCount_support (f : CountSelection (fun a=>even (e a))) :
    ↑(embedCount e even f).val.support ⊆ Set.range e := by
  intro b hb
  by_contra H
  exact Finsupp.mem_support_iff.mp hb (Finsupp.embDomain_of_notMem_range _ _ _ H)

lemma embedCount_sum {T : Type*} [AddCommMonoid T] (f : CountSelection (fun a=>even (e a)))
    (k : B → T) :
    (embedCount e even f).val.sum (fun b n=>n • k b)=f.val.sum (fun a n=>n • k (e a)) := by
  exact Finsupp.sum_embDomain

def restrictCount (f : CountSelection even) : CountSelection (fun a=>even (e a)) :=
  ⟨f.val.comapDomain e e.injective.injOn,fun a ha=>f.property (e a) ha⟩

def countSupportEquiv : CountSelection (fun a=>even (e a)) ≃
    {f : CountSelection even // ↑f.val.support ⊆ Set.range e} where
  toFun f:=⟨embedCount e even f,embedCount_support e even f⟩
  invFun f:=restrictCount e even f.val
  left_inv f:=by
    apply Subtype.ext
    exact Finsupp.comapDomain_embDomain e f.val
  right_inv f:=by
    apply Subtype.ext
    apply Subtype.ext
    exact Finsupp.embDomain_comapDomain f.property

variable {I : Type*} (dim : B → (I→ℕ))

def dimensionSupportEquiv (d : I→ℕ) :
    DimensionCounts (fun a=>even (e a)) (fun a=>dim (e a)) d ≃
      {f : DimensionCounts even dim d // ↑f.val.val.support ⊆ Set.range e} where
  toFun f:=⟨⟨embedCount e even f.val,by
    change (embedCount e even f.val).val.sum _=d
    rw [embedCount_sum]
    exact f.property⟩,embedCount_support e even f.val⟩
  invFun f:=⟨restrictCount e even f.val.val,by
    have H:=embedCount_sum e even (restrictCount e even f.val.val) dim
    have HE : embedCount e even (restrictCount e even f.val.val)=f.val.val :=
      Subtype.ext (Finsupp.embDomain_comapDomain f.property)
    rw [HE] at H
    exact H.symm.trans f.val.property⟩
  left_inv f:=by
    apply Subtype.ext
    exact (countSupportEquiv e even).symm_apply_apply f.val
  right_inv f:=by
    apply Subtype.ext
    apply Subtype.ext
    exact Subtype.ext (Finsupp.embDomain_comapDomain f.property)

lemma dimensionSupport_energy (k : B → ℤ) (d : I→ℕ)
    (f : DimensionCounts (fun a=>even (e a)) (fun a=>dim (e a)) d) :
    countEnergy even k (dimensionSupportEquiv e even dim d f).val.val=
      countEnergy (fun a=>even (e a)) (fun a=>k (e a)) f.val :=
  embedCount_sum e even f.val k
end
end ElementaryPositivity.SignedMultiplicity

end

end OAI
