import OAI.Combinatorics.ContingencyTables.Transport.FiniteDependentLaw
import OAI.Combinatorics.ContingencyTables.Transport.RejectionLaw

namespace OAI

/-! # Joint laws with a deterministic second coordinate -/

namespace ContingencyTables.FirstSuccess
open scoped BigOperators Classical
open ResidualMixture

variable {X : Type*} {Y : X → Type*} [Fintype X] [∀ x,Fintype (Y x)]

lemma mapLaw_deterministicJoint (p : RationalLaw X) (f : (x : X) → Y x) :
    mapLaw p (fun x => (⟨x,f x⟩ : Sigma Y))=
      dependentJointLaw p (fun x => pointLaw (f x)) := by
  apply RationalLaw.ext
  funext a
  rcases a with ⟨x,y⟩
  change (∑ z,if (⟨z,f z⟩ : Sigma Y)=⟨x,y⟩ then p.mass z else 0)=
    p.mass x*(if y=f x then 1 else 0)
  rw [Finset.sum_eq_single x]
  · by_cases h : f x=y <;> simp [h,eq_comm]
  · intro z _ hz
    have hn : (⟨z,f z⟩ : Sigma Y)≠⟨x,y⟩ := fun h => hz (congrArg Sigma.fst h)
    simp only [hn,ite_false]
  · simp

lemma pointLaw_eq_uniform {A : Type*} [Fintype A] [Subsingleton A] [Nonempty A] (a : A) :
    pointLaw a=uniformLaw (α := A) := by
  let : Unique A := ⟨⟨a⟩,fun x => Subsingleton.elim x a⟩
  apply RationalLaw.ext
  funext x
  simp only [pointLaw,uniformLaw,uniformMass,Subsingleton.elim a x,ite_true,
    Fintype.card_unique,Nat.cast_one,div_one]

end ContingencyTables.FirstSuccess

end OAI
