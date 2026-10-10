import OAI.Combinatorics.SquareDifference.LocalizedPair

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma tensorGood_density_square [Fintype TupleVertex] [DecidableEq TupleVertex]
    {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]
    (hp : ∀j,tupleMassThreshold≤(p j:ℝ)) (k : ℕ)
    (z : TupleVertex → ResidueSpace p)
    (hz : lawDensity (tensorLaw (fun j => tupleGoodLaw (p:=p j))) z≠0) :
    ∀j,z (cycleVertex (k+1)) j-z (cycleVertex k) j≠0 ∧
      IsSquare (z (cycleVertex (k+1)) j-z (cycleVertex k) j) := by
  classical
  let P : ResidueSpace p × ResidueSpace p → Prop := fun xy =>
    ∀j,xy.2 j-xy.1 j≠0 ∧ IsSquare (xy.2 j-xy.1 j)
  have hprob : tensorLaw (fun j => tupleGoodLaw (p:=p j))
      (fun z => if P (z (cycleVertex k),z (cycleVertex (k+1))) then 0 else 1)=0 := by
    rw [tensorGood_pair p hp k (fun x y => if P (x,y) then 0 else 1)]
    have hp' (w : ∀j,(ZMod (p j))ˣ) (x : ResidueSpace p) :
        P (x,fun j => x j+(w j:ZMod (p j))^2) := by
      intro j
      dsimp only
      rw [add_sub_cancel_left]
      exact ⟨pow_ne_zero _ (Units.ne_zero _),⟨(w j:ZMod (p j)),by ring⟩⟩
    simp only [hp',ite_true,Fintype.expect_const]
  exact positiveLaw_density_pair_support _
    (tensorLaw_nonneg _ (fun _ => tupleGoodLaw_nonneg))
    (fun z => (z (cycleVertex k),z (cycleVertex (k+1)))) P hprob z hz

end SquareDifference

end

end OAI
