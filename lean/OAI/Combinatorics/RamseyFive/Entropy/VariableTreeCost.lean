import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OrientedTreeCost
import OAI.Combinatorics.RamseyFive.Geometry.OrientedTreeDomains

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section

theorem eventually_variable_tree_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (w : ℕ) (m : Fin (w+1))
      (A₀ : Fin (m.val+1)→Finset (ℙ K V)) (B₀ : Fin (m.val+1)→Finset (ℙ K (Dual K V)))
      (hA₀ : ∀i,(A₀ i).Nonempty) (hB₀ : ∀i,(B₀ i).Nonempty)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      (∀i,(Nat.card K:ℝ)^5*Real.exp (-b)≤((A₀ i).card:ℝ)*(B₀ i).card) →
      let f := fun C : PivotContext K V =>
        fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V =>
        fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
          (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      let X := nodeChargeConstant*(Nat.card K:ℝ)*(P η σ D R)
      ∀ (t : VariableTreeTape f r w) (C : PivotContext K V),
      variableTreeCost f r t C
        (variableTreeEncoded f r t C m σ hσ hq hd.le A₀ B₀ hA₀ hB₀
          (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num))≤
      Real.log (w+1)+
      (X*(finiteBalanced m.val).height*
        (pivotPotential C+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*m.val)+
        (Real.log 2+X*(b+1+P η σ D R))*m.val)+
        (2*(m.val:ℝ)+1)*Real.log 2 := by
  filter_upwards [eventually_oriented_tree_cost hη hη' Cb hCb] with σ hh
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ _ hd w m A₀ B₀ hA₀ hB₀ hσ hq hcard hr hL hb hbhi hp
  dsimp only
  intro t C
  have h:=hh D b R L₀ q K V hd (Fin (m.val+1)) A₀ B₀ hA₀ hB₀ hσ hq hcard hr hL
    hb hbhi hp (finiteBalanced m.val) (t m) C
  let f := fun U : PivotContext K V=>fourFinitePredictor hd σ U.1 U.2
    (P η σ D R) (σ^(-800*beta η)) R L₀
  let r := fun U : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
    (by simpa using hd) σ U.2 (U.1.map bidualPoint.toEmbedding)
      (P η σ D R) (σ^(-800*beta η)) R L₀
  have hs := TreeCodec.slotCost_le_original
    (fun _ : Fin (m.val+1)=>OrientedPivotTape f r)
    (fun _ : Fin (m.val+1)=>OrientedPivotMessage f r)
    (fun _ : Fin (m.val+1)=>orientedPivotLeft f r)
    (fun _ : Fin (m.val+1)=>orientedPivotRight f r)
    (fun _ U t m=>orientedNodeCost (f U) (r U) U.1 U.2
      (1000*(Nat.card K)^2) (Nat.card K) t m)
    (finiteBalanced m.val) (t m) C
    (orientedPivotTreeEncoded f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀
      (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num)
      (finiteBalanced m.val) (t m) C)
  have hh' := hs.trans (add_le_add h le_rfl)
  simp only [finiteBalanced_nodes] at hh'
  unfold variableTreeCost variableTreeEncoded
  dsimp only
  simpa only [orientedPivotSlotCost, f, r, add_assoc] using add_le_add_right hh' (Real.log (w+1))
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
