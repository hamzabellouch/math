import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.OrientedPivotTree
import OAI.Combinatorics.RamseyFive.Geometry.OrientedNodeCaps
import OAI.Combinatorics.RamseyFive.Trees.EncodedTreePotential

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry PivotTree BinaryTree
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def pivotPotential (C : PivotContext K V) : ℝ :=
  potential C.1.card C.2.card ((Nat.card K:ℝ)^5)

theorem orientedPivotTree_potential {ι : Type}
    (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ : ι→Finset (ℙ K V)) (B₀ : ι→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀i,(A₀ i).Nonempty) (hB₀ : ∀i,(B₀ i).Nonempty)
    (c τ P b : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hb : 0≤b)
    (hp : ∀i,(Nat.card K:ℝ)^5*Real.exp (-b)≤((A₀ i).card:ℝ)*(B₀ i).card)
    (tree : BinaryTree ι) (ω : OrientedPivotTreeTape f r tree) (C : PivotContext K V) :
    TreeCodec.cost (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
      (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r)
      (fun _ C _ _=>pivotPotential C) tree ω C
        (orientedPivotTreeEncoded f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c (9/10) τ P (by norm_num) tree ω C)≤
      tree.height*(pivotPotential C+(b+1+2*Real.log (320/c+320))*tree.numNodes) := by
  have hC1 : 1≤320/c+320 := by
    have hh : (0:ℝ)≤320/c := by positivity
    linarith only [hh]
  apply TreeCodec.encoded_potential_le
  · intro C
    exact le_max_left _ _
  · have hh := Real.log_nonneg hC1
    linarith only [hb,hh]
  · intro i C t m hm
    simpa only [pivotPotential,orientedPivotLeft,orientedPivotRight,add_assoc] using
      orientedGuardedNode_split_potential (f C) (r C) σ hσ hq hd (A₀ i) C.1 (B₀ i) C.2
      (hA₀ i) (hB₀ i) c τ P b hc hc9 (hp i) t m hm
end SharpRamseyFive.ProjectiveIncidence

end OAI
