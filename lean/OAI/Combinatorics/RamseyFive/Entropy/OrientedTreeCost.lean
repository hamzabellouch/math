import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.MessageCounting
import OAI.Combinatorics.RamseyFive.Geometry.OrientedTreePotential
import OAI.Combinatorics.RamseyFive.Entropy.GuardedNodeCost

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry PivotTree BinaryTree Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

noncomputable def nodeChargeConstant : ℝ :=
  32120+21*(12-Real.log ((9:ℝ)/100000)-Real.log ((9:ℝ)/10))
lemma nodeChargeConstant_nonneg : 0≤nodeChargeConstant := by
  have h1 : Real.log ((9:ℝ)/100000)≤0 := Real.log_nonpos (by norm_num) (by norm_num)
  have h2 : Real.log ((9:ℝ)/10)≤0 := Real.log_nonpos (by norm_num) (by norm_num)
  unfold nodeChargeConstant
  linarith only [h1,h2]

theorem eventually_oriented_tree_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (ι : Type)
      (A₀ : ι→Finset (ℙ K V)) (B₀ : ι→Finset (ℙ K (Dual K V)))
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
      ∀ (tree : BinaryTree ι) (ω : OrientedPivotTreeTape f r tree) (C : PivotContext K V),
      TreeCodec.cost (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
        (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r)
        (fun _ C t m=>orientedNodeCost (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t m)
        tree ω C
        (orientedPivotTreeEncoded f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ (9/100000) (9/10)
          (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree ω C)≤
      X*tree.height*(pivotPotential C+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*tree.numNodes)+
        (Real.log 2+X*(b+1+P η σ D R))*tree.numNodes := by
  filter_upwards [eventually_oriented_guarded_node_cost hη hη' Cb hCb] with σ hn
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ _ hd ι A₀ B₀ hA₀ hB₀ hσ hq hcard hr hL hb hbhi hp
  dsimp only
  intro tree ω C
  have hP : 0≤P η σ D R := by
    obtain ⟨_,_,_,_,_,hP,_⟩ := finite_bounds hη hη' hσ hr
    exact (Real.rpow_nonneg (by linarith : 0≤σ) _).trans hP
  have hX : 0≤nodeChargeConstant*(Nat.card K:ℝ)*(P η σ D R) := by
    exact mul_nonneg (mul_nonneg nodeChargeConstant_nonneg (Nat.cast_nonneg _)) hP
  apply TreeCodec.encoded_cost_le
    (φ:=pivotPotential) (B:=b+1+2*Real.log (320/((9:ℝ)/100000)+320))
  · intro C
    exact le_max_left _ _
  · have hl := Real.log_nonneg (show 1≤320/((9:ℝ)/100000)+320 by norm_num)
    linarith only [hb,hl]
  · exact hX
  · exact add_nonneg (Real.log_nonneg (by norm_num))
      (mul_nonneg hX (by linarith only [hb,hP]))
  · intro i U t m hm
    simpa only [pivotPotential,orientedPivotLeft,orientedPivotRight,add_assoc] using
      orientedGuardedNode_split_potential _ _ σ hσ hq hd.le (A₀ i) U.1 (B₀ i) U.2
        (hA₀ i) (hB₀ i) (9/100000) (σ^(-1000*beta η)) (P η σ D R) b
        (by norm_num) (by norm_num) (hp i) t m hm
  · intro i U t m hm
    have hready := (orientedGuardedNode_original_capture _ _ σ hσ hq hd.le (A₀ i) U.1 (B₀ i) U.2
      (hA₀ i) (hB₀ i) (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R)
      (by norm_num) t m hm).1
    have hc := hn D b R L₀ q K V hd (A₀ i) U.1 (B₀ i) U.2 (hA₀ i) (hB₀ i)
      hσ hq hcard hr hL hb hbhi hready (hp i) t m hm
    have hg := ready_log_deficits (A₀ i) U.1 (B₀ i) U.2 (hA₀ i) (hB₀ i) _ b hready (hp i)
    have hm' := mul_le_mul_of_nonneg_left (add_le_add_right hg (P η σ D R)) hX
    change _≤_ * pivotPotential U+_
    dsimp only [pivotPotential,nodeChargeConstant] at hc hm' ⊢
    nlinarith only [hc,hm']
end

open Module FiniteEntropy ReverseCap ScoreGeometry PivotTree BinaryTree Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology BigOperators

theorem eventually_actual_context_entropy {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (ι J : Type) [Fintype J] (p : Law J)
      (A₀ : J→ι→Finset (ℙ K V)) (B₀ : J→ι→Finset (ℙ K (Dual K V)))
      (hA₀ : ∀j i,(A₀ j i).Nonempty) (hB₀ : ∀j i,(B₀ j i).Nonempty)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q → Range η σ D R → (L₀:ℝ)=L η σ D →
      0≤b → b≤Cb*D*σ^(6*beta η) →
      (∀j i,(Nat.card K:ℝ)^5*Real.exp (-b)≤((A₀ j i).card:ℝ)*(B₀ j i).card) →
      let f := fun C : PivotContext K V =>
        fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V =>
        fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
          (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      let X := nodeChargeConstant*(Nat.card K:ℝ)*(P η σ D R)
      ∀ (tree : BinaryTree ι) (ω : OrientedPivotTreeTape f r tree) (C : PivotContext K V),
      entropy (map p (fun j=>orientedPivotTreeEncoded f r σ hσ hq hd.le
        (A₀ j) (B₀ j) (hA₀ j) (hB₀ j) (9/100000) (9/10)
          (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree ω C))≤
      X*tree.height*(pivotPotential C+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*tree.numNodes)+
        (Real.log 2+X*(b+1+P η σ D R))*tree.numNodes+
        (2*(tree.numNodes:ℝ)+1)*Real.log 2 := by
  filter_upwards [eventually_oriented_tree_cost hη hη' Cb hCb] with σ hn
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ _ hd ι J _ p A₀ B₀ hA₀ hB₀ hσ hq hcard hr hL hb hbhi hp
  dsimp only
  intro tree ω C
  let f := fun U : PivotContext K V=>fourFinitePredictor hd σ U.1 U.2
    (P η σ D R) (σ^(-800*beta η)) R L₀
  let r := fun U : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
    (by simpa using hd) σ U.2 (U.1.map bidualPoint.toEmbedding)
      (P η σ D R) (σ^(-800*beta η)) R L₀
  have hw := fourPivotTree_weight (ι:=ι) hd σ (P η σ D R) (σ^(-800*beta η)) R L₀ tree ω C
  apply MessageWeights.entropy_map_le_bound p _ (orientedPivotSlotCost f r tree ω C) hw
  intro j
  have hc := hn D b R L₀ q K V hd ι (A₀ j) (B₀ j) (hA₀ j) (hB₀ j)
    hσ hq hcard hr hL hb hbhi (hp j) tree ω C
  have hs := TreeCodec.slotCost_le_original
    (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
    (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r)
    (fun _ U t m=>orientedNodeCost (f U) (r U) U.1 U.2 (1000*(Nat.card K)^2) (Nat.card K) t m)
    tree ω C (orientedPivotTreeEncoded f r σ hσ hq hd.le (A₀ j) (B₀ j) (hA₀ j) (hB₀ j)
      (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree ω C)
  exact hs.trans (add_le_add hc le_rfl)

end SharpRamseyFive.ProjectiveIncidence

end OAI
