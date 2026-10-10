import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OrientedTreeCost

namespace OAI

namespace SharpRamseyFive.MessageWeights
open FiniteEntropy
open scoped Classical BigOperators
universe u v
variable {A : Type u} [Fintype A]

def CountedMessage (n : A→ℕ) (T : ℕ) := (a : A) × (Fin (n a)→Fin (T+1))
noncomputable instance (n : A→ℕ) (T : ℕ) : Fintype (CountedMessage n T) :=
  inferInstanceAs (Fintype ((a : A) × (Fin (n a)→Fin (T+1))))
noncomputable def countedCost (c : A→ℝ) (n : A→ℕ) (T : ℕ)
    (m : CountedMessage n T) : ℝ := c m.1+(n m.1:ℝ)*Real.log (T+1)
lemma count_slots_weight (n T : ℕ) :
    (∑_x : Fin n→Fin (T+1),Real.exp (-((n:ℝ)*Real.log (T+1))))≤1 := by
  have h := log_card_weight (Fin n→Fin (T+1))
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_add,
    Nat.cast_one,Real.log_pow] using h
lemma counted_weight (c : A→ℝ) (hc : (∑a,Real.exp (-c a))≤1)
    (n : A→ℕ) (T : ℕ) :
    (∑m : CountedMessage n T,Real.exp (-countedCost c n T m))≤1 := by
  exact sigma_weight_le A (fun a=>Fin (n a)→Fin (T+1)) c
    (fun a _=>(n a:ℝ)*Real.log (T+1)) hc (fun a=>count_slots_weight (n a) T)

lemma counted_entropy_bound {J : Type v} [Fintype J] (p : Law J)
    (c : A→ℝ) (hc : (∑a,Real.exp (-c a))≤1) (n : A→ℕ) (T N : ℕ)
    (e : J → CountedMessage n T) (B : ℝ)
    (hb : ∀j,c (e j).1≤B) (hn : ∀j,n (e j).1≤N) :
    entropy (map p e)≤B+(N:ℝ)*Real.log (T+1) := by
  apply entropy_map_le_bound p e (countedCost c n T) (counted_weight c hc n T)
  intro j
  apply add_le_add (hb j)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn j)
    (Real.log_nonneg (by have h := Nat.cast_nonneg (α:=ℝ) T; linarith))
end SharpRamseyFive.MessageWeights

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry PivotTree BinaryTree Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology BigOperators

theorem eventually_actual_counted_context_entropy {η : ℝ} (hη : 0<η) (hη' : η<1/10)
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
      let e := fun j=>orientedPivotTreeEncoded f r σ hσ hq hd.le
        (A₀ j) (B₀ j) (hA₀ j) (hB₀ j) (9/100000) (9/10)
          (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree ω C
      ∀ (T : ℕ) (counts : ∀j,Fin ((orientedPivotTreeRetained f r tree ω C (e j)).numNodes) → Fin (T+1)),
      entropy (map p (fun j=>(⟨e j,counts j⟩ :
        MessageWeights.CountedMessage (fun m=>(orientedPivotTreeRetained f r tree ω C m).numNodes) T)))≤
      X*tree.height*(pivotPotential C+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*tree.numNodes)+
        (Real.log 2+X*(b+1+P η σ D R))*tree.numNodes+
        (2*(tree.numNodes:ℝ)+1)*Real.log 2+(tree.numNodes:ℝ)*Real.log (T+1) := by
  filter_upwards [eventually_oriented_tree_cost hη hη' Cb hCb] with σ hn
  intro D b R L₀ q K V _ _ _ _ _ _ _ _ _ hd ι J _ p A₀ B₀ hA₀ hB₀ hσ hq hcard hr hL hb hbhi hp
  dsimp only
  intro tree ω C T counts
  let f := fun U : PivotContext K V=>fourFinitePredictor hd σ U.1 U.2
    (P η σ D R) (σ^(-800*beta η)) R L₀
  let r := fun U : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
    (by simpa using hd) σ U.2 (U.1.map bidualPoint.toEmbedding)
      (P η σ D R) (σ^(-800*beta η)) R L₀
  have hw := fourPivotTree_weight (ι:=ι) hd σ (P η σ D R) (σ^(-800*beta η)) R L₀ tree ω C
  apply MessageWeights.counted_entropy_bound p (orientedPivotSlotCost f r tree ω C) hw
    (fun m=>(orientedPivotTreeRetained f r tree ω C m).numNodes) T tree.numNodes
  · intro j
    have hc := hn D b R L₀ q K V hd ι (A₀ j) (B₀ j) (hA₀ j) (hB₀ j)
      hσ hq hcard hr hL hb hbhi (hp j) tree ω C
    have hs := TreeCodec.slotCost_le_original
      (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
      (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r)
      (fun _ U t m=>orientedNodeCost (f U) (r U) U.1 U.2 (1000*(Nat.card K)^2) (Nat.card K) t m)
      tree ω C (orientedPivotTreeEncoded f r σ hσ hq hd.le (A₀ j) (B₀ j) (hA₀ j) (hB₀ j)
        (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree ω C)
    exact hs.trans (add_le_add hc le_rfl)
  · intro j
    exact orientedPivotTree_retained_nodes f r tree ω C _
end SharpRamseyFive.ProjectiveIncidence

end OAI
