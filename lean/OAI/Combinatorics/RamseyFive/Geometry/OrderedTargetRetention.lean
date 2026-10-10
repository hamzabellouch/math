import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.TargetRetention
import OAI.Combinatorics.RamseyFive.Entropy.OrderedRetention

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal Topology
noncomputable section
local instance (priority := high) orderedTargetPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {K V I Ω : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Fintype I] [DecidableEq I] [Fintype Ω]
  {A B : I → Type} [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]

def orientedTargetFailure
    (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V ≤ 5)
    (μ : ∀ i,Law (A i)) (ν : ∀ i,Law (B i))
    (X : ∀ i,A i → Finset (ℙ K V)) (Y : ∀ i,B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a,(X i a).Nonempty) (hY : ∀ i b,(Y i b).Nonempty)
    (γ : Law Ω) (a : Ω → ℙ K V) (b : Ω → ℙ K (Dual K V))
    (c δ τ P : ℝ) (hδ : 0<δ) (tree : BinaryTree I) (j : Address tree) : ℝ :=
  eventMass (adaptiveLaw γ (fun _=>adaptiveLaw (originalLevelLaw μ ν)
    (fun _=>orientedPivotTreeLaw f r tree))) (Finset.univ.filter fun z=>
      ¬TargetCovered
        (orientedPivotContextAt f r σ hσ hq hd (fun i=>X i (z.2.1.1 i))
          (fun i=>Y i (z.2.1.2 i)) (fun i=>hX i _) (fun i=>hY i _)
          c δ τ P hδ tree z.2.2 (Finset.univ,Finset.univ) j)
        (orientedPivotCapsAt f r σ hσ hq hd (fun i=>X i (z.2.1.1 i))
          (fun i=>Y i (z.2.1.2 i)) (fun i=>hX i _) (fun i=>hY i _)
          c δ τ P hδ tree z.2.2 (Finset.univ,Finset.univ) j)
        (a z.1) (b z.1))

theorem eventually_ordered_target_retention {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3 ≤ Nat.card K) (I : Type) [Fintype I] [DecidableEq I] [Preorder I]
      (A B : I → Type) [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]
      (μ : ∀ i,Law (A i)) (ν : ∀ i,Law (B i))
      (X : ∀ i,A i → Finset (ℙ K V)) (Y : ∀ i,B i → Finset (ℙ K (Dual K V)))
      (hX : ∀ i a,(X i a).Nonempty) (hY : ∀ i b,(Y i b).Nonempty)
      (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
      (F ε : ℝ) (hF : 0 ≤ F) (hε : 0 ≤ ε)
      (hμ : ∀ i a,(∑ s,μ i s*uniformWeight (X i s) a) ≤ F*p i a)
      (hν : ∀ i b,(∑ t,ν i t*uniformWeight (Y i t) b) ≤ F*q i b)
      (hsparse : ∀ i j,i ≤ j → relationMass Incident (p i) (q j) ≤ ε)
      (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀ → Range η σ D R → (L₀:ℝ)=L η σ D →
      0 ≤ b → b ≤ Cb*D*σ^(6*beta η) →
      (∀ i a d,(Nat.card K:ℝ)^5*Real.exp (-b) ≤ ((X i a).card:ℝ)*(Y i d).card) →
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (tree : BinaryTree I),Ordered tree → ∀ (j : Address tree),
      ∀ (Ω : Type) [Fintype Ω] (γ : Law Ω) (a : Ω → ℙ K V) (b₀ : Ω → ℙ K (Dual K V))
        (goodA : ℙ K V → Prop) (goodB : ℙ K (Dual K V) → Prop) (ε₀ : ℝ),0 ≤ ε₀ →
        (∀ i,label tree j ≤ i → relationMass Incident (fun x=>if goodA x then map γ a x else 0) (q i) ≤ ε₀) →
        (∀ i,i ≤ label tree j → relationMass Incident (p i) (fun y=>if goodB y then map γ b₀ y else 0) ≤ ε₀) →
      orientedTargetFailure f r σ hσ hq hd.le μ ν X Y hX hY γ a b₀
        (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree j ≤
      eventMass γ (Finset.univ.filter fun x=>¬goodA (a x))+
      eventMass γ (Finset.univ.filter fun x=>¬goodB (b₀ x))+
      tree.height*(20*tree.height*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F^2*ε+
        ((Nat.card K:ℝ)/(σ^(-1000*beta η)))*F^2*ε+5*Real.exp (-(Nat.card K:ℝ)))+
      (20*tree.height+2)*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F*ε₀ := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-1000*beta η) ≤ ((9/100000:ℝ)*(9/10)^2)/1000 := by
    have hp : 0<1000*beta η := mul_pos (by norm_num) (beta_pos hη)
    exact ((tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<((9/100000:ℝ)*(9/10)^2)/1000)).mono
        (fun σ h=>by simpa only [neg_mul] using h.le)
  filter_upwards [eventually_ordered_tree_missing hη hη' Cb hCb,ht] with σ hh ht
  intro D b R L₀ q₀ K V _ _ _ _ _ _ _ _ _ hd hq3 I _ _ _ A B _ _ μ ν X Y hX hY p q F ε hF hε hμ hν hsparse hσ hq hcard hr hL hb hbhi hprod
  dsimp only
  intro tree hord j Ω _ γ a b₀ goodA goodB ε₀ hε₀ hA hB
  let f:=fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
    (P η σ D R) (σ^(-800*beta η)) R L₀
  let r:=fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
    (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
    (P η σ D R) (σ^(-800*beta η)) R L₀
  have hn:=hh D b R L₀ q₀ K V hd hq3 I A B μ ν X Y hX hY p q F ε hF hε hμ hν hsparse
    hσ hq hcard hr hL hb hbhi hprod tree hord j
  have hτ : 1000*σ^(-1000*beta η) ≤ (9/100000:ℝ)*(9/10)^2 := by linarith only [ht]
  have htarg:=oriented_actual_target_loss f r σ hσ hq hd hq3 μ ν X Y hX hY p q F hμ hν
    γ a b₀ goodA goodB (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R)
    (by norm_num) (by norm_num) (by norm_num) hτ tree j
  have hbudget:=directed_target_budget tree hord
    (fun i=>relationMass Incident (fun x=>if goodA x then map γ a x else 0) (q i))
    (fun i=>relationMass Incident (p i) (fun y=>if goodB y then map γ b₀ y else 0))
    ε₀ ((50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F) hε₀ (by positivity) j hA hB
  dsimp only at htarg
  change orientedTargetFailure f r σ hσ hq hd.le μ ν X Y hX hY γ a b₀ _ _ _ _ _ tree j ≤ _ at htarg
  change orientedTargetFailure f r σ hσ hq hd.le μ ν X Y hX hY γ a b₀ _ _ _ _ _ tree j ≤ _
  calc
    _  ≤  _ := htarg
    _  ≤  _ := by
      dsimp only [f,r] at *
      nlinarith only [hn,hbudget]
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
