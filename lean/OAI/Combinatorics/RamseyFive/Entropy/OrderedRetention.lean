import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.TreeOrder
import OAI.Combinatorics.RamseyFive.Geometry.FiniteTreeFailure

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree FiniteEntropy
open scoped Classical BigOperators
variable {I : Type*} [Preorder I]

lemma directed_failure_budget (tree : BinaryTree I) (hord : Ordered tree)
    (ρ : I → I → ℝ) (ε C Q E : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hρ : ∀ i j,i ≤ j → ρ i j ≤ ε) (j : Address tree) :
    pathSum tree (fun k=>10*pathBudget (fun i=>C*ρ (label tree k) i) (fun _=>0) tree k+
      10*pathBudget (fun _=>0) (fun i=>C*ρ i (label tree k)) tree k+
      Q*ρ (label tree k) (label tree k)+E) j  ≤
      tree.height*(20*tree.height*C*ε+Q*ε+E) := by
  have hcap : ∀ k : Address tree,
      10*pathBudget (fun i=>C*ρ (label tree k) i) (fun _=>0) tree k+
      10*pathBudget (fun _=>0) (fun i=>C*ρ i (label tree k)) tree k+
      Q*ρ (label tree k) (label tree k)+E  ≤  20*tree.height*C*ε+Q*ε+E := by
    intro k
    have hh:=mul_nonneg hC hε
    have h1:=ordered_pathBudget_bound tree hord k (fun i=>C*ρ (label tree k) i)
      (fun _=>0) (C*ε) hh
      (fun i hi=>mul_le_mul_of_nonneg_left (hρ _ _ hi) hC) (fun _ _=>hh)
    have h2:=ordered_pathBudget_bound tree hord k (fun _=>0)
      (fun i=>C*ρ i (label tree k)) (C*ε) hh
      (fun _ _=>hh) (fun i hi=>mul_le_mul_of_nonneg_left (hρ _ _ hi) hC)
    have h3:=mul_le_mul_of_nonneg_left (hρ (label tree k) (label tree k) le_rfl) hQ
    linarith
  exact (pathSum_mono tree _ _ hcap j).trans (pathSum_const_le_height tree j _ (by positivity))

lemma directed_target_budget (tree : BinaryTree I) (hord : Ordered tree)
    (gA gB : I → ℝ) (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (j : Address tree)
    (hA : ∀ i,label tree j ≤ i → gA i ≤ ε) (hB : ∀ i,i ≤ label tree j → gB i ≤ ε) :
    10*pathBudget (fun i=>C*gA i) (fun _=>0) tree j+
      10*pathBudget (fun _=>0) (fun i=>C*gB i) tree j+
      C*gA (label tree j)+C*gB (label tree j) ≤ (20*tree.height+2)*C*ε := by
  have hh:=mul_nonneg hC hε
  have h1:=ordered_pathBudget_bound tree hord j (fun i=>C*gA i) (fun _=>0) (C*ε) hh
    (fun i hi=>mul_le_mul_of_nonneg_left (hA i hi) hC) (fun _ _=>hh)
  have h2:=ordered_pathBudget_bound tree hord j (fun _=>0) (fun i=>C*gB i) (C*ε) hh
    (fun _ _=>hh) (fun i hi=>mul_le_mul_of_nonneg_left (hB i hi) hC)
  have h3:=mul_le_mul_of_nonneg_left (hA _ le_rfl) hC
  have h4:=mul_le_mul_of_nonneg_left (hB _ le_rfl) hC
  linarith
end SharpRamseyFive.TreeCodec

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal Topology
noncomputable section
local instance (priority := high) orderedRetentionPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem eventually_ordered_tree_missing {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3 ≤ Nat.card K) (I : Type) [Fintype I] [DecidableEq I] [Preorder I]
      (A B : I  →  Type) [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
      (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
      (X : ∀ i, A i  →  Finset (ℙ K V)) (Y : ∀ i, B i  →  Finset (ℙ K (Dual K V)))
      (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
      (p : I  →  Law (ℙ K V)) (q : I  →  Law (ℙ K (Dual K V)))
      (F ε : ℝ) (hF : 0 ≤ F) (hε : 0 ≤ ε)
      (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a)  ≤  F*p i a)
      (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b)  ≤  F*q i b)
      (hsparse : ∀ i j,i ≤ j → relationMass Incident (p i) (q j) ≤ ε)
      (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀  →  Range η σ D R  →  (L₀:ℝ)=L η σ D  →
      0 ≤ b  →  b ≤ Cb*D*σ^(6*beta η)  →
      (∀ i a d, (Nat.card K:ℝ)^5*Real.exp (-b) ≤ ((X i a).card:ℝ)*(Y i d).card)  →
      let f := fun C : PivotContext K V =>
        fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V =>
        fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
          (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (tree : BinaryTree I),Ordered tree → ∀ (j : Address tree),
    (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω =>
        orientedPivotSuccessAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree ω (Finset.univ,Finset.univ) j = none)))  ≤
      tree.height*(20*tree.height*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F^2*ε+
        ((Nat.card K:ℝ)/(σ^(-1000*beta η)))*F^2*ε+5*Real.exp (-(Nat.card K:ℝ))) := by
  filter_upwards [eventually_actual_tree_missing hη hη' Cb hCb] with σ hh
  intro D b R L₀ q₀ K V _ _ _ _ _ _ _ _ _ hd hq3 I _ _ _ A B _ _ μ ν X Y hX hY p q F ε hF hε hμ hν hsparse hσ hq hcard hr hL hb hbhi hprod
  dsimp only
  intro tree hord j
  have h:=hh D b R L₀ q₀ K V hd hq3 I A B μ ν X Y hX hY p q F hF hμ hν hσ hq hcard hr hL hb hbhi hprod tree j
  apply h.trans
  have hn:=directed_failure_budget tree hord (fun i j=>relationMass Incident (p i) (q j)) ε
    ((50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F^2)
    (((Nat.card K:ℝ)/(σ^(-1000*beta η)))*F^2)
    (5*Real.exp (-(Nat.card K:ℝ))) hε (by positivity) (by positivity) (by positivity) hsparse j
  simpa only [mul_assoc] using hn
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
