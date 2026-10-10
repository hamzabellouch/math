import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Relabel

namespace OAI

namespace MatchingFPRAS.RationalSource

open MatchingFPRAS Switching Subdivision RealGeometry Hierarchy Enlargement Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

lemma labelCast_level {X : Type*} [Fintype X] {B B' : X → X → ℝ}
    (s : ∀ x y,B x y=B y x)
    (t : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (s' : ∀ x y,B' x y=B' y x)
    (t' : ∀ x y z,x≠y → x≠z → y≠z → min (B' x z) (B' z y)≤B' x y)
    {H H' : ℕ} (hB : B=B') (hH : H=H') (l : Hierarchy.Label B s t H) :
    (labelCast s t s' t' hB hH l).1.val=l.1.val := by
  cases hB;cases hH;rfl

lemma labelCast_edgeLabel {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E]
    {B B' : X → X → ℝ}
    (s : ∀ x y,B x y=B y x)
    (t : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (s' : ∀ x y,B' x y=B' y x)
    (t' : ∀ x y z,x≠y → x≠z → y≠z → min (B' x z) (B' z y)≤B' x y)
    (u v : E → X) {H H' : ℕ} (hB : B=B') (hH : H=H') (e : E) :
    labelCast s t s' t' hB hH (Hierarchy.edgeLabel B s t u v H e)=
      Hierarchy.edgeLabel B' s' t' u v H' e := by
  cases hB;cases hH;rfl

lemma labelsEquiv_level (w : V → V → ℚ) (K : ℕ)
    (l : SourceLabel (fun x y=>(w x y:ℝ)) K) :
    (labelsEquiv w K l).1.val=l.1.val := by
  unfold labelsEquiv
  simp only [Equiv.trans_apply,NumberedHierarchy.labelEquiv_level,labelCast_level]

lemma labelsEquiv_edgeLabel (w : V → V → ℚ) (K : ℕ) (q : SourceRealEdge V K) :
    labelsEquiv w K (Hierarchy.edgeLabel (sourceRealB (fun x y=>(w x y:ℝ)) K)
      (sourceRealB_comm _ _) (sourceRealB_tri _ _) (realLeft K) (realRight K)
      (sourceLevels (fun x y=>(w x y:ℝ)) K) q)=realLabel w K q := by
  unfold labelsEquiv
  simp only [Equiv.trans_apply,labelCast_edgeLabel,NumberedHierarchy.edgeLabel_equiv,realLabel]

end MatchingFPRAS.RationalSource

end OAI
