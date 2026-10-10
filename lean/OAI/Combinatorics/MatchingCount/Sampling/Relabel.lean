import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.LabelOrder

namespace OAI

namespace MatchingFPRAS.Transport

open Finset

variable {V L J : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]
    [Fintype J] [DecidableEq J]

variable {b : V → Finset L} {c : V → Finset J}

def relabelEdge (e : L ≃ J) (h : ∀ v,(b v).image e=c v) (a : BagEdge b) : BagEdge c :=
  ⟨⟨(a.val.val.1,e a.val.val.2),a.val.property⟩,by
    intro v hv
    change e a.val.val.2∈c v
    rw [←h v]
    exact mem_image.mpr ⟨a.val.val.2,a.property v hv,rfl⟩⟩

omit [Fintype V] [DecidableEq V] [Fintype L] [Fintype J] in
lemma image_symm_bags (e : L ≃ J) (h : ∀ v,(b v).image e=c v) (v : V) :
    (c v).image e.symm=b v := by
  rw [←h v,image_image]
  simp

def relabelEdgeEquiv (e : L ≃ J) (h : ∀ v,(b v).image e=c v) : BagEdge b ≃ BagEdge c where
  toFun:=relabelEdge e h
  invFun:=relabelEdge e.symm (image_symm_bags e h)
  left_inv a := by apply Subtype.ext; apply Subtype.ext; simp [relabelEdge]
  right_inv a := by apply Subtype.ext; apply Subtype.ext; simp [relabelEdge]

omit [Fintype V] [DecidableEq V] [Fintype L] [Fintype J] in
lemma relabelEdge_incident (e : L ≃ J) (h : ∀ v,(b v).image e=c v) (a : BagEdge b) (v : V) :
    (relabelEdgeEquiv e h a).Incident v ↔ a.Incident v := Iff.rfl


variable {E F : Type*} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable {inc : E → V → Prop} {j : F → V → Prop}

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype F] in
lemma MatchingOn.image (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    {M : Finset E} {U : Finset V} (hM : MatchingOn inc M U) :
    MatchingOn j (M.image e) U := by
  constructor
  · intro f hf v hv
    obtain ⟨a,ha,rfl⟩:=mem_image.mp hf
    exact hM.1 a ha v ((he a v).mp hv)
  · intro v hv
    obtain ⟨a,⟨ha,hav⟩,hu⟩:=hM.2 v hv
    refine ⟨e a,⟨mem_image.mpr ⟨a,ha,rfl⟩,(he a v).mpr hav⟩,?_⟩
    rintro f ⟨hf,hfv⟩
    obtain ⟨d,hd,rfl⟩:=mem_image.mp hf
    exact congrArg e (hu d ⟨hd,(he d v).mp hfv⟩)

def pmEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v) : PM inc ≃ PM j where
  toFun M:=⟨M.val.image e,M.property.image e he⟩
  invFun M:=⟨M.val.image e.symm,M.property.image e.symm (by intro a v; simpa using (he (e.symm a) v).symm)⟩
  left_inv M:=by apply Subtype.ext; simp [image_image]
  right_inv M:=by apply Subtype.ext; simp [image_image]

omit [DecidableEq V] [Fintype E] [Fintype F] in
lemma matchingWeight_pmEquiv [DecidableEq V] [Fintype E] [Fintype F]
    (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (w : F → ℝ) (M : PM inc) : matchingWeight w (pmEquiv e he M)=matchingWeight (w ∘ e) M := by
  unfold matchingWeight pmEquiv
  exact Finset.prod_image (fun _ _ _ _ h=>e.injective h)

lemma partition_pmEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (w : F → ℝ) : partition (inc:=j) w=partition (inc:=inc) (w ∘ e) := by
  classical
  unfold partition
  symm
  exact Finset.sum_equiv (pmEquiv e he) (by simp) (fun M _=>(matchingWeight_pmEquiv e he w M).symm)

lemma gibbs_pmEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (w : F → ℝ) (M : PM inc) : gibbs w (pmEquiv e he M)=gibbs (w ∘ e) M := by
  unfold gibbs
  rw [matchingWeight_pmEquiv,partition_pmEquiv e he w]


end MatchingFPRAS.Transport

namespace MatchingFPRAS.RationalSource

open MatchingFPRAS Switching Subdivision RealGeometry Hierarchy Enlargement Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance {X : Type*} [Fintype X] (B : X → X → ℝ)
    (s : ∀ x y,B x y=B y x)
    (t : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y) (H : ℕ) :
    DecidableEq (Hierarchy.Label B s t H) := Classical.decEq _

noncomputable def labelCast {X : Type*} [Fintype X] {B B' : X → X → ℝ}
    (s : ∀ x y,B x y=B y x)
    (t : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (s' : ∀ x y,B' x y=B' y x)
    (t' : ∀ x y z,x≠y → x≠z → y≠z → min (B' x z) (B' z y)≤B' x y)
    {H H' : ℕ} (hB : B=B') (hH : H=H') :
    Hierarchy.Label B s t H ≃ Hierarchy.Label B' s' t' H' :=
  Equiv.cast (by cases hB;cases hH;rfl)

lemma labelCast_bags {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E]
    {B B' : X → X → ℝ}
    (s : ∀ x y,B x y=B y x)
    (t : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (s' : ∀ x y,B' x y=B' y x)
    (t' : ∀ x y z,x≠y → x≠z → y≠z → min (B' x z) (B' z y)≤B' x y)
    (u v : E → X) {H H' : ℕ} (hB : B=B') (hH : H=H') (x : X) :
    (memberships B s t u v H x).image (labelCast s t s' t' hB hH)=
      memberships B' s' t' u v H' x := by
  classical
  cases hB;cases hH
  simp [labelCast]

noncomputable def labelsEquiv (w : V → V → ℚ) (K : ℕ) :
    SourceLabel (fun x y=>(w x y:ℝ)) K ≃ Label w K :=
  (labelCast (sourceRealB_comm _ _) (sourceRealB_tri _ _)
    (NumberedHierarchy.symmetric (realB w K) (realB_symm w K))
    (NumberedHierarchy.triangular (realB w K) (realB_tri w K))
    (by funext x y;exact (realB_cast w K x y).symm) (levels_eq w K).symm).trans
      (NumberedHierarchy.labelEquiv (realB w K) (realB_symm w K) (realB_tri w K) (levels w K))

lemma source_bags_equiv (w : V → V → ℚ) (K : ℕ) (x : SourceVertex V K) :
    (sourceBags (fun a b=>(w a b:ℝ)) K x).image (labelsEquiv w K)=bags w K x := by
  change image ((NumberedHierarchy.labelEquiv _ _ _ _) ∘ _ ) _=_
  rw [←image_image,sourceBags,labelCast_bags]
  exact NumberedHierarchy.bags_equiv (realB w K) (realB_symm w K) (realB_tri w K)
    (realLeft K) (realRight K) (levels w K) x

end MatchingFPRAS.RationalSource

end OAI
