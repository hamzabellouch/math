import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Related2

namespace OAI

namespace MatchingFPRAS.NumberedHierarchy

open Finset MatchingFPRAS.UnitRefresh

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (B : V → V → ℚ) (hsym : ∀ x y,B x y=B y x)

variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)

@[instance_reducible] def labelOrder (H : ℕ) : LinearOrder (Label B H) :=
  LinearOrder.lift' (fun l : Label B H=>toLex (l.1,l.2.val)) (by
    intro a b h
    have h' := toLex.injective h
    obtain ⟨k,a⟩:=a
    obtain ⟨j,b⟩:=b
    have hk : k=j:=congrArg Prod.fst h'
    cases hk
    exact congrArg (Sigma.mk k) (Subtype.ext (congrArg Prod.snd h')))

attribute [local instance] labelOrder

noncomputable def abstractTree (H : ℕ) : SimpleGraph (Label B H) :=
  (Hierarchy.tree (fun x y=>(B x y:ℝ)) (symmetric B hsym) (triangular B htri)).comap
    (labelEquiv B hsym htri H).symm

lemma abstractTree_acyclic (H : ℕ) : (abstractTree B hsym htri H).IsAcyclic := by
  exact SimpleGraph.IsAcyclic.of_comap (labelEquiv B hsym htri H).symm.toEmbedding
    (Hierarchy.tree_acyclic _ _ _ _)

lemma abstractTree_adj (H : ℕ) (a b : Label B H) :
    (abstractTree B hsym htri H).Adj a b ↔
      parent B hsym htri b=some a ∨ parent B hsym htri a=some b := by
  change (Hierarchy.Parent _ _ _ ((labelEquiv B hsym htri H).symm a) ((labelEquiv B hsym htri H).symm b) ∨
    Hierarchy.Parent _ _ _ ((labelEquiv B hsym htri H).symm b) ((labelEquiv B hsym htri H).symm a)) ↔ _
  have ha:=parent_equiv_iff B hsym htri ((labelEquiv B hsym htri H).symm b) ((labelEquiv B hsym htri H).symm a)
  have hb:=parent_equiv_iff B hsym htri ((labelEquiv B hsym htri H).symm a) ((labelEquiv B hsym htri H).symm b)
  simpa only [Equiv.apply_symm_apply] using or_congr ha.symm hb.symm

def tree (H : ℕ) : SimpleGraph (Label B H) where
  Adj a b := parent B hsym htri b=some a ∨ parent B hsym htri a=some b
  symm := ⟨fun _ _ h=>Or.symm h⟩
  loopless := ⟨by intro a h; rcases h with h|h <;> exact (Nat.lt_irrefl _ (parent_rank B hsym htri h))⟩

instance treeDec (H : ℕ) : DecidableRel (tree B hsym htri H).Adj := by
  intro a b
  exact inferInstanceAs (Decidable (parent B hsym htri b=some a ∨ parent B hsym htri a=some b))

lemma tree_adj (H : ℕ) (a b : Label B H) :
    (tree B hsym htri H).Adj a b ↔
      parent B hsym htri b=some a ∨ parent B hsym htri a=some b := Iff.rfl

lemma tree_eq (H : ℕ) : tree B hsym htri H=abstractTree B hsym htri H := by
  ext a b
  exact (abstractTree_adj B hsym htri H a b).symm

lemma tree_acyclic (H : ℕ) : (tree B hsym htri H).IsAcyclic := by
  rw [tree_eq]
  exact abstractTree_acyclic B hsym htri H

variable {E : Type*} [Fintype E] [DecidableEq E] (left right : E → V)

lemma bags_nonempty (H : ℕ) (hx : ∀ x,∃ e,x=left e ∨ x=right e) (x : V) :
    (bags B hsym htri left right H x).Nonempty := by
  obtain ⟨e,he⟩:=hx x
  exact ⟨_,(mem_bags _ _ _ _ _ _ _ _).mpr ⟨e,he,rfl⟩⟩

lemma bags_adjacent (H : ℕ) (hfloor : ∀ x y,1≤B x y)
    (hmax : ∀ e,B (left e) (right e)<(2:ℚ)^(H+1))
    (hnear : ∀ x e f,Hierarchy.Incident left right e x → Hierarchy.Incident left right f x →
      B (left e) (right e)≤2*B (left f) (right f)) :
    ∀ x a,a∈bags B hsym htri left right H x → ∀ b∈bags B hsym htri left right H x,
      a=b ∨ (tree B hsym htri H).Adj a b := by
  intro x a ha b hb
  rw [←bags_equiv] at ha hb
  obtain ⟨a',ha',rfl⟩:=mem_image.mp ha
  obtain ⟨b',hb',rfl⟩:=mem_image.mp hb
  have hf : ∀ x y,1≤(B x y:ℝ) := by intro x y; exact_mod_cast hfloor x y
  have hm : ∀ e,(B (left e) (right e):ℝ)<(2:ℝ)^(H+1) := by
    intro e; exact_mod_cast hmax e
  have hn : ∀ x e f,Hierarchy.Incident left right e x → Hierarchy.Incident left right f x →
      (B (left e) (right e):ℝ)≤2*(B (left f) (right f):ℝ) := by
    intro x e f he hf; exact_mod_cast hnear x e f he hf
  have h:=Hierarchy.memberships_tree_bags (fun x y=>(B x y:ℝ)) (symmetric B hsym)
    (triangular B htri) hf left right H hm hn x a' b' ha' hb'
  rcases h with h|h
  · exact Or.inl (congrArg _ h)
  · exact Or.inr (by simpa only [tree_eq,abstractTree,SimpleGraph.comap_adj,Equiv.symm_apply_apply] using h)

lemma bags_ranked (H : ℕ) (hfloor : ∀ x y,1≤B x y)
    (hmax : ∀ e,B (left e) (right e)<(2:ℚ)^(H+1))
    (hnear : ∀ x e f,Hierarchy.Incident left right e x → Hierarchy.Incident left right f x →
      B (left e) (right e)≤2*B (left f) (right f)) :
    RankedBags (bags B hsym htri left right H) (fun l=>l.1.val) (parent B hsym htri) := by
  intro x a ha b hb hab
  rcases bags_adjacent B hsym htri left right H hfloor hmax hnear x a ha b hb with h|h
  · exact (hab h).elim
  · rcases (tree_adj B hsym htri H a b).mp h with h|h
    · exact Or.inl ⟨parent_rank B hsym htri h,h⟩
    · exact Or.inr ⟨parent_rank B hsym htri h,h⟩

omit [Fintype E] [DecidableEq E] in
lemma height_step (H : ℕ) (a b : Label B H) (h : (tree B hsym htri H).Adj a b) :
    (2:ℝ)^a.1.val ≤ 2*(2:ℝ)^b.1.val := by
  rcases (tree_adj B hsym htri H a b).mp h with h|h
  · have hh:=((parent_iff B hsym htri b a).mp h).1
    rw [←hh,pow_succ]
    have hp : 0≤(2:ℝ)^a.1.val := by positivity
    nlinarith
  · have hh:=((parent_iff B hsym htri a b).mp h).1
    rw [←hh,pow_succ]
    ring_nf
    exact le_rfl

end MatchingFPRAS.NumberedHierarchy

namespace MatchingFPRAS.RationalSource

open Finset MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec

def parent (w : V → V → ℚ) (K : ℕ) : Label w K → Option (Label w K) :=
  NumberedHierarchy.parent (realB w K) (realB_symm w K) (realB_tri w K)

def tree (w : V → V → ℚ) (K : ℕ) : SimpleGraph (Label w K) :=
  NumberedHierarchy.tree (realB w K) (realB_symm w K) (realB_tri w K) (levels w K)

lemma tree_acyclic (w : V → V → ℚ) (K : ℕ) : (tree w K).IsAcyclic :=
  NumberedHierarchy.tree_acyclic _ _ _ _

lemma parent_rank (w : V → V → ℚ) (K : ℕ) (l p : Label w K)
    (h : parent w K l=some p) : p.1.val<l.1.val :=
  NumberedHierarchy.parent_rank _ _ _ h

omit [Fintype V] [Nontrivial V] in
lemma raw_cast [Fintype V] [Nontrivial V] (w : V → V → ℚ) (K : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K) :
    ∀ x y,x≠y → edgeActivity (fun x y=>(w x y:ℝ)) x y≤(4:ℝ)^K := by
  intro x y hxy
  have he : ((BottleneckAlgorithm.edge w x y:ℚ):ℝ)=edgeActivity (fun x y=>(w x y:ℝ)) x y := by
    unfold BottleneckAlgorithm.edge edgeActivity
    split_ifs <;> rfl
  simpa only [he,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr (h x y hxy)

lemma realB_floor (w : V → V → ℚ) (K : ℕ) (x y : SourceVertex V K) : 1≤realB w K x y := by
  apply (Rat.cast_le (K:=ℝ)).mp
  simpa only [Rat.cast_one,realB_cast] using sourceRealB_floor (fun x y=>(w x y:ℝ)) K x y

lemma realB_upper (w : V → V → ℚ) (K : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K) (e : SourceRealEdge V K) :
    realB w K (realLeft K e) (realRight K e)<(2:ℚ)^(levels w K+1) := by
  apply (Rat.cast_lt (K:=ℝ)).mp
  simpa only [realB_cast,levels_eq,Rat.cast_pow,Rat.cast_ofNat] using
    (source_strength_le_max (fun x y=>(w x y:ℝ)) K (raw_cast w K h) e).trans_lt
      (maxSourceHeight_lt (fun x y=>(w x y:ℝ)) K (raw_cast w K h))

lemma realB_near (w : V → V → ℚ) (K : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (x : SourceVertex V K) (e f : SourceRealEdge V K)
    (he : Hierarchy.Incident (realLeft K) (realRight K) e x)
    (hf : Hierarchy.Incident (realLeft K) (realRight K) f x) :
    realB w K (realLeft K e) (realRight K e)≤2*realB w K (realLeft K f) (realRight K f) := by
  apply (Rat.cast_le (K:=ℝ)).mp
  simpa only [realB_cast,Rat.cast_mul,Rat.cast_ofNat] using
    source_strength_incident_near (fun x y=>(w x y:ℝ)) K (raw_cast w K h) x e f he hf

lemma bags_adjacent (w : V → V → ℚ) (K : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K) :
    ∀ x a,a∈bags w K x → ∀ b∈bags w K x,a=b ∨ (tree w K).Adj a b :=
  NumberedHierarchy.bags_adjacent _ _ _ _ _ _ (realB_floor w K) (realB_upper w K h) (realB_near w K h)

lemma bags_ranked (w : V → V → ℚ) (K : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K) :
    UnitRefresh.RankedBags (bags w K) (fun l=>l.1.val) (parent w K) :=
  NumberedHierarchy.bags_ranked _ _ _ _ _ _ (realB_floor w K) (realB_upper w K h) (realB_near w K h)

omit [Fintype V] in
lemma incident_exists [Fintype V] (K : ℕ) (x : SourceVertex V K) :
    ∃ e,Hierarchy.Incident (realLeft K) (realRight K) e x := by
  cases x with
  | inl x =>
    obtain ⟨y,hy⟩ := exists_ne x
    rcases lt_or_gt_of_ne hy with h | h
    · let e : LogicalEdge V := ⟨(y,x),h⟩
      refine ⟨(e,Fin.last (4*(2*K+2))),Or.inr ?_⟩
      simp [realRight,atVertex_last,target,e]
    · let e : LogicalEdge V := ⟨(x,y),h⟩
      refine ⟨(e,0),Or.inl ?_⟩
      simp [realLeft,atVertex_zero,source,e]
  | inr q =>
    obtain ⟨e,i⟩ := q
    refine ⟨(e,i.castSucc),Or.inr ?_⟩
    change Sum.inr (e,i)=atVertex source target _ e i.castSucc.succ
    have he : i.castSucc.succ=i.succ.castSucc := Fin.ext rfl
    rw [he,atVertex_internal]

lemma bags_nonempty (w : V → V → ℚ) (K : ℕ) (x : SourceVertex V K) :
    (bags w K x).Nonempty :=
  NumberedHierarchy.bags_nonempty _ _ _ _ _ _ (incident_exists K) x

def realLabel (w : V → V → ℚ) (K : ℕ) (e : SourceRealEdge V K) : Label w K :=
  NumberedHierarchy.edgeLabel (realB w K) (realB_symm w K) (realB_tri w K)
    (realLeft K) (realRight K) (levels w K) e

omit [Nontrivial V] in
lemma real_not_diag [Nontrivial V] (K : ℕ) (e : SourceRealEdge V K) :
    ¬(edge source target (4*(2*K+2)) e.1 e.2).IsDiag := by
  rw [edge,Sym2.mk_isDiag_iff]
  intro he
  have hi := atVertex_injective source target (4*(2*K+2)) e.1 (source_ne_target e.1) he
  have := congrArg Fin.val hi
  simp at this

def coloredReal (w : V → V → ℚ) (K : ℕ) (e : SourceRealEdge V K) : BagEdge (bags w K) :=
  ⟨⟨(edge source target (4*(2*K+2)) e.1 e.2,realLabel w K e),real_not_diag K e⟩,by
    intro x hx
    apply (NumberedHierarchy.mem_bags _ _ _ (realLeft K) (realRight K) (levels w K) x _).mpr
    refine ⟨e,?_,rfl⟩
    simpa [ColoredEdge.Incident,realLeft,realRight,edge] using hx⟩

lemma coloredReal_injective (w : V → V → ℚ) (K : ℕ) : Function.Injective (coloredReal w K) := by
  intro e f h
  apply edge_injective source target (4*(2*K+2)) (by omega)
  exact congrArg (fun q : BagEdge (bags w K)=>q.val.val.1) h

def realPortion (w : V → V → ℚ) (K : ℕ) (e : BagEdge (bags w K)) : ℚ :=
  ∑ q : SourceRealEdge V K,if coloredReal w K q=e then pathActivity w K q.1 q.2 else 0

lemma realPortion_on (w : V → V → ℚ) (K : ℕ) (q : SourceRealEdge V K) :
    realPortion w K (coloredReal w K q)=pathActivity w K q.1 q.2 := by
  simp only [realPortion,(coloredReal_injective w K).eq_iff,sum_ite_eq',mem_univ,ite_true]

lemma realPortion_off (w : V → V → ℚ) (K : ℕ) (e : BagEdge (bags w K))
    (he : ¬∃ q,coloredReal w K q=e) : realPortion w K e=0 := by
  apply sum_eq_zero
  intro q _
  exact ite_eq_right (fun h=>he ⟨q,h⟩)

lemma pathActivity_pos (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (e : LogicalEdge V) (i : Fin (4*(2*K+2)+1)) : 0<pathActivity w K e i := by
  have hb : 0<logicalB w (source e) (target e) := by
    have h : (1:ℝ)≤(logicalB w (source e) (target e):ℝ) := by
      rw [logicalB_cast]; exact one_le_bottleneck _ _ _
    have : (1:ℚ)≤logicalB w (source e) (target e) := by exact_mod_cast h
    linarith
  unfold pathActivity profile
  split_ifs
  · exact hb.trans_le (le_max_left _ _)
  · unfold BottleneckAlgorithm.edge
    split_ifs <;> exact hw _ _
  · exact hb.trans_le (le_max_left _ _)

lemma pathActivity_le_realB (w : V → V → ℚ) (K : ℕ) (e : SourceRealEdge V K) :
    pathActivity w K e.1 e.2≤realB w K (realLeft K e) (realRight K e) := by
  apply (Rat.cast_le (K:=ℝ)).mp
  rw [pathActivity_cast,realB_cast]
  exact edge_activity_le_realBottleneck source target source_ne_target (2*K+2) (by omega) _ _ _ _ e.1 e.2

def bagHeight (w : V → V → ℚ) (K : ℕ) (l : Label w K) : ℚ := 2^l.1.val

lemma realPortion_nonneg (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (e : BagEdge (bags w K)) : 0≤realPortion w K e := by
  apply sum_nonneg
  intro q _
  split_ifs
  · exact (pathActivity_pos w hw K q.1 q.2).le
  · exact le_rfl

lemma realPortion_le_height (w : V → V → ℚ) (K : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (e : BagEdge (bags w K)) : realPortion w K e≤2*bagHeight w K e.color := by
  by_cases he : ∃ q,coloredReal w K q=e
  · obtain ⟨q,rfl⟩:=he
    rw [realPortion_on]
    apply (pathActivity_le_realB w K q).trans
    apply (Rat.cast_le (K:=ℝ)).mp
    have hu:=dyadic_upper_of_lt (levels w K) (realB w K (realLeft K q) (realRight K q):ℝ)
      (by exact_mod_cast realB_upper w K h q)
    rw [←NumberedHierarchy.level_cast,pow_succ] at hu
    change (realB w K (realLeft K q) (realRight K q):ℝ)≤((2*2^_ : ℚ):ℝ)
    push_cast
    simpa only [coloredReal,BagEdge.color,ColoredEdge.color,realLabel,NumberedHierarchy.edgeLabel,NumberedHierarchy.labelAt,mul_comm] using hu.le
  · rw [realPortion_off w K e he]
    dsimp [bagHeight]
    positivity

def bagWeight (w : V → V → ℚ) (K D : ℕ) (e : BagEdge (bags w K)) : ℚ :=
  realPortion w K e+bagHeight w K e.color/D

lemma bagWeight_range (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 1≤D)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (e : BagEdge (bags w K)) :
    (bagHeight w K e.color:ℝ)/D≤(bagWeight w K D e:ℝ) ∧
      (bagWeight w K D e:ℝ)≤3*(bagHeight w K e.color:ℝ) := by
  have he:=realPortion_nonneg w hw K e
  have hu:=realPortion_le_height w K h e
  have hd : (1:ℚ)≤D := by exact_mod_cast hD
  have hh : bagHeight w K e.color/(D:ℚ)≤bagHeight w K e.color :=
    div_le_self (by dsimp [bagHeight]; positivity) hd
  have hlo : bagHeight w K e.color / (D:ℚ)≤bagWeight w K D e := by unfold bagWeight; linarith
  have hhi : bagWeight w K D e≤3*bagHeight w K e.color := by unfold bagWeight; linarith
  constructor <;> exact_mod_cast (by assumption)

lemma bagHeight_one (w : V → V → ℚ) (K : ℕ) (l : Label w K) : 1≤bagHeight w K l := by
  exact one_le_pow₀ (by norm_num)

lemma bagHeight_le (w : V → V → ℚ) (K : ℕ) (l : Label w K) : bagHeight w K l≤(4:ℚ)^K := by
  have hl : l.1.val≤2*K := (Nat.le_of_lt_succ l.1.isLt).trans (by rw [levels_eq]; exact sourceLevels_le _ _)
  calc
    _ ≤ (2:ℚ)^(2*K) := pow_le_pow_right₀ (by norm_num) hl
    _ = _ := by rw [pow_mul]; norm_num

lemma bagHeight_step (w : V → V → ℚ) (K : ℕ) (a b : Label w K) (h : (tree w K).Adj a b) :
    (bagHeight w K a:ℝ)≤2*(bagHeight w K b:ℝ) := by
  simpa only [bagHeight,Rat.cast_pow,Rat.cast_ofNat] using
    NumberedHierarchy.height_step (realB w K) (realB_symm w K) (realB_tri w K) (levels w K) a b h

lemma bagWeight_global (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 1≤D)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (e : BagEdge (bags w K)) :
    (D:ℝ)⁻¹≤(bagWeight w K D e:ℝ) ∧ (bagWeight w K D e:ℝ)≤3*4^K := by
  have hr:=bagWeight_range w hw K D hD h e
  have h1 : (1:ℝ)≤(bagHeight w K e.color:ℝ) := by exact_mod_cast bagHeight_one w K e.color
  have h4 : (bagHeight w K e.color:ℝ)≤(4:ℝ)^K := by exact_mod_cast bagHeight_le w K e.color
  constructor
  · calc
      (D:ℝ)⁻¹ = 1/(D:ℝ) := (one_div _).symm
      _ ≤ (bagHeight w K e.color:ℝ)/(D:ℝ) := div_le_div_of_nonneg_right h1 (Nat.cast_nonneg D)
      _ ≤ _ := hr.1
  · exact hr.2.trans (mul_le_mul_of_nonneg_left h4 (by norm_num))

open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Variation

attribute [local instance] prodOrder sumOrder

noncomputable local instance (w : V → V → ℚ) (K : ℕ) : DecidableEq (BagPM (bags w K)) := Classical.decEq _

def sampler (w : V → V → ℚ) (K D T m : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ)
    (s : Slot T (ladderQ (Fintype.card (SourceVertex V K)) D) → BagPM (bags w K)) :=
  finiteLadder (bags_adjacent w K h) (tree_acyclic w K) (fun l=>l.1.val) (parent w K)
    (bags_ranked w K h) (bags_nonempty w K) (parent_rank w K) D K T m hq (bagWeight w K D) M η s

noncomputable local instance (w : V → V → ℚ) (K : ℕ) : Fintype (BagPM (bags w K)) := Fintype.ofFinite _

theorem sampler_tv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D T m : ℕ) (hD : 1≤D)
    (hN : 2≤Fintype.card (SourceVertex V K)) (hm : 1 < m)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) (hη : 0<η)
    (s : Slot T (ladderQ (Fintype.card (SourceVertex V K)) D) → BagPM (bags w K)) :
    tv (imageLaw (sampler w K D T m h hq M η s))
      (ladderLaw (fun e=>(bagWeight w K D e:ℝ)) T (ladderQ (Fintype.card (SourceVertex V K)) D))≤
        (η:ℝ)+(m:ℝ)⁻¹ := by
  apply finiteLadder_tv (bags_adjacent w K h) (tree_acyclic w K) (fun l=>l.1.val) (parent w K)
    (bags_ranked w K h) (bags_nonempty w K) (parent_rank w K) (fun l=>(bagHeight w K l:ℝ))
    (fun l=>by have hh : (1:ℝ)≤(bagHeight w K l:ℝ) := by exact_mod_cast bagHeight_one w K l
               linarith)
    (bagHeight_step w K) D K hD hN (bagWeight w K D) (bagWeight_range w hw K D hD h)
    (bagWeight_global w hw K D hD h) M T m hm η hη hq s

end MatchingFPRAS.RationalSource

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable local instance : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _

omit [DecidableEq V] in
lemma gibbs_instances [DecidableEq V] {E : Type*} (F₁ F₂ : Fintype E) (inc : E → V → Prop)
    (w : E → ℝ) : @gibbs V E _ inc F₁ w = @gibbs V E _ inc F₂ w := by
  cases Subsingleton.elim F₁ F₂
  rfl

omit [DecidableEq J] in
lemma slotLaw_of_weight [DecidableEq J] {T q : ℕ} (F : Fintype (BagEdge bags))
    (w : BagEdge bags → ℝ) (i : Slot T q)
    (he : slotWeight w i=w) : slotLaw w i=@gibbs V (BagEdge bags) _ BagEdge.Incident F w := by
  change @gibbs V (BagEdge bags) _ BagEdge.Incident (instFintypeBagEdge_5 (bags:=bags))
    (slotWeight w i)=_
  rw [he]
  exact gibbs_instances _ _ _ _

lemma top_marginal_tv {A : Type*} [Fintype A] {T q : ℕ} (F : Fintype (BagEdge bags))
    (hq : 0<q) (w : BagEdge bags → ℝ) (M : PM (BagEdge.Incident (bags:=bags)))
    (f : A → Slot T q → PM (BagEdge.Incident (bags:=bags)))
    (he : slotWeight w (topSlot T q hq)=w) :
    Variation.tv (Variation.imageLaw (fun a=>f a (topSlot T q hq)))
      (@gibbs V (BagEdge bags) _ BagEdge.Incident F w)≤
      Variation.tv (Variation.imageLaw f) (ladderLaw w T q) := by
  have ht:=Variation.push_contraction (Variation.imageLaw f) (ladderLaw w T q)
    (fun x=>x (topSlot T q hq))
  rw [ladder_top_marginal w T q hq M,slotLaw_of_weight F _ _ he] at ht
  change Variation.tv (Variation.imageLaw ((fun x=>x (topSlot T q hq)) ∘ f)) _≤_
  rw [Variation.imageLaw_comp]
  exact ht



open Finset Replica Replica.Ladder Variation

def rationalBase (N : ℕ) : ℚ := 1+((N:ℚ)^2)⁻¹

lemma rationalBase_cast (N : ℕ) : (rationalBase N:ℝ)=1+((N:ℝ)^2)⁻¹ := by
  simp [rationalBase]

private lemma reaches_cast (N D K t : ℕ) :
    max (D:ℚ) (3*4^K)≤(rationalBase N)^t ↔
      max (D:ℝ) (3*4^K)≤(1+((N:ℝ)^2)⁻¹)^t := by
  rw [←rationalBase_cast]
  exact_mod_cast (Iff.rfl : max (D:ℚ) (3*4^K)≤(rationalBase N)^t ↔ _)

def endpoint (N D K : ℕ) (hN : 0<N) : ℕ :=
  ((range (tierBound N D K+1)).filter
    (fun t => max (D:ℚ) (3*4^K)≤(rationalBase N)^t)).min'
      (by refine ⟨tierBound N D K,mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩⟩
          exact (reaches_cast _ _ _ _).mpr (tierBound_reaches N D K hN))

lemma endpoint_eq (N D K : ℕ) (hN : 0<N) : endpoint N D K hN=ladderTier N D K hN := by
  apply Nat.le_antisymm
  · apply min'_le
    apply mem_filter.mpr
    exact ⟨mem_range.mpr (by have := ladderTier_le N D K hN; omega),
      (reaches_cast _ _ _ _).mpr (ladderTier_spec N D K hN)⟩
  · have he : max (D:ℝ) (3*4^K)≤(1+((N:ℝ)^2)⁻¹)^(endpoint N D K hN) := by
      apply (reaches_cast _ _ _ _).mp
      unfold endpoint
      exact (mem_filter.mp (min'_mem ((range (tierBound N D K+1)).filter
        (fun t => max (D:ℚ) (3*4^K)≤(rationalBase N)^t)) _)).2
    unfold ladderTier
    exact Nat.find_min' _ he

lemma endpoint_reaches (N D K : ℕ) (hN : 0<N) :
    max (D:ℝ) (3*4^K)≤(1+((N:ℝ)^2)⁻¹)^(endpoint N D K hN) := by
  rw [endpoint_eq]; exact ladderTier_spec N D K hN

end MatchingFPRAS.Transport

namespace MatchingFPRAS.RationalSource

open Finset MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Enlargement
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Variation

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance (w : V → V → ℚ) (K : ℕ) : DecidableEq (BagPM (bags w K)) := Classical.decEq _

noncomputable local instance (w : V → V → ℚ) (K : ℕ) : Fintype (BagPM (bags w K)) := Fintype.ofFinite _

def topSampler (w : V → V → ℚ) (K D m : ℕ) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :=
  fun bits => sampler w K D (endpoint (Fintype.card (SourceVertex V K)) D K hN) m h hq M η
    (fun _=>M) bits (topSlot _ _ hq)

theorem topSampler_tv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ) (hD : 1≤D)
    (hN : 2≤Fintype.card (SourceVertex V K)) (hm : 1 < m)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) (hη : 0<η) :
    tv (imageLaw (topSampler w K D m (by omega) h hq M η))
      (gibbs (fun e=>(bagWeight w K D e:ℝ)))≤(η:ℝ)+(m:ℝ)⁻¹ := by
  let T:=endpoint (Fintype.card (SourceVertex V K)) D K (by omega)
  have hs:=sampler_tv w hw K D T m hD hN hm h hq M η hη (fun _=>M)
  have he:=slotWeight_top (fun e=>(bagWeight w K D e:ℝ)) D K T _ (by omega) hq
    (bagWeight_global w hw K D hD h) (endpoint_reaches _ _ _ (by omega))
  exact (top_marginal_tv (bagEdgeFintype (bags:=bags w K)) hq (fun e=>(bagWeight w K D e:ℝ)) M
    (sampler w K D T m h hq M η (fun _=>M)) he).trans hs

end MatchingFPRAS.RationalSource

end OAI
