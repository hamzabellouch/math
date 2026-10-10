import OAI.Probability.TraceReconstruction.Anchors

namespace OAI

/-!
# Shapes

Global schedules, edge labels, forced/extra coordinate splitting, finite shape codes, and occupied-label counts.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Source central third, in the zero-based child label convention. The
shift of the source one-based indices is recorded in center parameters. -/
def centralThird (N : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun u => N ≤ 3*u.val ∧ 3*u.val ≤ 2*N)

/-- One actual global-pair orientation, ordered by its pre-region block and
its local identifier there. -/
def globalTrialIndex (N t : ℕ) (v : Fin (N/4)) (a : Fin t) : Fin ((N/4)*t) :=
  ⟨v.val*t+a.val, by nlinarith [v.isLt,a.isLt]⟩

/-- Literal net global displacement immediately before a child window:
a pre block at v+1 remains active through its matched post region N-v.
The paired displacement has even t trials in each affected region. -/
def scheduledGlobalShift (N t : ℕ) (bits : Fin ((N/4)*t) → Bool) (u : Fin N) : ℤ :=
  ∑v : Fin (N/4), if v.val ≤ u.val ∧ u.val+v.val<N then
    (∑a : Fin t, (bitIndex (bits (globalTrialIndex N t v a)):ℤ))-(t/2:ℕ) else 0

theorem centralThird_active (N : ℕ) (u : Fin N) (hu : u∈centralThird N)
    (v : Fin (N/4)) : v.val≤u.val ∧ u.val+v.val<N := by
  have huu := (Finset.mem_filter.mp hu).2
  have hv := v.isLt
  have hd := Nat.mod_add_div N 4
  have hm := Nat.mod_lt N (by omega : 0<4)
  omega

theorem globalTrialIndex_bijective (N t : ℕ) :
    Function.Bijective (fun x : Fin (N/4) × Fin t => globalTrialIndex N t x.1 x.2) := by
  constructor
  · intro x y he
    have he' := congrArg Fin.val he
    change x.1.val*t+x.2.val = y.1.val*t+y.2.val at he'
    have hx := x.2.isLt
    have hy := y.2.isLt
    have hv : x.1.val=y.1.val := by
      by_contra h
      rcases lt_or_gt_of_ne h with h | h <;> nlinarith
    have ha : x.2.val=y.2.val := by rw [hv] at he'; omega
    exact Prod.ext (Fin.ext hv) (Fin.ext ha)
  · intro i
    have ht : 0<t := by
      by_contra h
      have hz : t=0 := by omega
      have := i.isLt
      simp only [hz,Nat.mul_zero] at this
      omega
    refine ⟨(⟨i.val/t, (Nat.div_lt_iff_lt_mul ht).mpr i.isLt⟩,
      ⟨i.val%t,Nat.mod_lt _ ht⟩),?_⟩
    apply Fin.ext
    change i.val/t*t+i.val%t=i.val
    simpa only [Nat.mul_comm] using Nat.div_add_mod i.val t

theorem globalTrial_sum (N t : ℕ) (f : Fin ((N/4)*t) → ℤ) :
    (∑v : Fin (N/4),∑a : Fin t,f (globalTrialIndex N t v a)) = ∑i,f i := by
  let e := Equiv.ofBijective _ (globalTrialIndex_bijective N t)
  have h := e.sum_comp f
  simpa only [e,Fintype.sum_prod_type,Equiv.ofBijective_apply] using h

theorem scheduledGlobalShift_plateau (N t : ℕ) (ht : Even t)
    (bits : Fin ((N/4)*t) → Bool) (u : Fin N) (hu : u∈centralThird N) :
    scheduledGlobalShift N t bits u = (∑i,(bitIndex (bits i):ℤ))-(((N/4)*t)/2:ℕ) := by
  have hd : 2 ∣ t := (even_iff_two_dvd).mp ht
  have hh := Nat.mul_div_assoc (N/4) hd
  calc
    _ = ∑v : Fin (N/4),
        ((∑a : Fin t, (bitIndex (bits (globalTrialIndex N t v a)):ℤ))-(t/2:ℕ)) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact ite_eq_left (centralThird_active N u hu v)
    _ = (∑i,(bitIndex (bits i):ℤ))-(N/4:ℕ)*(t/2:ℕ) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      · exact globalTrial_sum N t (fun i => (bitIndex (bits i):ℤ))
      · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ = _ := by congr 1; exact_mod_cast hh.symm


/-- The actual complete-tree global schedule has the exact plateau identity
needed by the already proved correlated anchor energy theorem. -/
def sourceGlobalTrials (T t : ℕ → ℕ) (b : ℕ) : ℕ := (T b/4)*t b

def sourceGlobalShift (T t : ℕ → ℕ) (b : ℕ)
    (bits : Fin (sourceGlobalTrials T t b) → Bool) (u : Fin (T b)) : ℤ :=
  scheduledGlobalShift (T b) (t b) bits u

theorem sourceGlobalShift_hasPlateau (T t : ℕ → ℕ) (ht : ∀b,Even (t b)) :
    HasGlobalPlateau T (sourceGlobalTrials T t) (fun b => centralThird (T b))
      (fun b => (sourceGlobalTrials T t b/2:ℕ)) (sourceGlobalShift T t) := by
  intro b bits u hu
  exact scheduledGlobalShift_plateau (T b) (t b) (ht b) bits u hu
end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

/-- One actual child-label coordinate of an arbitrary ordered occupied
shape. Unlike a complete r-ary padding, this contains no unused edges. -/
def Edge : {b : ℕ} → OccupiedParityTree b → Type
  | _, .leaf => PEmpty
  | _, .node n children _ => Fin n ⊕ ((i : Fin n) × Edge (children i))

noncomputable instance edgeFintype : {b : ℕ} → (t : OccupiedParityTree b) → Fintype t.Edge
  | _, .leaf => inferInstanceAs (Fintype PEmpty)
  | _, .node n children roles => by
      letI := fun i => edgeFintype (children i)
      exact inferInstanceAs (Fintype (Fin n ⊕ ((i : Fin n) × Edge (children i))))

def Edge.height : {b : ℕ} → {t : OccupiedParityTree b} → t.Edge → ℕ
  | _, .leaf, e => e.elim
  | _, @OccupiedParityTree.node b _n _children _roles, e =>
      match e with
      | Sum.inl _ => b
      | Sum.inr z => Edge.height z.2

/-- All literal label assignments to this particular ordered shape. -/
def Labels (T : ℕ → ℕ) {b : ℕ} (t : OccupiedParityTree b) :=
  (e : t.Edge) → Fin (T e.height)

noncomputable instance labelsFintype (T : ℕ → ℕ) {b : ℕ} (t : OccupiedParityTree b) :
    Fintype (t.Labels T) := inferInstanceAs (Fintype ((e : t.Edge) → Fin (T e.height)))

def Labels.child (T : ℕ → ℕ) {b n : ℕ} {children : Fin n → OccupiedParityTree b}
    {roles : Fin n → Fin 3} (x : (OccupiedParityTree.node n children roles).Labels T)
    (i : Fin n) : (children i).Labels T := fun e => x (Sum.inr ⟨i,e⟩)

/-- Projection to the actual labels of a fixed forced subtree. The shape
selection is independent of these labels and of all random orientations. -/
def Forced.labels (T : ℕ → ℕ) : {b : ℕ} → {t : OccupiedParityTree b} →
    t.Forced → t.Labels T → BinaryWindowLabels T b
  | _, _, .leaf, _ => PUnit.unit
  | _, _, .node a c _ _ _ left right, x =>
      (x (Sum.inl a),x (Sum.inl c),left.labels T (x.child T a),right.labels T (x.child T c))

/-- Edge addresses in a complete binary tree, independent of all actual
numeric labels. False and true are its two children. -/
def BinaryEdge : ℕ → Type
  | 0 => PEmpty
  | b+1 => Bool ⊕ (Bool × BinaryEdge b)

noncomputable instance binaryEdgeFintype : (b : ℕ) → Fintype (BinaryEdge b)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | b+1 => by
      letI := binaryEdgeFintype b
      exact inferInstanceAs (Fintype (Bool ⊕ (Bool × BinaryEdge b)))

def BinaryEdge.height : {b : ℕ} → BinaryEdge b → ℕ
  | 0, e => e.elim
  | b+1, Sum.inl _ => b
  | _b+1, Sum.inr e => BinaryEdge.height e.2

/-- The forced binary tree is embedded in the actual occupied edge set. -/
def Forced.edge : {b : ℕ} → {t : OccupiedParityTree b} → t.Forced → BinaryEdge b → t.Edge
  | _, _, .leaf, e => e.elim
  | _, _, .node a _ _ _ _ _ _, Sum.inl false => Sum.inl a
  | _, _, .node _ c _ _ _ _ _, Sum.inl true => Sum.inl c
  | _, _, .node a _ _ _ _ left _, Sum.inr (false,e) => Sum.inr ⟨a,left.edge e⟩
  | _, _, .node _ c _ _ _ _ right, Sum.inr (true,e) => Sum.inr ⟨c,right.edge e⟩

theorem Forced.edge_injective {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    Function.Injective F.edge := by
  induction F with
  | leaf => intro i; exact i.elim
  | @node b n children roles a c hne ha hc left right ihl ihr =>
    intro i j he
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        cases i <;> cases j
        · rfl
        · exact (hne (Sum.inl.inj he)).elim
        · exact (hne (Sum.inl.inj he).symm).elim
        · rfl
      | inr j => cases i <;> rcases j with ⟨j,e⟩ <;> cases j <;> cases he
    | inr i =>
      cases j with
      | inl j => rcases i with ⟨i,e⟩; cases i <;> cases j <;> cases he
      | inr j =>
        rcases i with ⟨i,e⟩
        rcases j with ⟨j,f⟩
        cases i <;> cases j
        · have hh := Sum.inr.inj he
          have hh' : left.edge e=left.edge f := by injection hh
          exact congrArg (fun e => Sum.inr (false,e)) (ihl hh')
        · have hh := congrArg Sigma.fst (Sum.inr.inj he)
          exact (hne hh).elim
        · have hh := congrArg Sigma.fst (Sum.inr.inj he)
          exact (hne hh.symm).elim
        · have hh := Sum.inr.inj he
          have hh' : right.edge e=right.edge f := by injection hh
          exact congrArg (fun e => Sum.inr (true,e)) (ihr hh')

theorem Forced.edge_height {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (e : BinaryEdge b) : (F.edge e).height=e.height := by
  induction F with
  | leaf => exact e.elim
  | @node b n children roles a c hne ha hc left right ihl ihr =>
    cases e with
    | inl i => cases i <;> rfl
    | inr z => rcases z with ⟨i,e⟩; cases i; exact ihl e; exact ihr e

/-- The finite number of edge coordinates at a given child height. -/
def edgeCount {b : ℕ} (t : OccupiedParityTree b) (h : ℕ) : ℕ :=
  Fintype.card {e : t.Edge // e.height=h}

theorem edgeCount_leaf (h : ℕ) : edgeCount OccupiedParityTree.leaf h=0 := by
  unfold edgeCount
  exact Fintype.card_eq_zero_iff.mpr ⟨fun e => e.val.elim⟩

theorem edgeCount_node {b n : ℕ} (children : Fin n → OccupiedParityTree b)
    (roles : Fin n → Fin 3) (h : ℕ) :
    edgeCount (.node n children roles) h = (if b=h then n else 0)+∑i,edgeCount (children i) h := by
  unfold edgeCount
  simp only [Fintype.card_subtype, Finset.card_filter]
  change (∑e : Fin n ⊕ ((i : Fin n) × (children i).Edge),if Edge.height (t := .node n children roles) e=h then 1 else 0)=_
  rw [Fintype.sum_sum_type]
  simp only [Edge.height,Fintype.sum_sigma]

  split_ifs <;> simp_all <;> simp only [Finset.card_filter] <;> rfl

theorem Edge.height_lt {b : ℕ} {t : OccupiedParityTree b} (e : t.Edge) : e.height<b := by
  induction t with
  | leaf => exact e.elim
  | @node b n children roles ih =>
    cases e with
    | inl i => exact Nat.lt_succ_self b
    | inr z => exact Nat.lt_succ_of_lt (ih z.1 z.2)

theorem edgeCount_outside {b : ℕ} (t : OccupiedParityTree b) (h : ℕ) (hh : b≤h) :
    t.edgeCount h=0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun e => ?_⟩
  have hc := e.val.height_lt
  rw [e.property] at hc
  omega

theorem edgeCount_level {b : ℕ} (t : OccupiedParityTree b) (h : ℕ) (hh : h<b) :
    t.edgeCount h=t.levelCount (b-h) := by
  induction t with
  | leaf => omega
  | @node b n children roles ih =>
    rw [edgeCount_node]
    by_cases he : h=b
    · subst h
      have hz (i : Fin n) := edgeCount_outside (children i) b le_rfl
      simp only [hz,Finset.sum_const_zero,add_zero,Nat.add_sub_cancel_left,
        levelCount,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
      rfl
    · have hh' : h<b := by omega
      have hd : b+1-h=(b-h)+1 := by omega
      rw [ite_eq_right (Ne.symm he),zero_add,hd]
      exact Finset.sum_congr rfl (fun i _ => ih i hh')

def BinaryEdgeLabels (T : ℕ → ℕ) (b : ℕ) := (e : BinaryEdge b) → Fin (T e.height)

noncomputable instance binaryEdgeLabelsFintype (T : ℕ → ℕ) (b : ℕ) :
    Fintype (BinaryEdgeLabels T b) := inferInstanceAs (Fintype ((e : BinaryEdge b) → Fin (T e.height)))

/-- Exact coordinates of the recursively defined forced label tuple. -/
def binaryLabelsEquiv (T : ℕ → ℕ) : (b : ℕ) → BinaryEdgeLabels T b ≃ BinaryWindowLabels T b
  | 0 =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ e => e.elim
      left_inv := fun _ => by funext e; exact e.elim
      right_inv := fun y => by cases y; rfl }
  | b+1 =>
    { toFun := fun x => (x (Sum.inl false),x (Sum.inl true),
        binaryLabelsEquiv T b (fun e => x (Sum.inr (false,e))),
        binaryLabelsEquiv T b (fun e => x (Sum.inr (true,e))))
      invFun := fun x e => match e with
        | Sum.inl false => x.1
        | Sum.inl true => x.2.1
        | Sum.inr (false,e) => (binaryLabelsEquiv T b).symm x.2.2.1 e
        | Sum.inr (true,e) => (binaryLabelsEquiv T b).symm x.2.2.2 e
      left_inv := fun x => by
        funext e
        cases e with
        | inl j => cases j <;> rfl
        | inr z =>
          rcases z with ⟨j,e⟩
          cases j <;> exact congrFun ((binaryLabelsEquiv T b).symm_apply_apply _) e
      right_inv := fun x => by
        rcases x with ⟨a,c,l,r⟩
        simp only [Equiv.apply_symm_apply]
        rfl }

/-- Restriction to the real forced coordinates, with only equality transport
of the child-height index. -/
def Forced.restrict (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (x : t.Labels T) : BinaryEdgeLabels T b := fun e =>
  Fin.cast (congrArg T (F.edge_height e)) (x (F.edge e))

theorem Forced.restrict_labels (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (x : t.Labels T) : binaryLabelsEquiv T b (F.restrict T x)=F.labels T x := by
  induction F with
  | leaf => rfl
  | @node b n children roles a c hne ha hc left right ihl ihr =>
    change (x (Sum.inl a),x (Sum.inl c),_,_) = (x (Sum.inl a),x (Sum.inl c),_,_)
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
    · exact ihl (x.child T a)
    · exact ihr (x.child T c)

end OccupiedParityTree
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

def Forced.ExtraEdge {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :=
  {e : t.Edge // e∉Set.range F.edge}

noncomputable instance forcedExtraEdgeFintype {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    Fintype F.ExtraEdge := inferInstanceAs (Fintype {e : t.Edge // e∉Set.range F.edge})

def Forced.ExtraLabels (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :=
  (e : F.ExtraEdge) → Fin (T e.val.height)

noncomputable instance forcedExtraLabelsFintype (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) : Fintype (F.ExtraLabels T) :=
  inferInstanceAs (Fintype ((e : F.ExtraEdge) → Fin (T e.val.height)))

/-- Exact bijective partition of all actual edge coordinates into the
forced binary coordinates and the genuine extra coordinates. -/
noncomputable def Forced.labelsEquiv (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    t.Labels T ≃ BinaryWindowLabels T b × F.ExtraLabels T := by
  classical
  letI : DecidablePred (Set.range F.edge) := fun _ => Classical.propDecidable _
  exact (Equiv.piEquivPiSubtypeProd (Set.range F.edge) (fun e : t.Edge => Fin (T e.height))).trans
    (Equiv.prodCongr
      (((Equiv.piCongrLeft (fun e : Set.range F.edge => Fin (T e.val.height))
        (Equiv.ofInjective F.edge F.edge_injective)).symm.trans
          (Equiv.piCongrRight fun e => finCongr (congrArg T (F.edge_height e)))).trans
            (binaryLabelsEquiv T b))
      (Equiv.refl _))

theorem Forced.labelsEquiv_fst (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (x : t.Labels T) : (F.labelsEquiv T x).1=F.labels T x := by
  exact F.restrict_labels T x

theorem Forced.labelsEquiv_snd (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (x : t.Labels T) : (F.labelsEquiv T x).2=(fun e : F.ExtraEdge => x e.val) := rfl

/-- Literal finite Fubini over forced labels and all remaining labels. -/
theorem Forced.sum_labels (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (f : BinaryWindowLabels T b → F.ExtraLabels T → ℝ) :
    (∑x : t.Labels T,f (F.labels T x) (fun e => x e.val)) =
      ∑p : BinaryWindowLabels T b, ∑z : F.ExtraLabels T,f p z := by
  have h := (F.labelsEquiv T).sum_comp (fun x => f x.1 x.2)
  simpa only [Forced.labelsEquiv_fst,Forced.labelsEquiv_snd,Fintype.sum_prod_type] using h

def Forced.ExtraLeafEdge {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :=
  {e : F.ExtraEdge // e.val.height=0}

def Forced.ExtraInteriorEdge {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :=
  {e : F.ExtraEdge // e.val.height≠0}

noncomputable instance extraLeafEdgeFintype {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    Fintype F.ExtraLeafEdge := inferInstanceAs (Fintype {e : F.ExtraEdge // e.val.height=0})

noncomputable instance extraInteriorEdgeFintype {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    Fintype F.ExtraInteriorEdge := inferInstanceAs (Fintype {e : F.ExtraEdge // e.val.height≠0})

def Forced.InteriorLabels (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :=
  (e : F.ExtraInteriorEdge) → Fin (T e.val.val.height)

noncomputable instance extraInteriorLabelsFintype (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) : Fintype (F.InteriorLabels T) :=
  inferInstanceAs (Fintype ((e : F.ExtraInteriorEdge) → Fin (T e.val.val.height)))

/-- Extra bottom labels are separated from all nonleaf labels without
introducing any T₁ factor. -/
noncomputable def Forced.extraLabelsEquiv (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) : F.ExtraLabels T ≃ (F.ExtraLeafEdge → Fin (T 0)) × F.InteriorLabels T :=
  (Equiv.piEquivPiSubtypeProd (fun e : F.ExtraEdge => e.val.height=0)
    (fun e : F.ExtraEdge => Fin (T e.val.height))).trans
    (Equiv.prodCongr (Equiv.piCongrRight fun e => finCongr (congrArg T e.property)) (Equiv.refl _))

end OccupiedParityTree
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

/-- The parent address of an edge in the full deterministic numerical index
tree. In particular it does not contain the edge's own child label. -/
def Edge.parentPath (T : ℕ → ℕ) : {b : ℕ} → {t : OccupiedParityTree b} →
    t.Labels T → t.Edge → List ℕ
  | _, .leaf, _, e => e.elim
  | _, .node _n _children _roles, x, e => match e with
    | Sum.inl _ => []
    | Sum.inr z => (x (Sum.inl z.1)).val :: Edge.parentPath T (x.child T z.1) z.2

/-- Every ancestor label of an extra selected leaf is an interior label. -/
theorem Edge.parentPath_congr (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (x y : t.Labels T) (h : ∀e : t.Edge, e.height≠0 → (x e).val=(y e).val)
    (e : t.Edge) : e.parentPath T x=e.parentPath T y := by
  induction t with
  | leaf => exact e.elim
  | @node b n children roles ih =>
    cases e with
    | inl i => rfl
    | inr z =>
      have hb : b≠0 := by have := z.2.height_lt; omega
      change (x (Sum.inl z.1)).val :: _ = (y (Sum.inl z.1)).val :: _
      congr 1
      · exact h (Sum.inl z.1) hb
      · exact ih z.1 (x.child T z.1) (y.child T z.1)
          (fun e he => h (Sum.inr ⟨z.1,e⟩) he) z.2

theorem Forced.labels_value_eq (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) (x y : t.Labels T) (h : F.labels T x=F.labels T y) (j : BinaryEdge b) :
    (x (F.edge j)).val=(y (F.edge j)).val := by
  have hh := (binaryLabelsEquiv T b).injective
    ((F.restrict_labels T x).trans (h.trans (F.restrict_labels T y).symm))
  exact congrArg (fun z : BinaryEdgeLabels T b => (z j).val) hh

/-- The combined exact split into forced, extra-leaf and extra-interior labels. -/
noncomputable def Forced.fullLabelsEquiv (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) : t.Labels T ≃
      BinaryWindowLabels T b × (F.ExtraLeafEdge → Fin (T 0)) × F.InteriorLabels T :=
  (F.labelsEquiv T).trans (Equiv.prodCongr (Equiv.refl _) (F.extraLabelsEquiv T))

theorem Forced.fullLabelsEquiv_fst (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) (x : t.Labels T) : (F.fullLabelsEquiv T x).1=F.labels T x :=
  F.labelsEquiv_fst T x

theorem Forced.fullLabelsEquiv_leaf_value (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) (x : t.Labels T) (e : F.ExtraLeafEdge) :
    ((F.fullLabelsEquiv T x).2.1 e).val=(x e.val.val).val := rfl

theorem Forced.fullLabelsEquiv_interior_value (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) (x : t.Labels T) (e : F.ExtraInteriorEdge) :
    ((F.fullLabelsEquiv T x).2.2 e).val=(x e.val.val).val := rfl

/-- Changing only extra leaf labels changes no ancestor address, even when
all the complete-tree mechanisms share their source global bits. -/
theorem Forced.parentPath_extraLeaf_invariant (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) (p : BinaryWindowLabels T b) (h k : F.ExtraLeafEdge → Fin (T 0))
    (z : F.InteriorLabels T) (e : t.Edge) :
    e.parentPath T ((F.fullLabelsEquiv T).symm (p,h,z)) =
      e.parentPath T ((F.fullLabelsEquiv T).symm (p,k,z)) := by
  let x := (F.fullLabelsEquiv T).symm (p,h,z)
  let y := (F.fullLabelsEquiv T).symm (p,k,z)
  have hx : F.fullLabelsEquiv T x=(p,h,z) := Equiv.apply_symm_apply _ _
  have hy : F.fullLabelsEquiv T y=(p,k,z) := Equiv.apply_symm_apply _ _
  have hp : F.labels T x=F.labels T y := by
    rw [←F.fullLabelsEquiv_fst,←F.fullLabelsEquiv_fst,hx,hy]
  apply Edge.parentPath_congr T x y
  intro i hi
  by_cases hr : i∈Set.range F.edge
  · obtain ⟨j,rfl⟩ := hr
    exact F.labels_value_eq T x y hp j
  · let j : F.ExtraInteriorEdge := ⟨⟨i,hr⟩,hi⟩
    have hvx := congrArg (fun a => (a.2.2 j).val) hx
    have hvy := congrArg (fun a => (a.2.2 j).val) hy
    have hv := hvx.trans hvy.symm
    simpa only [Forced.fullLabelsEquiv_interior_value] using hv

end OccupiedParityTree
end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

/-- A finite ordered-role shape code with at most r children at every
vertex. There are no numerical child labels in this type. -/
def FiniteRoleShape (r : ℕ) : ℕ → Type
  | 0 => PUnit
  | b+1 => (n : Fin (r+1)) × (Fin n.val → FiniteRoleShape r b) × (Fin n.val → Fin 3)

noncomputable instance finiteRoleShapeFintype (r : ℕ) : (b : ℕ) → Fintype (FiniteRoleShape r b)
  | 0 => inferInstanceAs (Fintype PUnit)
  | b+1 => by
    letI := finiteRoleShapeFintype r b
    exact inferInstanceAs (Fintype ((n : Fin (r+1)) ×
      (Fin n.val → FiniteRoleShape r b) × (Fin n.val → Fin 3)))

def FiniteRoleShape.toTree (r : ℕ) : (b : ℕ) → FiniteRoleShape r b → OccupiedParityTree b
  | 0, _ => .leaf
  | b+1, x => .node x.1.val (fun i => (x.2.1 i).toTree r b) x.2.2

theorem occupied_arity_le_leaves {b n : ℕ} (children : Fin n → OccupiedParityTree b)
    (roles : Fin n → Fin 3) (ht : (OccupiedParityTree.node n children roles).occupied) :
    n≤(OccupiedParityTree.node n children roles).leafCount := by
  have h (i : Fin n) : 1≤(children i).leafCount := leafCount_pos _ (ht.2 i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,leafCount]
    using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => h i)

theorem child_le_leaves {b n : ℕ} (children : Fin n → OccupiedParityTree b)
    (roles : Fin n → Fin 3) (i : Fin n) :
    (children i).leafCount≤(OccupiedParityTree.node n children roles).leafCount :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((children j).leafCount)) (Finset.mem_univ i)

/-- Every occupied shape with r selected leaves really has a finite code
whose domain depends only on r and the depth, not on any window size. -/
theorem exists_finiteRoleShape {b : ℕ} (t : OccupiedParityTree b) (r : ℕ)
    (ht : t.occupied) (hr : t.leafCount≤r) :
    ∃x : FiniteRoleShape r b,x.toTree r b=t := by
  induction t with
  | leaf => exact ⟨PUnit.unit,rfl⟩
  | @node b n children roles ih =>
    have hn : n<r+1 := by have := occupied_arity_le_leaves children roles ht; omega
    have hx (i : Fin n) : ∃x : FiniteRoleShape r b,x.toTree r b=children i :=
      ih i (ht.2 i) ((child_le_leaves children roles i).trans hr)
    choose x hx using hx
    refine ⟨⟨⟨n,hn⟩,x,roles⟩,?_⟩
    change OccupiedParityTree.node n (fun i => (x i).toTree r b) roles = _
    congr 1
    exact funext hx

/-- The manuscript's finite shape/role constant, now a literal natural
number independent of the actual child-label sizes and all channel data. -/
def shapeRoleConstant (r b : ℕ) : ℕ := Fintype.card (FiniteRoleShape r b)

theorem finite_bounded_occupied_shapes (b r : ℕ) :
    Finite {t : OccupiedParityTree b // t.occupied ∧ t.leafCount≤r} := by
  let f : {t : OccupiedParityTree b // t.occupied ∧ t.leafCount≤r} → FiniteRoleShape r b :=
    fun t => Classical.choose (exists_finiteRoleShape t.val r t.property.1 t.property.2)
  apply Finite.of_injective f
  intro x y he
  apply Subtype.ext
  have hx := Classical.choose_spec (exists_finiteRoleShape x.val r x.property.1 x.property.2)
  have hy := Classical.choose_spec (exists_finiteRoleShape y.val r y.property.1 y.property.2)
  dsimp only [f] at he
  exact hx.symm.trans ((congrArg (FiniteRoleShape.toTree r b) he).trans hy)
end OccupiedParityTree
end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Extra-leaf index set version of the whole-bit-law sum. -/
def indexedExtraAverage {Ω E : Type*} [Fintype Ω] [Fintype E] (P : FiniteLaw Ω)
    (s N : ℕ) (f : Ω → ℝ) (X : Ω → E → ℤ) (h : E → Fin N) : ℝ :=
  P.expect (fun ω => f ω*∏j,motifIndicator s (((h j).val:ℤ)-X ω j))

theorem indexedExtraAverage_nonneg {Ω E : Type*} [Fintype Ω] [Fintype E] (P : FiniteLaw Ω)
    (s N : ℕ) (f : Ω → ℝ) (hf : ∀ω,0≤f ω) (X : Ω → E → ℤ)
    (h : E → Fin N) : 0 ≤ indexedExtraAverage P s N f X h := by
  apply Finset.sum_nonneg
  intro ω hω
  apply mul_nonneg (P.nonneg ω)
  exact mul_nonneg (hf ω) (Finset.prod_nonneg (fun j _ => motifIndicator_nonneg _ _))

theorem indexedExtraAverage_sum {Ω E : Type*} [Fintype Ω] [Fintype E] (P : FiniteLaw Ω)
    (s N : ℕ) (f : Ω → ℝ) (hf : ∀ω,0≤f ω) (X : Ω → E → ℤ) :
    (∑h : E → Fin N,indexedExtraAverage P s N f X h) ≤
      ((2^s:ℕ):ℝ)^(Fintype.card E)*P.expect f := by
  unfold indexedExtraAverage expect
  rw [Finset.sum_comm]
  simp_rw [←mul_assoc,←Finset.mul_sum]
  calc
    _ ≤ ∑ω,P.mass ω*f ω*(((2^s:ℕ):ℝ)^(Fintype.card E)) := by
      apply Finset.sum_le_sum
      intro ω hω
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (P.nonneg _) (hf ω))
      have he := Fintype.prod_sum (fun (j : E) (h : Fin N) => motifIndicator s ((h.val:ℤ)-X ω j))
      rw [←he]
      calc
        _ ≤ ∏_j : E,((2^s:ℕ):ℝ) := by
          apply Finset.prod_le_prod₀
          · intro j hj
            exact Finset.sum_nonneg (fun h hh => motifIndicator_nonneg _ _)
          · intro j hj
            exact motifIndicator_finite_sum s N (X ω j)
        _ = _ := by simp
    _ = _ := by rw [←Finset.sum_mul]; ring

theorem indexedExtraAverage_energy {Ω E : Type*} [Fintype Ω] [Fintype E] (P : FiniteLaw Ω)
    (s N : ℕ) (f : Ω → ℝ) (hf : ∀ω,0≤f ω) (X : Ω → E → ℤ) :
    (∑h : E → Fin N,indexedExtraAverage P s N f X h ^ 2) ≤
      ((2^s:ℕ):ℝ)^(2*Fintype.card E)*(P.expect f)^2 := by
  have hn (h : E → Fin N) := indexedExtraAverage_nonneg P s N f hf X h
  calc
    _ ≤ (∑h : E → Fin N,indexedExtraAverage P s N f X h)^2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun h _ => hn h)
    _ ≤ (((2^s:ℕ):ℝ)^(Fintype.card E)*P.expect f)^2 := by
      apply pow_le_pow_left₀ (Finset.sum_nonneg (fun h _ => hn h))
      exact indexedExtraAverage_sum P s N f hf X
    _ = _ := by rw [mul_pow,←pow_mul]; congr 2; omega
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open OccupiedParityTree

/-- Node-wise assembly of genuine edge labels. -/
def OccupiedParityTree.Labels.node (T : ℕ → ℕ) {b k : ℕ}
    {children : Fin k → OccupiedParityTree b} {roles : Fin k → Fin 3}
    (h : Fin k → Fin (T b)) (z : (i : Fin k) → (children i).Labels T) :
    (OccupiedParityTree.node k children roles).Labels T :=
  fun e => match e with
  | Sum.inl i => h i
  | Sum.inr q => z q.1 q.2

/-- The real numeric labels of the selected occupied configuration. -/
def occupiedTermLabels (T : ℕ → ℕ) : (b : ℕ) →
    (S : Finset (WindowLeaf T (b+1))) → (a : OccupiedWindowChoice T b S) →
      (occupiedWindowTerm T b S a).Labels T
  | 0, S, _ => Labels.node T (fun i => (S.equivFin.symm i).val.1) (fun _ e => e.elim)
  | b+1, S, a => Labels.node T (fun i => ((selectedChildren S).equivFin.symm i).val)
      (fun i => occupiedTermLabels T b
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i))

theorem occupiedTermLabels_forced (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced) :
    F.labels T (occupiedTermLabels T b S a)=forcedWindowLabels T b S a F := by
  induction b with
  | zero =>
    cases F with
    | node i j hne hi hj left right => cases left; cases right; rfl
  | succ b ih =>
    rcases a with ⟨u,r⟩
    cases F with
    | node i j hne hi hj left right =>
      change
        (((selectedChildren S).equivFin.symm i).val,
         ((selectedChildren S).equivFin.symm j).val,
         left.labels T (occupiedTermLabels T b (selectedChildLeaves S
           ((selectedChildren S).equivFin.symm i).val) (u i)),
         right.labels T (occupiedTermLabels T b (selectedChildLeaves S
           ((selectedChildren S).equivFin.symm j).val) (u j))) =
        (((selectedChildren S).equivFin.symm i).val,
         ((selectedChildren S).equivFin.symm j).val,
         forcedWindowLabels T b (selectedChildLeaves S
           ((selectedChildren S).equivFin.symm i).val) (u i) left,
         forcedWindowLabels T b (selectedChildLeaves S
           ((selectedChildren S).equivFin.symm j).val) (u j) right)
      exact congrArg (fun z => (((selectedChildren S).equivFin.symm i).val,
        ((selectedChildren S).equivFin.symm j).val,z)) (Prod.ext (ih _ _ left) (ih _ _ right))

namespace OccupiedParityTree
/-- Reading the set of leaf addresses from a shape and numeric edge labels.
Repeated or unordered coordinates are allowed; the true encoding is a
particular subset of this unrestricted label domain. -/
def labelledLeaves (T : ℕ → ℕ) : {b : ℕ} → (t : OccupiedParityTree b) →
    t.Labels T → Finset (WindowLeaf T b)
  | 0, .leaf, _ => {(⟨0,by decide⟩ : Fin 1)}
  | b+1, .node n children roles, x => Finset.univ.biUnion fun i : Fin n =>
      ((children i).labelledLeaves T (x.child T i)).image (fun v => (x (Sum.inl i),v))
end OccupiedParityTree

theorem mem_selectedChildLeaves {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α×β)) (h : α) (v : β) : v∈selectedChildLeaves S h ↔ (h,v)∈S := by
  constructor
  · intro hm
    obtain ⟨w,hw,hv⟩ := Finset.mem_image.mp hm
    have he : w=(h,v) := Prod.ext (Finset.mem_filter.mp hw).2 hv
    exact he ▸ (Finset.mem_filter.mp hw).1
  · intro hm
    exact Finset.mem_image.mpr ⟨(h,v),Finset.mem_filter.mpr ⟨hm,rfl⟩,rfl⟩

theorem occupiedTermLabels_leaves (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) :
    (occupiedWindowTerm T b S a).labelledLeaves T (occupiedTermLabels T b S a)=S := by
  induction b with
  | zero =>
    ext v
    constructor
    · intro hv
      obtain ⟨i,hi,hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨w,hw,hvw⟩ := Finset.mem_image.mp hv
      have he : (S.equivFin.symm i).val=v := by
        apply Prod.ext
        · change (occupiedTermLabels T 0 S a (Sum.inl i)) = v.1
          have hfst := congrArg (Prod.fst : Fin (T 0) × Fin 1 → Fin (T 0)) hvw
          exact hfst
        · exact Subsingleton.elim (α := Fin 1) _ _
      exact he ▸ (S.equivFin.symm i).property
    · intro hv
      let i := S.equivFin ⟨v,hv⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨(⟨0,by decide⟩ : Fin 1),Finset.mem_singleton_self _,?_⟩
      change ((S.equivFin.symm i).val.1,(⟨0,by decide⟩ : Fin 1))=v
      have he : (S.equivFin.symm i).val=v := congrArg Subtype.val (S.equivFin.symm_apply_apply _)
      apply Prod.ext
      · change (S.equivFin.symm i).val.1=v.1
        exact congrArg (Prod.fst : Fin (T 0) × Fin 1 → Fin (T 0)) he
      · exact Subsingleton.elim (α := Fin 1) _ _
  | succ b ih =>
    rcases a with ⟨u,r⟩
    simp only [occupiedWindowTerm, labelledLeaves, occupiedTermLabels, Labels.node]
    have hc (i : Fin (selectedChildren S).card) :
        (Labels.node T (roles := r) (fun i => ((selectedChildren S).equivFin.symm i).val)
          (fun i => occupiedTermLabels T b (selectedChildLeaves S
            ((selectedChildren S).equivFin.symm i).val) (u i))).child T i =
        occupiedTermLabels T b (selectedChildLeaves S
            ((selectedChildren S).equivFin.symm i).val) (u i) := by rfl
    simp_rw [hc,ih]
    ext v
    constructor
    · intro hv
      obtain ⟨i,hi,hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      exact (mem_selectedChildLeaves _ _ _).mp hw
    · intro hv
      have hc : v.1∈selectedChildren S := Finset.mem_image.mpr ⟨v,hv,rfl⟩
      let i := (selectedChildren S).equivFin ⟨v.1,hc⟩
      have he : ((selectedChildren S).equivFin.symm i).val=v.1 :=
        congrArg Subtype.val ((selectedChildren S).equivFin.symm_apply_apply _)
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨v.2,?_,?_⟩
      · rw [he]
        exact (mem_selectedChildLeaves _ _ _).mpr hv
      · exact Prod.ext he rfl

/-- The shape remembers all the role choices once the actual selected set
is fixed. -/
theorem occupiedWindowTerm_injective (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) : Function.Injective (occupiedWindowTerm T b S) := by
  induction b with
  | zero =>
    intro a c h
    exact eq_of_heq (OccupiedParityTree.node.inj h).2.2
  | succ b ih =>
    intro a c h
    apply Prod.ext
    · funext i
      exact ih _ ((congrFun (eq_of_heq (OccupiedParityTree.node.inj h).2.1) i))
    · exact eq_of_heq (OccupiedParityTree.node.inj h).2.2

/-- Unrestricted shape/label space really covers the coefficient index
without multiplicity. -/
def occupiedTermEncoding (T : ℕ → ℕ) (b : ℕ)
    (w : (S : Finset (WindowLeaf T (b+1))) × OccupiedWindowChoice T b S) :
    (t : OccupiedParityTree (b+1)) × t.Labels T :=
  ⟨occupiedWindowTerm T b w.1 w.2,occupiedTermLabels T b w.1 w.2⟩

theorem occupiedTermEncoding_injective (T : ℕ → ℕ) (b : ℕ) :
    Function.Injective (occupiedTermEncoding T b) := by
  intro w v he
  have hS := congrArg (fun z : (t : OccupiedParityTree (b+1)) × t.Labels T =>
    z.1.labelledLeaves T z.2) he
  change (occupiedWindowTerm T b w.1 w.2).labelledLeaves T (occupiedTermLabels T b w.1 w.2)=
    (occupiedWindowTerm T b v.1 v.2).labelledLeaves T (occupiedTermLabels T b v.1 v.2) at hS
  simp only [occupiedTermLabels_leaves] at hS
  cases w with
  | mk S a =>
    cases v with
    | mk V c =>
      dsimp only at hS
      subst V
      have ht := congrArg Sigma.fst he
      have ha := occupiedWindowTerm_injective T b S ht
      change a=c at ha
      subst c
      rfl
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

noncomputable def Forced.edgeEquiv {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    BinaryEdge b ⊕ F.ExtraEdge ≃ t.Edge := by
  classical
  letI : DecidablePred (Set.range F.edge) := fun _ => Classical.propDecidable _
  exact (Equiv.sumCongr (Equiv.ofInjective F.edge F.edge_injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (Set.range F.edge))

def binaryEdgeCount (b h : ℕ) : ℕ := Fintype.card {e : BinaryEdge b // e.height=h}

theorem BinaryEdge.height_lt {b : ℕ} (e : BinaryEdge b) : e.height<b := by
  induction b with
  | zero => exact e.elim
  | succ b ih =>
    cases e with
    | inl i => exact Nat.lt_succ_self _
    | inr z => exact Nat.lt_succ_of_lt (ih z.2)

theorem binaryEdgeCount_outside (b h : ℕ) (hh : b≤h) : binaryEdgeCount b h=0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun e => ?_⟩
  have hc := e.val.height_lt
  rw [e.property] at hc
  omega

theorem binaryEdgeCount_succ (b h : ℕ) :
    binaryEdgeCount (b+1) h = (if b=h then 2 else 0)+2*binaryEdgeCount b h := by
  unfold binaryEdgeCount
  simp only [Fintype.card_subtype,Finset.card_filter]
  change (∑e : Bool ⊕ (Bool × BinaryEdge b), if BinaryEdge.height (b:=b+1) e=h then 1 else 0)=_
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  by_cases hb : b=h <;> simp [BinaryEdge.height,hb,two_mul] <;> simp only [Finset.card_filter] <;> rfl

theorem binaryEdgeCount_eq (b h : ℕ) (hh : h<b) : binaryEdgeCount b h=2^(b-h) := by
  induction b with
  | zero => omega
  | succ b ih =>
    rw [binaryEdgeCount_succ]
    by_cases he : b=h
    · subst h
      rw [ite_eq_left rfl,binaryEdgeCount_outside b b le_rfl]
      simp
    · rw [ite_eq_right he,zero_add,ih (by omega)]
      have hsub : b+1-h=(b-h)+1 := by omega
      rw [hsub,pow_succ,Nat.mul_comm]

def Forced.extraCount {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) (h : ℕ) : ℕ :=
  Fintype.card {e : F.ExtraEdge // e.val.height=h}

theorem Forced.count_partition {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) (h : ℕ) :
    F.extraCount h+binaryEdgeCount b h=t.edgeCount h := by
  have he := F.edgeEquiv.sum_comp (fun e : t.Edge => if e.height=h then (1:ℕ) else 0)
  rw [Fintype.sum_sum_type] at he
  change (∑e : BinaryEdge b, if (F.edge e).height=h then 1 else 0)+
    (∑e : F.ExtraEdge, if e.val.height=h then 1 else 0) =
      (∑e : t.Edge, if e.height=h then 1 else 0) at he
  simp_rw [F.edge_height] at he
  unfold Forced.extraCount binaryEdgeCount edgeCount
  simp only [Fintype.card_subtype,Finset.card_filter]
  omega

theorem levelCount_bottom {b : ℕ} (t : OccupiedParityTree b) : t.levelCount b=t.leafCount := by
  induction t with
  | leaf => rfl
  | node n children roles ih => exact Finset.sum_congr rfl (fun i _ => ih i)

/-- The extra bottom coordinates are precisely r-2^b, including the empty
height-zero case. -/
theorem Forced.card_extraLeafEdge {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    Fintype.card F.ExtraLeafEdge=t.leafCount-2^b := by
  cases b with
  | zero =>
    cases t
    change F.extraCount 0 = _
    have h := F.count_partition 0
    rw [edgeCount_leaf] at h
    simp only [leafCount,pow_zero,Nat.sub_self]
    omega
  | succ b =>
    change F.extraCount 0 = _
    have h := F.count_partition 0
    rw [binaryEdgeCount_eq (b+1) 0 (by omega),edgeCount_level t 0 (by omega)] at h
    simp only [Nat.sub_zero,levelCount_bottom] at h
    omega

/-- Exact source nonforced vertex bound, now for genuine extra edge-label
coordinates rather than an abstract level-count surrogate. -/
theorem Forced.extraCount_le {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (ht : t.occupied) (h : ℕ) : F.extraCount h≤t.leafCount-2^b := by
  by_cases hh : h<b
  · have hp := F.count_partition h
    rw [binaryEdgeCount_eq b h hh,edgeCount_level t h hh] at hp
    have Hb := F.nonforced_vertices_le_extra_leaves ht (b-h)
    omega
  · have hp := F.count_partition h
    rw [edgeCount_outside t h (by omega)] at hp
    omega

/-- Extra nonleaf numeric labels grouped by their actual child height. -/
def Forced.interiorHeight {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (e : F.ExtraInteriorEdge) : Fin b := ⟨e.val.val.height,e.val.val.height_lt⟩

theorem Forced.interiorFiber_le {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (ht : t.occupied) (h : Fin b) :
    Fintype.card {e : F.ExtraInteriorEdge // F.interiorHeight e=h} ≤ t.leafCount-2^b := by
  apply le_trans _ (F.extraCount_le ht h.val)
  let f : {e : F.ExtraInteriorEdge // F.interiorHeight e=h} →
      {e : F.ExtraEdge // e.val.height=h.val} := fun e =>
    ⟨e.val.val,congrArg Fin.val e.property⟩
  apply Fintype.card_le_of_injective f
  intro u v he
  have he' : u.val.val=v.val.val := congrArg
    (fun q : {e : F.ExtraEdge // e.val.height=h.val} => q.val) he
  exact Subtype.ext (Subtype.ext he')

theorem Forced.card_interiorLabels_le (T : ℕ → ℕ) (hT : ∀j,0<T j)
    {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) (ht : t.occupied) :
    Fintype.card (F.InteriorLabels T) ≤
      (∏j : Fin b,if j.val=0 then 1 else T j.val)^(t.leafCount-2^b) := by
  change Fintype.card ((e : F.ExtraInteriorEdge) → Fin (T e.val.val.height)) ≤ _
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  have hp := Fintype.prod_fiberwise' F.interiorHeight (fun j : Fin b => T j.val)
  change (∏j : Fin b, ∏_e : {e : F.ExtraInteriorEdge // F.interiorHeight e=j}, T j.val) =
    ∏e : F.ExtraInteriorEdge,T e.val.val.height at hp
  rw [←hp]
  simp only [Finset.prod_const,Finset.card_univ]
  rw [←Finset.prod_pow]
  apply Finset.prod_le_prod
  intro j hj
  by_cases hz : j.val=0
  · have he : Fintype.card {e : F.ExtraInteriorEdge // F.interiorHeight e=j}=0 := by
      apply Fintype.card_eq_zero_iff.mpr
      refine ⟨fun e => ?_⟩
      exact e.val.property ((congrArg Fin.val e.property).trans hz)
    rw [he,ite_eq_left hz,pow_zero,one_pow]
  · rw [ite_eq_right hz]
    exact Nat.pow_le_pow_right (hT j.val) (F.interiorFiber_le ht j)

end OccupiedParityTree
end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
