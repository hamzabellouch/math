import Mathlib
import OAI.Algebra.GroupRing.Attachment

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Attachment

section
open Set Metric Topology
universe u v w z
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι : Type w} {κ : Type z} {n : ℕ}
variable (a : ι → C(Sphere n,X)) (b : κ → C(Sphere n,Y))

def map (p : C(X,Y)) (σ : ι → κ) (h : ∀ i x, p (a i x) = b (σ i) x) :
    C(Space a,Space b) :=
  lift a ⟨base b ∘ p,(continuous_base b).comp p.continuous⟩
    (fun i => cell b (σ i)) (fun i x => by simp only [cell_boundary,ContinuousMap.coe_mk,Function.comp_apply,h])

@[simp] lemma map_base (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x) (x : X) :
    map a b p σ h (base a x) = base b (p x) := rfl

@[simp] lemma map_cell (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x) (i : ι) (d : Disk n) :
    map a b p σ h (cell a i d) = cell b (σ i) d := lift_cell a _ _ _ i d

@[simp] lemma map_openCell (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x) (i : ι) (d : OpenDisk n) :
    map a b p σ h (openCell a i d) = openCell b (σ i) d := by
  change map a b p σ h (Sum.inr ⟨i,d⟩) = Sum.inr ⟨σ i,d⟩
  rw [← cell_interior a i d,map_cell,cell_interior]

lemma map_surjective (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x)
    (hp : Function.Surjective p) (hσ : Function.Surjective σ) :
    Function.Surjective (map a b p σ h) := by
  intro z
  cases z with
  | inl y =>
    obtain ⟨x,rfl⟩ := hp y
    exact ⟨base a x,rfl⟩
  | inr q =>
    obtain ⟨i,hi⟩ := hσ q.1
    exact ⟨openCell a i q.2,by rw [map_openCell,hi]; rfl⟩

lemma map_isQuotientMap (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x)
    (hp : IsQuotientMap p) (hσ : Function.Surjective σ) :
    IsQuotientMap (map a b p σ h) := by
  refine ⟨?_,map_surjective a b p σ h hp.surjective hσ⟩
  rw [isCoinducing_iff]
  intro U
  constructor
  · intro hU
    rw [isOpen_iff] at hU ⊢
    constructor
    · apply hp.isOpen_preimage.mp
      exact hU.1
    · intro j
      obtain ⟨i,rfl⟩ := hσ j
      convert hU.2 i using 1
      ext d
      simp only [Set.mem_preimage,map_cell]
  · exact fun hU => hU.preimage (map a b p σ h).continuous

end

open Set Metric Topology
universe u v w z

def FreeIndex (G : Type u) (ι : Type v) := G × ι

instance {G : Type u} [Group G] {ι : Type v} : MulAction G (FreeIndex G ι) where
  smul g p := (g * p.1,p.2)
  one_smul p := by change ((1:G)*p.1,p.2)=p; simp only [one_mul]; rfl
  mul_smul g h p := by change ((g*h)*p.1,p.2)=(g*(h*p.1),p.2); rw [mul_assoc]

instance {G : Type u} [Group G] {ι : Type v} : IsCancelSMul G (FreeIndex G ι) where
  right_cancel' _ _ _ he := mul_right_cancel (congrArg (fun p : FreeIndex G ι => p.1) he)

variable {G : Type u} [Group G]
variable {E : Type v} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]
variable {X : Type w} [TopologicalSpace X] {ι : Type z} {n : ℕ}
variable (a : ι → C(Sphere n,E))

def equivariantFamily : FreeIndex G ι → C(Sphere n,E) :=
  fun i => ⟨fun x => i.1 • a i.2 x,(continuous_const_smul i.1).comp (a i.2).continuous⟩

lemma equivariantFamily_smul (g : G) (i : FreeIndex G ι) (x : Sphere n) :
    equivariantFamily (G := G) a (g • i) x = g • equivariantFamily a i x := mul_smul g i.1 _

instance equivariantAttachmentContinuousAction :
    ContinuousConstSMul G (Space (equivariantFamily (G := G) a)) :=
  continuousConstSMul _ (equivariantFamily_smul a)

variable (p : C(E,X)) (hp : IsQuotientCoveringMap p G)
variable (b : ι → C(Sphere n,X)) (h : ∀ i x, p (a i x) = b i x)

include hp h in
lemma equivariantFamily_over (i : FreeIndex G ι) (x : Sphere n) :
    p (equivariantFamily (G := G) a i x) = b i.2 x :=
  (hp.map_smul i.1).trans (h i.2 x)

def coverMap : C(Space (equivariantFamily (G := G) a),Space b) :=
  map _ b p Prod.snd (equivariantFamily_over a p hp b h)

lemma coverMap_isQuotient : IsQuotientMap (coverMap a p hp b h) :=
  map_isQuotientMap _ b p Prod.snd _ hp.toIsQuotientMap (fun i => ⟨(1,i),rfl⟩)

lemma coverMap_fibers {e₁ e₂ : Space (equivariantFamily (G := G) a)} :
    coverMap a p hp b h e₁ = coverMap a p hp b h e₂ ↔ e₁ ∈ MulAction.orbit G e₂ := by
  classical
  cases e₁ with
  | inl x =>
    cases e₂ with
    | inl y =>
      change Sum.inl (p x) = Sum.inl (p y) ↔ _
      rw [Sum.inl.injEq,hp.apply_eq_iff_mem_orbit]
      constructor
      · rintro ⟨g,hg⟩; exact ⟨g,congrArg Sum.inl hg⟩
      · rintro ⟨g,hg⟩; exact ⟨g,Sum.inl_injective hg⟩
    | inr q =>
      constructor
      · intro hh
        change base b (p x) = map _ b p Prod.snd _ (openCell _ q.1 q.2) at hh
        erw [map_openCell] at hh
        cases hh
      · rintro ⟨g,hg⟩; cases hg
  | inr q =>
    cases e₂ with
    | inl y =>
      constructor
      · intro hh
        change map _ b p Prod.snd _ (openCell _ q.1 q.2) = base b (p y) at hh
        erw [map_openCell] at hh
        cases hh
      · rintro ⟨g,hg⟩; cases hg
    | inr r =>
      change map _ b p Prod.snd _ (openCell _ q.1 q.2) =
        map _ b p Prod.snd _ (openCell _ r.1 r.2) ↔ _
      erw [map_openCell,map_openCell]
      constructor
      · intro hh
        have hi : q.1.2 = r.1.2 := congrArg Sigma.fst (Sum.inr_injective hh)
        have hd : q.2 = r.2 := congrArg (fun p : Σ _ : ι, OpenDisk n => p.2) (Sum.inr_injective hh)
        refine ⟨q.1.1 * r.1.1⁻¹,?_⟩
        change Sum.inr ⟨((q.1.1 * r.1.1⁻¹) * r.1.1,r.1.2),r.2⟩ = Sum.inr q
        simp only [inv_mul_cancel_right,← hi,← hd]
        rfl
      · rintro ⟨g,hg⟩
        change (Sum.inr ⟨g • r.1,r.2⟩ : Space (equivariantFamily (G := G) a)) = Sum.inr q at hg
        have hi : (g • r.1) = q.1 := congrArg Sigma.fst (Sum.inr_injective hg)
        have htuple : (⟨g • r.1,r.2⟩ : Σ _ : FreeIndex G ι, OpenDisk n) = q := Sum.inr_injective hg
        have hd' := congrArg (fun p : Σ _ : FreeIndex G ι, OpenDisk n => p.2) htuple
        have hd : r.2 = q.2 := hd' 
        have his' := congrArg (fun p : FreeIndex G ι => p.2) hi
        have his : r.1.2 = q.1.2 := his'
        change (Sum.inr ⟨q.1.2,q.2⟩ : Space b) = Sum.inr ⟨r.1.2,r.2⟩
        rw [his,hd]

/-- Free, equivariant cell attachments preserve a genuine regular covering.
The proof constructs collars of disjoint slices; no local-finiteness or
local-compactness hypothesis is imposed. -/
lemma coverMap_isQuotientCovering : IsQuotientCoveringMap (coverMap a p hp b h) G where
  __ := coverMap_isQuotient a p hp b h
  __ := equivariantAttachmentContinuousAction a
  apply_eq_iff_mem_orbit := coverMap_fibers a p hp b h
  disjoint := exists_disjoint_nhds _ (equivariantFamily_smul a) hp.disjoint

lemma coverMap_isCovering : IsCoveringMap (coverMap a p hp b h) :=
  (coverMap_isQuotientCovering a p hp b h).isCoveringMap

end GroupRingTopology.Attachment

namespace GroupRingTopology.Cayley
open Set Metric Topology Attachment
universe u

lemma sphere_one_cases (x : Sphere 1) : x.1 0 = -1 ∨ x.1 0 = 1 := by
  have hn : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
  have hc : x.1 = fun _ => x.1 0 := funext (fun i => congrArg x.1 (Subsingleton.elim i 0))
  rw [hc,pi_norm_const,Real.norm_eq_abs] at hn
  exact ((abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hn).symm

instance : Finite (Sphere 1) := by
  have he : {r : ℝ | r = -1 ∨ r = 1} = {-1,1} := by ext r; simp
  have hS : Set.Finite {r : ℝ | r = -1 ∨ r = 1} := he.symm ▸ ((Set.finite_singleton (1 : ℝ)).insert (-1))
  let : Finite {r : ℝ // r = -1 ∨ r = 1} := hS.to_subtype
  apply Finite.of_injective (fun x : Sphere 1 => (⟨x.1 0,sphere_one_cases x⟩ :
    {r : ℝ // r = -1 ∨ r = 1}))
  intro x y h
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [hi] using congrArg Subtype.val h

instance : DiscreteTopology (Sphere 1) := inferInstance

def minus : Sphere 1 := ⟨fun _ => -1,by norm_num [mem_sphere,dist_pi_def]⟩
def plus : Sphere 1 := ⟨fun _ => 1,by norm_num [mem_sphere,dist_pi_def]⟩

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

def attaching (i : S) : C(Sphere 1,G) :=
  ⟨fun x => if x.1 0 = -1 then 1 else s i,continuous_of_discreteTopology⟩

abbrev Graph := Space (equivariantFamily (G := G) (attaching s))

instance : Nonempty (Graph s) := ⟨base _ 1⟩

def vertex (g : G) : Graph s := base _ g

omit [Group G] in
lemma discrete_dimension (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set G) m) : m < 1 := by
  cases m with
  | zero => omega
  | succ m => exact i.elim

instance graphCW : CWComplex (Set.univ : Set (Graph s)) :=
  layerCW _ discrete_dimension

instance : T2Space (Graph s) :=
  t2Space _ ((realSeparated_of_tychonoff (Y := G)))

lemma graph_dimension (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set (Graph s)) m) : m < 2 :=
  layerCW_dimensions _ discrete_dimension m i

lemma vertex_injective : Function.Injective (vertex s) := Sum.inl_injective

lemma cell_minus (g : G) (i : S) :
    cell (equivariantFamily (G := G) (attaching s)) (g,i) (boundary 1 minus) = vertex s g := by
  erw [cell_boundary]
  simp only [equivariantFamily,attaching,ContinuousMap.coe_mk,minus,ite_true,smul_eq_mul,mul_one]
  rfl

lemma cell_plus (g : G) (i : S) :
    cell (equivariantFamily (G := G) (attaching s)) (g,i) (boundary 1 plus) = vertex s (g*s i) := by
  erw [cell_boundary]
  norm_num only [equivariantFamily,attaching,ContinuousMap.coe_mk,plus,ite_false,smul_eq_mul]
  rfl

instance disk_pathConnected (n : ℕ) : PathConnectedSpace (Disk n) :=
  isPathConnected_iff_pathConnectedSpace.mp ((convex_closedBall (0 : Fin n → ℝ) 1).isPathConnected ⟨0,mem_closedBall_self (by norm_num)⟩)

lemma cell_joined (g : G) (i : S) : Joined (vertex s g) (vertex s (g*s i)) := by
  have h : Joined (boundary 1 minus) (boundary 1 plus) := PathConnectedSpace.joined _ _
  have hh := h.map (cell (equivariantFamily (G := G) (attaching s)) (g,i)).continuous
  simpa only [cell_minus,cell_plus] using hh

lemma vertex_smul (g h : G) : g • vertex s h = vertex s (g*h) := rfl

lemma vertices_joined (hs : Subgroup.closure (Set.range s) = ⊤) (g : G) :
    Joined (vertex s 1) (vertex s g) := by
  let K : Subgroup G :=
    { carrier := {g | Joined (vertex s 1) (vertex s g)}
      one_mem' := Joined.refl _
      mul_mem' := by
        intro g h hg hh
        have hh' := hh.map (continuous_const_smul g : Continuous (fun x : Graph s => g • x))
        rw [vertex_smul,vertex_smul,mul_one] at hh'
        exact hg.trans hh'
      inv_mem' := by
        intro g hg
        have hh := hg.symm.map (continuous_const_smul g⁻¹ : Continuous (fun x : Graph s => g⁻¹ • x))
        change Joined (vertex s 1) (vertex s g⁻¹)
        simpa only [vertex_smul,mul_one,inv_mul_cancel] using hh }
  have hK : Subgroup.closure (Set.range s) ≤ K := (Subgroup.closure_le K).2 (by
    rintro _ ⟨i,rfl⟩
    change Joined (vertex s 1) (vertex s (s i))
    simpa only [one_mul] using cell_joined s 1 i)
  rw [hs] at hK
  exact hK (Subgroup.mem_top g)

lemma graph_pathConnected (hs : Subgroup.closure (Set.range s) = ⊤) : PathConnectedSpace (Graph s) := by
  have hj : ∀ x : Graph s, Joined (vertex s 1) x := by
    intro x
    cases x with
    | inl g => exact vertices_joined s hs g
    | inr p =>
      have h : Joined (boundary 1 minus) (interior 1 p.2) := PathConnectedSpace.joined _ _
      have hh := h.map (cell (equivariantFamily (G := G) (attaching s)) p.1).continuous
      rw [cell_interior] at hh
      have hp : cell (equivariantFamily (G := G) (attaching s)) p.1 (boundary 1 minus) = vertex s p.1.1 :=
        cell_minus s p.1.1 p.1.2
      rw [hp] at hh
      exact (vertices_joined s hs p.1.1).trans hh
  exact ⟨inferInstance,fun x y => (hj x).symm.trans (hj y)⟩

end GroupRingTopology.Cayley

namespace GroupRingTopology.PathSquares
open Set
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X] {x a b : X}

lemma turn (p : Path x a) (q : Path x b) (e : Path a b)
    (h : (p.trans e).Homotopic q) : e.Homotopic (p.symm.trans q) := by
  apply (Path.Homotopic.refl_trans e).symm.trans
  apply ((Path.Homotopic.symm_trans p).symm.hcomp (Path.Homotopic.refl e)).trans
  exact (Path.Homotopic.trans_assoc p.symm p e).trans ((Path.Homotopic.refl p.symm).hcomp h)

def spanContract (p : Path x a) (q : Path x b) :
    (p.symm.trans q).toContinuousMap.Homotopy (.const _ x) where
  toFun z := if (z.2 : ℝ) ≤ 1/2 then p.extend ((1-z.1)*(1-2*z.2))
    else q.extend ((1-z.1)*(2*z.2-1))
  continuous_toFun := continuous_if_le (by fun_prop) continuous_const
    (by fun_prop) (by fun_prop) (by intro z hz; simp [hz])
  map_zero_left z := by simp [Path.trans,Path.extend_symm_apply]
  map_one_left z := by simp

lemma spanContract_source (p : Path x a) (q : Path x b) (t : I) :
    spanContract p q (t,0) = p.symm t := by
  change (if (0 : ℝ) ≤ 1/2 then p.extend ((1-(t:ℝ))*(1-2*0)) else q.extend ((1-(t:ℝ))*(2*0-1))) = _
  norm_num only [show (0:ℝ)≤1/2 by norm_num,ite_true,mul_zero,sub_zero,mul_one]
  rw [← Path.extend_symm_apply,Path.extend_extends' ]
lemma spanContract_target (p : Path x a) (q : Path x b) (t : I) :
    spanContract p q (t,1) = q.symm t := by
  change (if (1 : ℝ) ≤ 1/2 then p.extend ((1-(t:ℝ))*(1-2*1)) else q.extend ((1-(t:ℝ))*(2*1-1))) = _
  norm_num only [mul_one,show (2:ℝ)-1=1 by norm_num,show ¬(1:ℝ)≤1/2 by norm_num,ite_false]
  rw [← Path.extend_symm_apply,Path.extend_extends' ]

def pauseReverse (p : Path x a) : C(I,X) := ((Path.refl a).trans p.symm).toContinuousMap

/-- Compatible vertex paths fill every edge square, without any path-word
approximation assertion. The pause at the vertex is the same for every edge. -/
theorem edgeSquare (p : Path x a) (q : Path x b) (e : Path a b)
    (h : (p.trans e).Homotopic q) :
    ∃ H : e.toContinuousMap.Homotopy (.const _ x),
      (∀ t, H (t,0) = pauseReverse p t) ∧ (∀ t, H (t,1) = pauseReverse q t) := by
  obtain ⟨A⟩ := turn p q e h
  refine ⟨A.toHomotopy.trans (spanContract p q),?_,?_⟩
  · intro t
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · change (t:ℝ) ≤ 1/2 at ht
      change A (_,0) = ((Path.refl a).trans p.symm) t
      rw [Path.trans_apply,dite_eq_left ht]
      exact A.source _
    · change ¬(t:ℝ) ≤ 1/2 at ht
      change spanContract p q (_,0) = ((Path.refl a).trans p.symm) t
      rw [Path.trans_apply,dite_eq_right ht,spanContract_source]
  · intro t
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · change (t:ℝ) ≤ 1/2 at ht
      change A (_,1) = ((Path.refl b).trans q.symm) t
      rw [Path.trans_apply,dite_eq_left ht]
      exact A.target _
    · change ¬(t:ℝ) ≤ 1/2 at ht
      change spanContract p q (_,1) = ((Path.refl b).trans q.symm) t
      rw [Path.trans_apply,dite_eq_right ht,spanContract_target]
end GroupRingTopology.PathSquares
namespace GroupRingTopology.Cayley
open Set Metric Topology Attachment
open scoped unitInterval
universe u v

def edgeParam (t : I) : Disk 1 := ⟨fun _ => 2*(t:ℝ)-1,by
  rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs,abs_le]
  constructor <;> linarith [t.2.1,t.2.2]⟩
lemma continuous_edgeParam : Continuous edgeParam := by unfold edgeParam; fun_prop

def edgeTime (d : Disk 1) : I := ⟨(d.1 0+1)/2,by
  have hh : |d.1 0| ≤ 1 := by
    have := d.2
    rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg zero_le_one] at this
    exact this 0
  rw [abs_le] at hh
  constructor <;> linarith⟩
lemma continuous_edgeTime : Continuous edgeTime := by
  apply Continuous.subtype_mk
  exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2
lemma edgeParam_time (d : Disk 1) : edgeParam (edgeTime d) = d := by
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  dsimp [edgeParam,edgeTime]
  ring
lemma edgeTime_param (t : I) : edgeTime (edgeParam t) = t := by
  apply Subtype.ext
  dsimp [edgeTime,edgeParam]
  ring
lemma edgeParam_zero : edgeParam 0 = boundary 1 minus := by
  apply Subtype.ext
  funext i
  norm_num [edgeParam,minus,boundary]
lemma edgeParam_one : edgeParam 1 = boundary 1 plus := by
  apply Subtype.ext
  funext i
  norm_num [edgeParam,plus,boundary]
lemma edgeTime_minus : edgeTime (boundary 1 minus) = 0 := by
  rw [←edgeParam_zero,edgeTime_param]
lemma edgeTime_plus : edgeTime (boundary 1 plus) = 1 := by
  rw [←edgeParam_one,edgeTime_param]
lemma sphere_one_eq (t : Sphere 1) : t = minus ∨ t = plus := by
  obtain h|h := sphere_one_cases t
  · left; apply Subtype.ext; funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; exact h
  · right; apply Subtype.ext; funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; exact h

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

def edge (g : G) (i : S) : Path (vertex s g) (vertex s (g*s i)) where
  toFun t := cell (equivariantFamily (G := G) (attaching s)) (g,i) (edgeParam t)
  continuous_toFun := (cell _ _).continuous.comp continuous_edgeParam
  source' := by rw [edgeParam_zero,cell_minus]
  target' := by rw [edgeParam_one,cell_plus]

variable {Y : Type v} [TopologicalSpace Y] (f : C(Graph s,Y)) (y : Y)
variable (p : ∀ g, Path y (f (vertex s g)))
variable (hp : ∀ g i, ((p g).trans ((edge s g i).map f.continuous)).Homotopic (p (g*s i)))

def edgeSquare (g : G) (i : S) : ((edge s g i).map f.continuous).toContinuousMap.Homotopy (.const _ y) :=
  (PathSquares.edgeSquare (p g) (p (g*s i)) ((edge s g i).map f.continuous) (hp g i)).choose
lemma edgeSquare_source (g : G) (i : S) (t : I) :
    edgeSquare s f y p hp g i (t,0) = PathSquares.pauseReverse (p g) t :=
  (PathSquares.edgeSquare (p g) (p (g*s i)) ((edge s g i).map f.continuous) (hp g i)).choose_spec.1 t
lemma edgeSquare_target (g : G) (i : S) (t : I) :
    edgeSquare s f y p hp g i (t,1) = PathSquares.pauseReverse (p (g*s i)) t :=
  (PathSquares.edgeSquare (p g) (p (g*s i)) ((edge s g i).map f.continuous) (hp g i)).choose_spec.2 t

def edgePaths (i : FreeIndex G S) : C(Disk 1,C(I,Y)) :=
  ContinuousMap.curry ⟨fun z => edgeSquare s f y p hp i.1 i.2 (z.2,edgeTime z.1),
    (edgeSquare s f y p hp i.1 i.2).continuous.comp
      (continuous_snd.prodMk (continuous_edgeTime.comp continuous_fst))⟩
def vertexPaths : C(G,C(I,Y)) := ⟨fun g => PathSquares.pauseReverse (p g),continuous_of_discreteTopology⟩
lemma edgePaths_boundary (i : FreeIndex G S) (t : Sphere 1) :
    edgePaths s f y p hp i (boundary 1 t) =
      vertexPaths s f y p (equivariantFamily (G := G) (attaching s) i t) := by
  obtain rfl|rfl := sphere_one_eq t
  · apply ContinuousMap.ext; intro z
    change edgeSquare s f y p hp i.1 i.2 (z,edgeTime (boundary 1 minus)) = _
    rw [edgeTime_minus,edgeSquare_source]
    simp only [vertexPaths,equivariantFamily,attaching,ContinuousMap.coe_mk,minus,ite_true,smul_eq_mul,mul_one]
  · apply ContinuousMap.ext; intro z
    change edgeSquare s f y p hp i.1 i.2 (z,edgeTime (boundary 1 plus)) = _
    rw [edgeTime_plus,edgeSquare_target]
    norm_num [vertexPaths,equivariantFamily,attaching,plus]

def graphPaths : C(Graph s,C(I,Y)) :=
  lift _ (vertexPaths s f y p) (edgePaths s f y p hp) (edgePaths_boundary s f y p hp)

lemma graphPaths_zero (z : Graph s) : graphPaths s f y p hp z 0 = f z := by
  cases z with
  | inl g =>
    change PathSquares.pauseReverse (p g) 0 = _
    exact Path.source _
  | inr z =>
    change edgeSquare s f y p hp z.1.1 z.1.2 (0,edgeTime (interior 1 z.2)) = _
    rw [ContinuousMap.Homotopy.apply_zero]
    change f (cell _ z.1 (edgeParam (edgeTime (interior 1 z.2)))) = f _
    rw [edgeParam_time,cell_interior]
lemma graphPaths_one (z : Graph s) : graphPaths s f y p hp z 1 = y := by
  cases z with
  | inl g =>
    change PathSquares.pauseReverse (p g) 1 = y
    exact Path.target _
  | inr z =>
    change edgeSquare s f y p hp z.1.1 z.1.2 (1,edgeTime (interior 1 z.2)) = y
    exact ContinuousMap.Homotopy.apply_one _ _

/-- A coherent system of vertex paths contracts the entire graph map. -/
def graphNullhomotopy : f.Homotopy (.const _ y) where
  toFun z := graphPaths s f y p hp z.2 z.1
  continuous_toFun := (graphPaths s f y p hp).uncurry.continuous.comp continuous_swap
  map_zero_left := graphPaths_zero s f y p hp
  map_one_left := graphPaths_one s f y p hp
end GroupRingTopology.Cayley
open Set Metric Topology

end

end OAI
