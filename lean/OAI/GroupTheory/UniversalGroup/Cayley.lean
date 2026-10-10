import OAI.GroupTheory.UniversalGroup.CellularAttachment

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Cayley
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
  refine (cell_boundary (equivariantFamily (G := G) (attaching s)) (g,i) minus).trans ?_
  change base _ (g * attaching s i minus) = vertex s g
  simp only [attaching,ContinuousMap.coe_mk,minus,ite_true,mul_one]
  rfl

lemma cell_plus (g : G) (i : S) :
    cell (equivariantFamily (G := G) (attaching s)) (g,i) (boundary 1 plus) = vertex s (g*s i) := by
  refine (cell_boundary (equivariantFamily (G := G) (attaching s)) (g,i) plus).trans ?_
  change base _ (g * attaching s i plus) = vertex s (g * s i)
  norm_num only [attaching,ContinuousMap.coe_mk,plus,ite_false]
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

end UniversalFInfinity.Cayley

namespace UniversalFInfinity.PathSquares
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
end UniversalFInfinity.PathSquares
namespace UniversalFInfinity.Cayley
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

def graphNullhomotopy : f.Homotopy (.const _ y) where
  toFun z := graphPaths s f y p hp z.2 z.1
  continuous_toFun := (graphPaths s f y p hp).uncurry.continuous.comp continuous_swap
  map_zero_left := graphPaths_zero s f y p hp
  map_one_left := graphPaths_one s f y p hp
end UniversalFInfinity.Cayley
open Set Metric Topology

namespace UniversalFInfinity.Cellular
open Set Metric Topology
variable {Y : Type*} [TopologicalSpace Y]

theorem cylinderFill {n : ℕ} (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
    (h : ∀ x, pathEndpoint (a x) = b (boundary n x))
    (F : C(Disk (n+1),Y)) (hF : ∀ x, F (boundary (n+1) x) = cylinderBoundaryMap a b h x) :
    ∃ e : C(Disk n,C(unitInterval,Y)),
      (∀ x, e (boundary n x) = a x) ∧ (∀ x, pathEndpoint (e x) = b x) := by
  let e : C(Disk n,C(unitInterval,Y)) :=
    (F.comp ⟨fun q : Disk n × unitInterval => diskCons q.1 q.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x
    apply ContinuousMap.ext
    intro t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = a x t
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t)) = a x t
    rw [diskTime_cons]
    congr 1
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 0))).1 = (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 1))).2 = (b x).2
      rw [diskTail_cons]

end UniversalFInfinity.Cellular
namespace UniversalFInfinity.LoopSphere
open Set Metric Topology Cellular
open scoped unitInterval
universe u v
variable {X : Type u} [TopologicalSpace X] {x : X}

def sides : C(Sphere 1,C(I,X)) := .const _ (.const _ x)
def ends (p : Path x x) : C(Disk 1,X × X) :=
  ⟨fun d => (p (Cayley.edgeTime d),x),
    (p.continuous.comp Cayley.continuous_edgeTime).prodMk continuous_const⟩
lemma ends_sides (p : Path x x) (z : Sphere 1) :
    pathEndpoint (sides (x := x) z) = ends p (boundary 1 z) := by
  obtain rfl|rfl := Cayley.sphere_one_eq z
  · change (x,x) = (p (Cayley.edgeTime (Attachment.boundary 1 Cayley.minus)),x)
    rw [Cayley.edgeTime_minus,p.source]
  · change (x,x) = (p (Cayley.edgeTime (Attachment.boundary 1 Cayley.plus)),x)
    rw [Cayley.edgeTime_plus,p.target]

def map (p : Path x x) : C(Sphere 2,X) := cylinderBoundaryMap sides (ends p) (ends_sides p)

theorem homotopic_of_fill (p : Path x x) (F : C(Disk 2,X))
    (hF : ∀ z, F (boundary 2 z) = map p z) : p.Homotopic (Path.refl x) := by
  obtain ⟨e,he,hep⟩ := cylinderFill sides (ends p) (ends_sides p) F hF
  refine ⟨{
    toFun := fun z => e (Cayley.edgeParam z.2) z.1
    continuous_toFun := e.uncurry.continuous.comp
      ((Cayley.continuous_edgeParam.comp continuous_snd).prodMk continuous_fst)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    have h := congrArg Prod.fst (hep (Cayley.edgeParam t))
    change e (Cayley.edgeParam t) 0 = p t
    change e (Cayley.edgeParam t) 0 = p (Cayley.edgeTime (Cayley.edgeParam t)) at h
    simpa only [Cayley.edgeTime_param] using h
  · intro t
    exact congrArg Prod.snd (hep (Cayley.edgeParam t))
  · intro t q hq
    obtain rfl|hq := hq
    · change e (Cayley.edgeParam 0) t = p 0
      rw [Cayley.edgeParam_zero,p.source]
      exact ContinuousMap.congr_fun (he Cayley.minus) t
    · obtain rfl := Set.mem_singleton_iff.mp hq
      change e (Cayley.edgeParam 1) t = p 1
      rw [Cayley.edgeParam_one,p.target]
      exact ContinuousMap.congr_fun (he Cayley.plus) t

variable {Y : Type v} [TopologicalSpace Y]
lemma natural (p : Path x x) (f : C(X,Y)) : map (p.map f.continuous) = f.comp (map p) := by
  apply ContinuousMap.ext; intro z
  have hz : z ∈ ⋃ i, cylinderFace 1 i := by rw [cylinderFace_cover]; trivial
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  change cylinderBoundaryMap sides (ends (p.map f.continuous)) (ends_sides _) z =
    f (cylinderBoundaryMap sides (ends p) (ends_sides p) z)
  rw [cylinderBoundaryMap_face _ _ _ i ⟨z,hi⟩,cylinderBoundaryMap_face _ _ _ i ⟨z,hi⟩]
  cases i with
  | none => rfl
  | some b => cases b <;> rfl

lemma homotopic_map_of_fill (p : Path x x) (f : C(X,Y)) (F : C(Disk 2,Y))
    (hF : ∀ z, F (boundary 2 z) = f (map p z)) :
    (p.map f.continuous).Homotopic (Path.refl (f x)) := by
  apply homotopic_of_fill _ F
  intro z
  rw [natural]
  exact hF z
end UniversalFInfinity.LoopSphere

end

end OAI
