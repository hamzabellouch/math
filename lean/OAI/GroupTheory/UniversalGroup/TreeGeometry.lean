import OAI.GroupTheory.UniversalGroup.TorusBundles

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.PathFamilies
open scoped unitInterval
universe u v
variable {Y : Type u} [TopologicalSpace Y] {X : Type v} [TopologicalSpace X]
variable {x y z : Y}

def diagonalSquare (p : Path x y) (q : Path y z) : C(I × I,Y) :=
  ⟨fun s => (p.trans q).extend (((s.1:ℝ)+(s.2:ℝ))/2),
    (p.trans q).continuous_extend.comp (by fun_prop)⟩

lemma diagonalSquare_zero_left (p : Path x y) (q : Path y z) (s : I) :
    diagonalSquare p q (0,s) = p s := by
  change (p.trans q).extend (((0:ℝ)+(s:ℝ))/2) = p s
  rw [Path.extend_trans_of_le_half p q (by have := s.2.2; linarith)]
  rw [show 2*(((0:ℝ)+(s:ℝ))/2) = (s:ℝ) by ring]
  exact p.extend_apply s.2
lemma diagonalSquare_one_left (p : Path x y) (q : Path y z) (s : I) :
    diagonalSquare p q (1,s) = q s := by
  change (p.trans q).extend (((1:ℝ)+(s:ℝ))/2) = q s
  rw [Path.extend_trans_of_half_le p q (by have := s.2.1; linarith)]
  rw [show 2*(((1:ℝ)+(s:ℝ))/2)-1 = (s:ℝ) by ring]
  exact q.extend_apply s.2
lemma diagonalSquare_symm (p : Path x y) (q : Path y z) (t s : I) :
    diagonalSquare p q (t,s) = diagonalSquare p q (s,t) := by
  change (p.trans q).extend _ = (p.trans q).extend _
  rw [add_comm (t:ℝ) (s:ℝ)]
lemma diagonalSquare_zero_right (p : Path x y) (q : Path y z) (t : I) :
    diagonalSquare p q (t,0) = p t := by
  rw [diagonalSquare_symm,diagonalSquare_zero_left]
lemma diagonalSquare_one_right (p : Path x y) (q : Path y z) (t : I) :
    diagonalSquare p q (t,1) = q t := by
  rw [diagonalSquare_symm,diagonalSquare_one_left]

lemma diagonalSquare_continuous {a b c : X → Y}
    (p : ∀ x,Path (a x) (b x)) (q : ∀ x,Path (b x) (c x))
    (hp : Continuous (fun z : X × I => p z.1 z.2))
    (hq : Continuous (fun z : X × I => q z.1 z.2)) :
    Continuous (fun z : X × (I × I) => diagonalSquare (p z.1) (q z.1) z.2) := by
  exact (Path.continuous_uncurry_extend_of_continuous_family
    (fun x => (p x).trans (q x)) (Path.trans_continuous_family p hp q hq)).comp
      (continuous_fst.prodMk (by fun_prop))
lemma diagonalSquare_continuous_params {a b c : X → Y}
    (p : ∀ x,Path (a x) (b x)) (q : ∀ x,Path (b x) (c x))
    (hp : Continuous (fun z : X × I => p z.1 z.2))
    (hq : Continuous (fun z : X × I => q z.1 z.2)) :
    Continuous (fun z : I × (I × X) => diagonalSquare (p z.2.2) (q z.2.2) (z.1,z.2.1)) := by
  have hc : Continuous (fun z : I × (I × X) => (z.2.2,(z.1,z.2.1))) :=
    continuous_snd.snd.prodMk (continuous_fst.prodMk continuous_snd.fst)
  exact (diagonalSquare_continuous p q hp hq).comp hc
end UniversalFInfinity.PathFamilies

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A]
variable (τ : C → C) (F : C → C(A,A))

abbrev Homogeneous := Space τ (fun _ => ContinuousMap.id A) F

def shift : C(Homogeneous τ F,Homogeneous τ F) :=
  lift τ (fun _ => .id A) F
    (fun c => (vertexMap τ (fun _ => .id A) F (τ c)).comp (F c))
    (fun c => (edgeMap τ (fun _ => .id A) F (τ c)).comp
      ⟨fun z => (z.1,F c z.2),continuous_fst.prodMk ((F c).continuous.comp continuous_snd)⟩)
    (fun c x => edge_zero τ _ F (τ c) (F c x))
    (fun c x => edge_one τ _ F (τ c) (F c x))
lemma shift_vertex (c : C) (x : A) :
    shift τ F (vertex τ (fun _ => .id A) F c x) = vertex τ (fun _ => .id A) F (τ c) (F c x) := rfl
lemma shift_edge (c : C) (t : I) (x : A) :
    shift τ F (edge τ (fun _ => .id A) F c t x) = edge τ (fun _ => .id A) F (τ c) t (F c x) :=
  lift_edge τ _ F _ _ _ _ c (t,x)

def shiftVertexHomotopy (c : C) :
    ((ContinuousMap.id _).comp (vertexMap τ (fun _ => .id A) F c)).Homotopy
      ((shift τ F).comp (vertexMap τ (fun _ => .id A) F c)) where
  toFun z := edge τ (fun _ => .id A) F c z.1 z.2
  continuous_toFun := (edgeMap τ (fun _ => .id A) F c).continuous
  map_zero_left x := edge_zero τ _ F c x
  map_one_left x := edge_one τ _ F c x

omit [DiscreteTopology C] in
lemma shiftEdge_continuous (c : C) :
    Continuous (fun z : I × (I × A) =>
      PathFamilies.diagonalSquare (edgePath τ (fun _ => .id A) F c z.2.2)
        (edgePath τ (fun _ => .id A) F (τ c) (F c z.2.2)) (z.1,z.2.1)) := by
  let p : ∀ x : A, Path (vertex τ (fun _ => .id A) F c x)
      (vertex τ (fun _ => .id A) F (τ c) (F c x)) := edgePath τ (fun _ => .id A) F c
  let q : ∀ x : A, Path (vertex τ (fun _ => .id A) F (τ c) (F c x))
      (vertex τ (fun _ => .id A) F (τ (τ c)) (F (τ c) (F c x))) :=
    fun x => edgePath τ (fun _ => .id A) F (τ c) (F c x)
  have hp : Continuous (fun z : A × I => p z.1 z.2) :=
    (edgeMap τ (fun _ => .id A) F c).continuous.comp continuous_swap
  have hq : Continuous (fun z : A × I => q z.1 z.2) :=
    (edgeMap τ (fun _ => .id A) F (τ c)).continuous.comp
      (continuous_snd.prodMk ((F c).continuous.comp continuous_fst))
  exact PathFamilies.diagonalSquare_continuous_params p q hp hq

def shiftEdgeHomotopy (c : C) :
    ((ContinuousMap.id _).comp (edgeMap τ (fun _ => .id A) F c)).Homotopy
      ((shift τ F).comp (edgeMap τ (fun _ => .id A) F c)) where
  toFun z := PathFamilies.diagonalSquare (edgePath τ (fun _ => .id A) F c z.2.2)
    (edgePath τ (fun _ => .id A) F (τ c) (F c z.2.2)) (z.1,z.2.1)
  continuous_toFun := shiftEdge_continuous τ F c
  map_zero_left z := PathFamilies.diagonalSquare_zero_left _ _ z.1
  map_one_left z := (PathFamilies.diagonalSquare_one_left _ _ z.1).trans (shift_edge τ F c z.1 z.2).symm

def shiftHomotopy : (ContinuousMap.id (Homogeneous τ F)).Homotopy (shift τ F) :=
  homotopy τ (fun _ => .id A) F _ _ (shiftVertexHomotopy τ F) (shiftEdgeHomotopy τ F)
    (fun _ t _ => PathFamilies.diagonalSquare_zero_right _ _ t)
    (fun _ t _ => PathFamilies.diagonalSquare_one_right _ _ t)

def shiftIterate : ℕ → C(Homogeneous τ F,Homogeneous τ F)
  | 0 => .id _
  | n+1 => (shift τ F).comp (shiftIterate n)
def shiftIterateHomotopy : ∀ n,(ContinuousMap.id _).Homotopy (shiftIterate τ F n)
  | 0 => .refl _
  | n+1 => (shiftIterateHomotopy n).trans ((shiftHomotopy τ F).compContinuousMap (shiftIterate τ F n))
end

open Set Topology
open scoped unitInterval
universe u v
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A]
variable (τ : C → C) (F : C → C(A,A))

def forward : ℕ → C → C(A,A)
  | 0,_ => .id _
  | n+1,c => (F (τ^[n] c)).comp (forward n c)
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma forward_natural (n : ℕ) (c : C) (x : A) :
    forward τ F n (τ c) (F c x) = F (τ^[n] c) (forward τ F n c x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change F (τ^[n] (τ c)) (forward τ F n (τ c) (F c x)) =
      F (τ^[n+1] c) (F (τ^[n] c) (forward τ F n c x))
    rw [ih,Function.iterate_succ_apply]
lemma shiftIterate_vertex (n : ℕ) (c : C) (x : A) :
    shiftIterate τ F n (vertex τ (fun _ => .id A) F c x) =
      vertex τ (fun _ => .id A) F (τ^[n] c) (forward τ F n c x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change shift τ F (shiftIterate τ F n (vertex τ (fun _ => .id A) F c x)) = _
    rw [ih,shift_vertex,Function.iterate_succ_apply']
    rfl
lemma shiftIterate_edge (n : ℕ) (c : C) (t : I) (x : A) :
    shiftIterate τ F n (edge τ (fun _ => .id A) F c t x) =
      edge τ (fun _ => .id A) F (τ^[n] c) t (forward τ F n c x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change shift τ F (shiftIterate τ F n (edge τ (fun _ => .id A) F c t x)) = _
    rw [ih,shift_edge,Function.iterate_succ_apply']
    rfl
end UniversalFInfinity.GraphBundle

namespace UniversalFInfinity.Milnor
variable {G : Type*} [Group G]

lemma iterateHom_comm (f : G →* G) (n : ℕ) (g : G) : iterateHom f n (f g) = f (iterateHom f n g) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg f ih
end UniversalFInfinity.Milnor

namespace UniversalFInfinity.TorusGeometry
open Set Topology Milnor AscendingTorus
open scoped unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

def forwardOffset : ℕ → Coset f → U
  | 0,_ => 1
  | n+1,c => cosetOffset f ((next f)^[n] c) * f (forwardOffset n c)
lemma forward_eq (n : ℕ) (c : Coset f) (x : Milnor.Space U) :
    GraphBundle.forward (next f) (transition f) n c x =
      forwardOffset f n c • Milnor.map (iterateHom f n) id Function.injective_id x := by
  induction n with
  | zero =>
    change x = 1 • Milnor.map (id : U → U) id Function.injective_id x
    rw [one_smul,Milnor.map_id]
  | succ n ih =>
    change transition f ((next f)^[n] c) (GraphBundle.forward (next f) (transition f) n c x) = _
    rw [ih,transition_apply]
    refine (congrArg (cosetOffset f ((next f)^[n] c) • ·)
      (Milnor.map_smul f (forwardOffset f n c) _)).trans ?_
    rw [←mul_smul]
    change (cosetOffset f ((next f)^[n] c) * f (forwardOffset f n c)) •
      Milnor.map f id Function.injective_id (Milnor.map (iterateHom f n) id Function.injective_id x) = _
    rw [Milnor.map_comp]
    rfl

lemma forward_naturality (n : ℕ) (c : Coset f) (x : Milnor.Space U) :
    transition f ((next f)^[n] c)
      (forwardOffset f n c • Milnor.map (iterateHom f n) id Function.injective_id x) =
      forwardOffset f n (next f c) • Milnor.map (iterateHom f n) id Function.injective_id (transition f c x) := by
  rw [←forward_eq,←forward_eq]
  exact (GraphBundle.forward_natural (next f) (transition f) n c x).symm

lemma stage_shift_vertex (S : Shapes U) (n : ℕ) (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    GraphBundle.shiftIterate (next f) (transition f) n
      (stageFull f S (GraphBundle.vertex _ _ _ c x)) =
    vertex f ((next f)^[n] c)
      (forwardOffset f n c • Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U _ x)) := by
  rw [stageFull_vertex]
  exact (GraphBundle.shiftIterate_vertex _ _ n c _).trans (congrArg (vertex f _) (forward_eq f n c _))
lemma stage_shift_edge (S : Shapes U) (n : ℕ) (c : Coset f) (t : I) (x : Milnor.Stage U S) :
    GraphBundle.shiftIterate (next f) (transition f) n
      (stageFull f S (GraphBundle.edge _ _ _ c t x)) =
    GraphBundle.edge _ _ _ ((next f)^[n] c) t
      (forwardOffset f n c • Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U _ x)) := by
  rw [stageFull_edge,GraphBundle.shiftIterate_edge,forward_eq]
end UniversalFInfinity.TorusGeometry

namespace UniversalFInfinity.DirectedGraph
open Set Metric Topology Attachment
open scoped unitInterval
universe u v
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C] (τ : C → C)

def attaching (c : C) : C(Sphere 1,C) :=
  ⟨fun x => if x.1 0 = -1 then c else τ c,continuous_of_discreteTopology⟩
abbrev Graph := Space (attaching τ)
def vertex (c : C) : Graph τ := base _ c

lemma discrete_dimension (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set C) m) : m < 1 := by
  cases m with
  | zero => omega
  | succ m => exact i.elim
instance graphCW [Nonempty C] : CWComplex (Set.univ : Set (Graph τ)) := layerCW _ discrete_dimension
instance : T2Space (Graph τ) := t2Space _ (realSeparated_of_tychonoff (Y := C))
lemma graph_dimension [Nonempty C] (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set (Graph τ)) m) : m < 2 :=
  layerCW_dimensions _ discrete_dimension m i

omit [DiscreteTopology C] in
lemma cell_minus (c : C) : cell (attaching τ) c (boundary 1 Cayley.minus) = vertex τ c := by
  rw [cell_boundary]; simp only [attaching,Cayley.minus,ContinuousMap.coe_mk,ite_true]; rfl
omit [DiscreteTopology C] in
lemma cell_plus (c : C) : cell (attaching τ) c (boundary 1 Cayley.plus) = vertex τ (τ c) := by
  rw [cell_boundary]; norm_num [attaching,Cayley.plus,vertex]

def edge (c : C) : Path (vertex τ c) (vertex τ (τ c)) where
  toFun t := cell (attaching τ) c (Cayley.edgeParam t)
  continuous_toFun := (cell _ c).continuous.comp Cayley.continuous_edgeParam
  source' := by rw [Cayley.edgeParam_zero,cell_minus]
  target' := by rw [Cayley.edgeParam_one,cell_plus]

variable {Y : Type v} [TopologicalSpace Y] (f : C(Graph τ,Y)) (y : Y)
variable (p : ∀ c,Path y (f (vertex τ c)))
variable (hp : ∀ c,((p c).trans ((edge τ c).map f.continuous)).Homotopic (p (τ c)))

def edgeSquare (c : C) : ((edge τ c).map f.continuous).toContinuousMap.Homotopy (.const _ y) :=
  (PathSquares.edgeSquare (p c) (p (τ c)) ((edge τ c).map f.continuous) (hp c)).choose
omit [DiscreteTopology C] in
lemma edgeSquare_source (c : C) (t : I) : edgeSquare τ f y p hp c (t,0) = PathSquares.pauseReverse (p c) t :=
  (PathSquares.edgeSquare (p c) (p (τ c)) ((edge τ c).map f.continuous) (hp c)).choose_spec.1 t
omit [DiscreteTopology C] in
lemma edgeSquare_target (c : C) (t : I) : edgeSquare τ f y p hp c (t,1) = PathSquares.pauseReverse (p (τ c)) t :=
  (PathSquares.edgeSquare (p c) (p (τ c)) ((edge τ c).map f.continuous) (hp c)).choose_spec.2 t

def edgePaths (c : C) : C(Disk 1,C(I,Y)) :=
  ContinuousMap.curry ⟨fun z => edgeSquare τ f y p hp c (z.2,Cayley.edgeTime z.1),
    (edgeSquare τ f y p hp c).continuous.comp
      (continuous_snd.prodMk (Cayley.continuous_edgeTime.comp continuous_fst))⟩
def vertexPaths : C(C,C(I,Y)) := ⟨fun c => PathSquares.pauseReverse (p c),continuous_of_discreteTopology⟩
lemma edgePaths_boundary (c : C) (t : Sphere 1) :
    edgePaths τ f y p hp c (boundary 1 t) = vertexPaths τ f y p (attaching τ c t) := by
  obtain rfl|rfl := Cayley.sphere_one_eq t
  · apply ContinuousMap.ext; intro z
    change edgeSquare τ f y p hp c (z,Cayley.edgeTime (boundary 1 Cayley.minus)) = _
    rw [Cayley.edgeTime_minus,edgeSquare_source]
    simp only [vertexPaths,attaching,ContinuousMap.coe_mk,Cayley.minus,ite_true]
  · apply ContinuousMap.ext; intro z
    change edgeSquare τ f y p hp c (z,Cayley.edgeTime (boundary 1 Cayley.plus)) = _
    rw [Cayley.edgeTime_plus,edgeSquare_target]
    norm_num [vertexPaths,attaching,Cayley.plus]

def graphPaths : C(Graph τ,C(I,Y)) :=
  lift _ (vertexPaths τ f y p) (edgePaths τ f y p hp) (edgePaths_boundary τ f y p hp)
lemma graphPaths_zero (z : Graph τ) : graphPaths τ f y p hp z 0 = f z := by
  cases z with
  | inl c => exact Path.source _
  | inr z =>
    change edgeSquare τ f y p hp z.1 (0,Cayley.edgeTime (interior 1 z.2)) = _
    rw [ContinuousMap.Homotopy.apply_zero]
    change f (cell _ z.1 (Cayley.edgeParam (Cayley.edgeTime (interior 1 z.2)))) = f _
    rw [Cayley.edgeParam_time,cell_interior]
lemma graphPaths_one (z : Graph τ) : graphPaths τ f y p hp z 1 = y := by
  cases z with
  | inl c => exact Path.target _
  | inr z =>
    change edgeSquare τ f y p hp z.1 (1,Cayley.edgeTime (interior 1 z.2)) = y
    exact ContinuousMap.Homotopy.apply_one _ _

def graphNullhomotopy : f.Homotopy (.const _ y) where
  toFun z := graphPaths τ f y p hp z.2 z.1
  continuous_toFun := (graphPaths τ f y p hp).uncurry.continuous.comp continuous_swap
  map_zero_left := graphPaths_zero τ f y p hp
  map_one_left := graphPaths_one τ f y p hp

end UniversalFInfinity.DirectedGraph

namespace UniversalFInfinity.DirectedTree
universe u v
variable {C : Type u} {G : Type v} [Group G]
variable (τ : C → C) (h : C → ℤ) (hτ : ∀ c, h (τ c) = h c + 1)

include hτ in
lemma height_iterate (c : C) (n : ℕ) : h (τ^[n] c) = h c + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',hτ,ih]; push_cast; omega

variable (w : C → G)
def rayProduct (c : C) : ℕ → G
  | 0 => 1
  | n+1 => rayProduct c n * w (τ^[n] c)

lemma rayProduct_add (c : C) (n k : ℕ) :
    rayProduct τ w c (n+k) = rayProduct τ w c n * rayProduct τ w (τ^[n] c) k := by
  induction k with
  | zero => simp [rayProduct]
  | succ k ih =>
    rw [Nat.add_succ,rayProduct,ih,rayProduct,mul_assoc]
    congr 2
    rw [Function.iterate_add_apply]
    exact congrArg w ((Function.Commute.iterate_iterate (Function.Commute.refl τ) n k).eq c)

lemma rayProduct_first (c : C) (n : ℕ) :
    rayProduct τ w c (n+1) = w c * rayProduct τ w (τ c) n := by
  simpa only [Nat.add_comm 1 n,rayProduct,Function.iterate_zero,Function.id_def,one_mul,
    Function.iterate_one] using rayProduct_add τ w c 1 n

include h hτ in

lemma route_independent (c d : C) (p q p' q' : ℕ)
    (he : τ^[p] c = τ^[q] d) (he' : τ^[p'] c = τ^[q'] d) :
    rayProduct τ w c p * (rayProduct τ w d q)⁻¹ =
      rayProduct τ w c p' * (rayProduct τ w d q')⁻¹ := by
  have hlen : (p:ℤ) + q' = (p':ℤ) + q := by
    have ha := congrArg h he
    have hb := congrArg h he'
    rw [height_iterate τ h hτ,height_iterate τ h hτ] at ha hb
    omega
  have hlen' : p + q' = p' + q := by omega
  have enlarge (a b : C) (i j k : ℕ) (hab : τ^[i] a = τ^[j] b) :
      rayProduct τ w a i * (rayProduct τ w b j)⁻¹ =
      rayProduct τ w a (i+k) * (rayProduct τ w b (j+k))⁻¹ := by
    rw [rayProduct_add,rayProduct_add,hab,mul_inv_rev]
    group
  rw [enlarge c d p q q' he,enlarge c d p' q' q he',hlen',Nat.add_comm q' q]

variable (hc : ∀ c d, ∃ p q : ℕ, τ^[p] c = τ^[q] d) (root : C)
def potential (c : C) : G :=
  let p := (hc root c).choose
  let q := (hc root c).choose_spec.choose
  rayProduct τ w root p * (rayProduct τ w c q)⁻¹

include h hτ in
lemma potential_route (c : C) (p q : ℕ) (he : τ^[p] root = τ^[q] c) :
    potential τ w hc root c = rayProduct τ w root p * (rayProduct τ w c q)⁻¹ := by
  exact route_independent τ h hτ w root c _ _ p q (hc root c).choose_spec.choose_spec he

include h hτ in

lemma potential_edge (c : C) : potential τ w hc root c * w c = potential τ w hc root (τ c) := by
  obtain ⟨p,q,he⟩ := hc root (τ c)
  have he' : τ^[p] root = τ^[q+1] c := by simpa only [Function.iterate_succ_apply] using he
  rw [potential_route τ h hτ w hc root c p (q+1) he',
    potential_route τ h hτ w hc root (τ c) p q he,rayProduct_first]
  group

end UniversalFInfinity.DirectedTree

namespace UniversalFInfinity.DirectedGraph
open Set Topology Attachment
open scoped unitInterval
universe u
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C] (τ : C → C)
variable (h : C → ℤ) (hτ : ∀ c, h (τ c) = h c + 1)
variable (hc : ∀ c d, ∃ p q : ℕ, τ^[p] c = τ^[q] d) (root : C)

omit [DiscreteTopology C] in
lemma ray_joined (c : C) (n : ℕ) : Joined (vertex τ c) (vertex τ (τ^[n] c)) := by
  induction n with
  | zero => exact Joined.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans ⟨edge τ (τ^[n] c)⟩

include hc in
omit [DiscreteTopology C] in
lemma vertex_joined (c : C) : Joined (vertex τ root) (vertex τ c) := by
  obtain ⟨p,q,he⟩ := hc root c
  have hd : Joined (vertex τ c) (vertex τ (τ^[p] root)) := by
    rw [he]; exact ray_joined τ c q
  exact (ray_joined τ root p).trans hd.symm

def initialPath (c : C) : Path (vertex τ root) (vertex τ c) :=
  (vertex_joined τ hc root c).somePath

def initialClass (c : C) : Path.Homotopic.Quotient (vertex τ root) (vertex τ c) :=
  Path.Homotopic.Quotient.mk (initialPath τ hc root c)

def edgeClass (c : C) : Path.Homotopic.Quotient (vertex τ c) (vertex τ (τ c)) :=
  Path.Homotopic.Quotient.mk (edge τ c)

def edgeWeight (c : C) : (FundamentalGroup (Graph τ) (vertex τ root))ᵐᵒᵖ :=
  MulOpposite.op (((initialClass τ hc root c).trans (edgeClass τ c)).trans
    (initialClass τ hc root (τ c)).symm)

def treeClass (c : C) : Path.Homotopic.Quotient (vertex τ root) (vertex τ c) :=
  (MulOpposite.unop (DirectedTree.potential τ (edgeWeight τ hc root) hc root c)).trans
    (initialClass τ hc root c)

include h hτ in
omit [DiscreteTopology C] in
lemma treeClass_edge (c : C) : (treeClass τ hc root c).trans (edgeClass τ c) =
    treeClass τ hc root (τ c) := by
  have he := DirectedTree.potential_edge τ h hτ (edgeWeight τ hc root) hc root c
  have he' := congrArg MulOpposite.unop he
  simp only [MulOpposite.unop_mul,FundamentalGroup.mul_def,edgeWeight,MulOpposite.unop_op] at he'
  have hh := congrArg (fun (k : FundamentalGroup (Graph τ) (vertex τ root)) =>
    k.trans (initialClass τ hc root (τ c))) he'
  simpa only [treeClass,Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.trans_refl] using hh

def treePath (c : C) : Path (vertex τ root) (vertex τ c) :=
  (Path.Homotopic.Quotient.mk_surjective (treeClass τ hc root c)).choose

include h hτ in
omit [DiscreteTopology C] in
lemma treePath_edge (c : C) : ((treePath τ hc root c).trans (edge τ c)).Homotopic
    (treePath τ hc root (τ c)) := by
  apply Path.Homotopic.Quotient.exact
  change (Path.Homotopic.Quotient.mk (treePath τ hc root c)).trans (edgeClass τ c) = _
  unfold treePath
  rw [(Path.Homotopic.Quotient.mk_surjective (treeClass τ hc root c)).choose_spec,
    (Path.Homotopic.Quotient.mk_surjective (treeClass τ hc root (τ c))).choose_spec]
  exact treeClass_edge τ h hτ hc root c

include hτ hc root in

lemma tree_contractible : ContractibleSpace (Graph τ) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨vertex τ root,⟨graphNullhomotopy τ (.id _) (vertex τ root)
    (treePath τ hc root) ?_⟩⟩
  intro c
  simpa only [ContinuousMap.coe_id,Path.map_id] using treePath_edge τ h hτ hc root c
end UniversalFInfinity.DirectedGraph

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))
variable {Y : Type z} [TopologicalSpace Y]

def treeProjection : C(Space τ L R,DirectedGraph.Graph τ) :=
  lift τ L R (fun c => .const _ (DirectedGraph.vertex τ c))
    (fun c => (DirectedGraph.edge τ c).toContinuousMap.comp (.fst))
    (fun c _ => (DirectedGraph.edge τ c).source)
    (fun c _ => (DirectedGraph.edge τ c).target)
lemma treeProjection_vertex (c : C) (x : A) :
    treeProjection τ L R (vertex τ L R c x) = DirectedGraph.vertex τ c := rfl
lemma treeProjection_edge (c : C) (t : I) (x : B) :
    treeProjection τ L R (edge τ L R c t x) = DirectedGraph.edge τ c t :=
  lift_edge τ L R _ _ _ _ c (t,x)

omit [DiscreteTopology C] in
lemma pathMap_boundary (y : C → Y) (p : ∀ c,Path (y c) (y (τ c))) (c : C)
    (x : Attachment.Sphere 1) :
    p c (Cayley.edgeTime (Attachment.boundary 1 x)) = y (DirectedGraph.attaching τ c x) := by
  obtain rfl|rfl := Cayley.sphere_one_eq x
  · rw [Cayley.edgeTime_minus,Path.source]
    simp only [DirectedGraph.attaching,Cayley.minus,ContinuousMap.coe_mk,ite_true]
  · rw [Cayley.edgeTime_plus,Path.target]
    norm_num [DirectedGraph.attaching,Cayley.plus]

def treePathMap (y : C → Y) (p : ∀ c,Path (y c) (y (τ c))) : C(DirectedGraph.Graph τ,Y) :=
  Attachment.lift _ ⟨y,continuous_of_discreteTopology⟩
    (fun c => (p c).toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩)
    (pathMap_boundary τ y p)
lemma treePathMap_vertex (y : C → Y) (p : ∀ c,Path (y c) (y (τ c))) (c : C) :
    treePathMap τ y p (DirectedGraph.vertex τ c) = y c := rfl
lemma treePathMap_edge (y : C → Y) (p : ∀ c,Path (y c) (y (τ c))) (c : C) (t : I) :
    treePathMap τ y p (DirectedGraph.edge τ c t) = p c t := by
  change Attachment.lift _ _ _ _ (Attachment.cell _ c (Cayley.edgeParam t)) = _
  rw [Attachment.lift_cell]
  change p c (Cayley.edgeTime (Cayley.edgeParam t)) = p c t
  rw [Cayley.edgeTime_param]

lemma nullhomotopic_of_fiber_constant (h : C → ℤ) (hτ : ∀ c,h (τ c) = h c+1)
    (hc : ∀ c d,∃ m n : ℕ,τ^[m] c = τ^[n] d) (root : C)
    (f : C(Space τ L R,Y)) (y : C → Y) (p : ∀ c,Path (y c) (y (τ c)))
    (hv : ∀ c x,f (vertex τ L R c x) = y c)
    (he : ∀ c t x,f (edge τ L R c t x) = p c t) : f.Nullhomotopic := by
  have := DirectedGraph.tree_contractible τ h hτ hc root
  have hf : f = (treePathMap τ y p).comp (treeProjection τ L R) := by
    apply hom_ext τ L R
    · intro c x
      simpa only [ContinuousMap.comp_apply,treeProjection_vertex,treePathMap_vertex] using hv c x
    · intro c z
      simpa only [ContinuousMap.comp_apply,treeProjection_edge,treePathMap_edge] using he c z.1 z.2
  rw [hf]
  have hn := (id_nullhomotopic (DirectedGraph.Graph τ)).comp_right (treePathMap τ y p)
  exact hn.comp_left (treeProjection τ L R)
end

open Set Topology
open scoped unitInterval
universe u v w z r
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))
variable {Y : Type z} [TopologicalSpace Y] {Z : Type r} [TopologicalSpace Z]
variable (f : C(Space τ L R,Y)) (y : C → Y)
variable (V : ∀ c,(f.comp (vertexMap τ L R c)).Homotopy (.const _ (y c)))
variable (a b : C → C(Z,Y)) (e : ∀ c z,Path (a c z) (b c z))
variable (he : ∀ c,Continuous (fun p : Z × I => e c p.1 p.2))
variable (H : C → C(I × B,Z))
variable (Q : C → C(B,C(I,C(I,Y))))
variable (hleft : ∀ c t x,a c (H c (t,x)) = V c (t,L c x))
variable (qleft : ∀ c x t,Q c x t 0 = b c (H c (t,x)))
variable (qright : ∀ c x t,Q c x t 1 = V (τ c) (t,R c x))

def connectorPath (c : C) (p : I × B) :
    Path (b c (H c p)) (V (τ c) (p.1,R c p.2)) where
  toFun s := Q c p.2 p.1 s
  continuous_toFun := (Q c p.2 p.1).continuous
  source' := qleft c p.2 p.1
  target' := qright c p.2 p.1

omit [DiscreteTopology C] in
lemma connectorPath_continuous (c : C) : Continuous (fun p : (I × B) × I =>
    connectorPath τ L R f y V b H Q qleft qright c p.1 p.2) := by
  change Continuous (fun p : (I × B) × I => Q c p.1.2 p.1.1 p.2)
  exact (Q c).uncurry.uncurry.continuous.comp
    ((continuous_fst.snd.prodMk continuous_fst.fst).prodMk continuous_snd)

def gluedPath (c : C) (p : I × B) : Path (a c (H c p)) (V (τ c) (p.1,R c p.2)) :=
  (e c (H c p)).trans (connectorPath τ L R f y V b H Q qleft qright c p)

include he in
omit [DiscreteTopology C] in
lemma gluedPath_continuous (c : C) : Continuous (fun p : (I × B) × I =>
    gluedPath τ L R f y V a b e H Q qleft qright c p.1 p.2) := by
  exact Path.trans_continuous_family (fun z : I × B => e c (H c z))
    ((he c).comp (((H c).continuous.comp continuous_fst).prodMk continuous_snd))
    (connectorPath τ L R f y V b H Q qleft qright c)
    (connectorPath_continuous τ L R f y V b H Q qleft qright c)

variable (e0 : ∀ c x s,e c (H c (0,x)) s = f (edge τ L R c s x))
variable (q0 : ∀ c x s,Q c x 0 s = f (vertex τ L R (τ c) (R c x)))
variable (p : ∀ c,Path (y c) (y (τ c)))
variable (e1 : ∀ c x s,gluedPath τ L R f y V a b e H Q qleft qright c (1,x) s = p c s)

include e0 q0 in
lemma gluedPath_zero (c : C) (x : B) (s : I) :
    gluedPath τ L R f y V a b e H Q qleft qright c (0,x) s =
      f (pause τ L R (edge τ L R c s x)) := by
  rw [pause_edge τ L R c (s,x)]
  change ((e c (H c (0,x))).trans (connectorPath τ L R f y V b H Q qleft qright c (0,x))) s =
    f ((edgePath τ L R c x).trans (Path.refl _) s)
  rw [Path.trans_apply,Path.trans_apply]
  split_ifs with hs
  · exact e0 c x _
  · exact q0 c x _

def collapsed : C(Space τ L R,Y) :=
  lift τ L R (fun c => .const _ (y c))
    (fun c => (p c).toContinuousMap.comp .fst)
    (fun c _ => (p c).source) (fun c _ => (p c).target)

lemma collapsed_edge (c : C) (s : I) (x : B) :
    collapsed τ L R y p (edge τ L R c s x) = p c s :=
  lift_edge τ L R _ _ _ _ c (s,x)

def gluedEdgeHomotopy (c : C) :
    ((f.comp (pause τ L R)).comp (edgeMap τ L R c)).Homotopy
      ((collapsed τ L R y p).comp (edgeMap τ L R c)) where
  toFun z := gluedPath τ L R f y V a b e H Q qleft qright c (z.1,z.2.2) z.2.1
  continuous_toFun := (gluedPath_continuous τ L R f y V a b e he H Q qleft qright c).comp
    ((continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst)
  map_zero_left z := gluedPath_zero τ L R f y V a b e H Q qleft qright e0 q0 c z.2 z.1
  map_one_left z := (e1 c z.2 z.1).trans (collapsed_edge τ L R y p c z.1 z.2).symm

def gluedVertexHomotopy (c : C) :
    ((f.comp (pause τ L R)).comp (vertexMap τ L R c)).Homotopy
      ((collapsed τ L R y p).comp (vertexMap τ L R c)) := V c

def coherentHomotopy : (f.comp (pause τ L R)).Homotopy (collapsed τ L R y p) :=
  homotopy τ L R _ _ (gluedVertexHomotopy τ L R f y V p)
    (gluedEdgeHomotopy τ L R f y V a b e he H Q qleft qright e0 q0 p e1)
    (fun c t x => ((gluedPath τ L R f y V a b e H Q qleft qright c (t,x)).source).trans (hleft c t x))
    (fun c t x => (gluedPath τ L R f y V a b e H Q qleft qright c (t,x)).target)

include he hleft e0 q0 e1 in

theorem nullhomotopic_of_coherent_contraction
    (height : C → ℤ) (hτ : ∀ c,height (τ c) = height c+1)
    (hc : ∀ c d,∃ m n : ℕ,τ^[m] c = τ^[n] d) (root : C) : f.Nullhomotopic := by
  have hn := nullhomotopic_of_fiber_constant τ L R height hτ hc root
    (collapsed τ L R y p) y p (fun _ _ => rfl) (collapsed_edge τ L R y p)
  obtain ⟨z,⟨K⟩⟩ := hn
  refine ⟨z,⟨?_⟩⟩
  have J := coherentHomotopy τ L R f y V a b e he H Q hleft qleft qright e0 q0 p e1
  have P := (ContinuousMap.Homotopy.refl f).comp (pauseHomotopy τ L R)
  exact P.symm.trans (J.trans K)
end UniversalFInfinity.GraphBundle

end

end OAI
