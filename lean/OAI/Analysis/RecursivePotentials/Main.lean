import OAI.Analysis.RecursivePotentials.VariableStability

namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

open Filter Topology TopologicalSpace

open scoped ENNReal

namespace VariableTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

lemma path_upper (s : ι) : GlobalUpper T e (T.path s) := by
  intro a S hS
  apply (e.agg_le_iff S (T.path s) (T.path_nonneg s a)).mpr
  have hpow (c) : |T.path s c|^e.val = (T.path s c)^2 := by
    rw [T.path_apply]
    split_ifs <;> simp [Real.zero_rpow e.ne_zero]
  calc
    _ = ∑ c ∈ S, T.path s c^2 := Finset.sum_congr rfl (fun c hc => hpow c)
    _ ≤ T.path s a^2 := T.path_upper s a S hS
    _ = T.path s a^e.val := by rw [←hpow,abs_of_nonneg (T.path_nonneg s a)]

lemma path_fields (s c : ι) : P T e (T.path s) c = T.path s c ∧ Q T e (T.path s) c = 0 := by
  have hh := potentials_minimal T e (T.path s) (T.path s) 0 (T.path_nonneg s)
    (fun _ => le_rfl) (fun _ => sub_zero _) (path_upper T e s)
    (by intro s S hs; exact (e.agg_zero S).le) c
  have hq : Q T e (T.path s) c = 0 := le_antisymm hh.2 (Q_nonneg T e _ _)
  have hp := P_sub_Q T e (T.path s) c
  rw [hq,sub_zero] at hp
  exact ⟨hp,hq⟩

lemma normSum_path (s : ι) : normSum T e (T.path s) = 1 := by
  unfold normSum
  rw [(path_fields T e s T.root).1,(path_fields T e s T.root).2,T.path_root,add_zero]

lemma twice_coordinate_le_normSum (v : ι →₀ ℝ) (hv : v T.root = 0) (s : ι) :
    2*|v s| ≤ normSum T e v := by
  have hd := P_sub_Q T e v T.root
  rw [hv] at hd
  have hp := (P_upper T e v).le_root T e (P_nonneg T e v) s
  have hq := (Q_upper T e v).le_root T e (Q_nonneg T e v) s
  have hc := P_sub_Q T e v s
  have hp0 := P_nonneg T e v s
  have hq0 := Q_nonneg T e v s
  unfold normSum
  rcases le_total 0 (v s) with hs | hs
  · rw [abs_of_nonneg hs]; linarith
  · rw [abs_of_nonpos hs]; linarith

end VariableTree

namespace Variable

open UniformSpace VariableExponent Filter Topology

def componentBasis (h : ℕ+) (s : ComponentNode h) : Component h :=
  ((AggregationVector.basisVector (componentTree h) (exponent h) s : AggregationVector (componentTree h) (exponent h)) : Component h)

lemma componentEquiv_basis (h : ℕ+) (s : ComponentNode h) :
    componentEquiv h (componentBasis h s) = lp.single (ENNReal.ofReal (heightExponent h)) s 1 := by
  apply Subtype.ext
  funext t
  rw [componentEquiv_apply,componentBasis,componentCoordinate,AggregationSpace.coordinate_coe,
    AggregationVector.basisVector_apply,lp.single_apply]
  simp [Pi.single_apply,eq_comm]

lemma componentBasis_lower (h : ℕ+) (s : ComponentNode h) (hs : s ≠ (componentTree h).root) :
    2 ≤ ‖componentBasis h s‖ := by
  rw [componentBasis,Completion.norm_coe,AggregationVector.norm_def]
  have hh := VariableTree.twice_coordinate_le_normSum (componentTree h) (exponent h)
    (Finsupp.single s 1) (by simp [hs]) s
  simpa only [AggregationVector.basisVector,Finsupp.single_eq_same,abs_one,mul_one] using hh

lemma componentBasis_weaklyNull (h : ℕ+) (s : ℕ → ComponentNode h) (hs : Function.Injective s) :
    WeaklyNull (fun n => componentBasis h (s n)) := by
  intro f
  let p : PowerExponent := ⟨heightExponent h,heightExponent_gt_one h⟩
  let : Fact (1 ≤ ENNReal.ofReal p.val) := ⟨ENNReal.one_le_ofReal.mpr p.one_lt.le⟩
  have hh := ScalarLp.basis_functionals_tendsto_zero p s hs
    (f.comp (componentEquiv h).symm.toContinuousLinearMap)
  convert hh using 1
  funext n
  change f (componentBasis h (s n)) = f ((componentEquiv h).symm (lp.single _ (s n) 1))
  exact congrArg f (((componentEquiv h).symm_apply_apply (componentBasis h (s n))).symm.trans
    (congrArg (componentEquiv h).symm (componentEquiv_basis h (s n))))

lemma basis_weaklyNull (h : ℕ+) (s : ℕ → ComponentNode h) (hs : Function.Injective s) :
    WeaklyNull (fun n => basis ⟨h,s n⟩) := by
  intro f
  exact componentBasis_weaklyNull h s hs (f.comp (lp.singleContinuousLinearMap ℝ Component 2 h))

def componentPath (h : ℕ+) (s : ComponentNode h) : Component h :=
  ((show AggregationVector (componentTree h) (exponent h) from (componentTree h).path s) : Component h)

lemma componentPath_norm (h : ℕ+) (s : ComponentNode h) : ‖componentPath h s‖ = 1 := by
  let v : AggregationVector (componentTree h) (exponent h) := (componentTree h).path s
  change ‖(v : Component h)‖ = 1
  exact (Completion.norm_coe v).trans (VariableTree.normSum_path (componentTree h) (exponent h) s)

lemma componentPath_step (h : ℕ+) (s : ComponentNode h) (hs : s ≠ (componentTree h).root) :
    componentPath h s-componentPath h ((componentTree h).parent s) = componentBasis h s := by
  change ((↑(show AggregationVector (componentTree h) (exponent h) from (componentTree h).path s)) : Component h)-
    ↑(show AggregationVector (componentTree h) (exponent h) from (componentTree h).path ((componentTree h).parent s)) = _
  rw [←Completion.coe_sub]
  apply congrArg (fun a : AggregationVector (componentTree h) (exponent h) => (a : Component h))
  change (componentTree h).path s-(componentTree h).path ((componentTree h).parent s) = Finsupp.single s 1
  rw [(componentTree h).path_step s hs]
  abel

def pathHeight (h : ℕ) : ℕ+ := ⟨h+1,by omega⟩

def pathNode (h : ℕ) (s : List ℕ) : ComponentNode (pathHeight h) :=
  ⟨s.take h,by change (s.take h).length ≤ h+1; simp only [List.length_take]; omega⟩

def pathVector (h : ℕ) (s : List ℕ) : Xv :=
  lp.single 2 (pathHeight h) (componentPath _ (pathNode h s))

lemma pathVector_norm (h : ℕ) (s : List ℕ) : ‖pathVector h s‖ = 1 := by
  rw [pathVector,lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2),componentPath_norm]

lemma pathNode_child (h : ℕ) (s : List ℕ) (hs : s.length < h) (k : ℕ) :
    pathNode h (s++[k]) ≠ (componentTree (pathHeight h)).root ∧
      (componentTree (pathHeight h)).parent (pathNode h (s++[k])) = pathNode h s := by
  have hs' : s.length ≤ h := hs.le
  have hsk : (s++[k]).length ≤ h := by simp; omega
  constructor
  · intro he
    have hh := congrArg Subtype.val he
    simp only [pathNode,componentTree,List.take_of_length_le hsk,List.append_eq_nil_iff,List.cons_ne_self, and_false] at hh
  · apply Subtype.ext
    simp [componentTree,pathNode,List.take_of_length_le hs',List.take_of_length_le hsk]

def children (h : ℕ) (s : List ℕ) (hs : s.length < h) : ℕ ↪ ComponentNode (pathHeight h) where
  toFun k := pathNode h (s++[k])
  inj' := by
    intro k l he
    have hsk : (s++[k]).length ≤ h := by simp; omega
    have hsl : (s++[l]).length ≤ h := by simp; omega
    have hh := congrArg Subtype.val he
    simpa [pathNode,List.take_of_length_le hsk,List.take_of_length_le hsl] using hh

lemma pathVector_step (h : ℕ) (s : List ℕ) (hs : s.length < h) (k : ℕ) :
    pathVector h (s++[k])-pathVector h s = basis ⟨(pathHeight h),children h s hs k⟩ := by
  have hh := componentPath_step (pathHeight h) (pathNode h (s++[k])) (pathNode_child h s hs k).1
  rw [(pathNode_child h s hs k).2] at hh
  change lp.single 2 _ _-lp.single 2 _ _ = _
  rw [←lp.single_sub,hh]
  rfl

lemma pathVector_increments (h : ℕ) (s : List ℕ) (hs : s.length < h) :
    WeaklyNull (fun k => pathVector h (s++[k])-pathVector h s) := by
  simp_rw [pathVector_step h s hs]
  exact basis_weaklyNull _ (children h s hs) (children h s hs).injective

lemma pathVector_increment_lower (h : ℕ) (s : List ℕ) (hs : s.length < h) (k : ℕ) :
    2 ≤ ‖pathVector h (s++[k])-pathVector h s‖ := by
  rw [pathVector_step h s hs k]
  change 2 ≤ ‖lp.single 2 _ (componentBasis _ _)‖
  rw [lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2)]
  exact componentBasis_lower _ _ (pathNode_child h s hs k).1

lemma not_finite_dimensional : ¬Module.Finite ℝ Xv := by
  intro hh
  let := hh
  have hf : Function.Injective (fun x : Component (1:ℕ+) => lp.single 2 (1:ℕ+) x) := by
    intro x y he
    have h := congrArg (fun z : Xv => z (1:ℕ+)) he
    simpa only [lp.single_apply_self] using h
  have hfin := FiniteDimensional.of_injective (lp.singleContinuousLinearMap ℝ Component 2 (1:ℕ+)).toLinearMap hf
  let : Infinite (ComponentNode (1:ℕ+)) := Infinite.of_injective
    (fun n : ℕ => (⟨[n],by simp⟩ : ComponentNode (1:ℕ+))) (by intro n m he; simpa using congrArg Subtype.val he)
  exact AggregationSpace.not_finite_dimensional (componentTree (1:ℕ+)) (exponent (1:ℕ+)) hfin

theorem one_sided_modulus_zero (A : EquivalentNorm Xv) : A.modulus (A.lower/A.upper) = 0 := by
  have he : A.lower*2/(2*A.upper*1) = A.lower/A.upper := by field_simp [A.upper_pos.ne']
  rw [←he]
  apply bounded_trees_modulus_eq_zero not_finite_dimensional A pathVector
    (m := 1) (M := 1) (c := 2) (by norm_num) (by norm_num) (by norm_num)
  · intro h hh s hs; rw [pathVector_norm]; exact ⟨le_rfl,le_rfl⟩
  · intro h hh s hs; exact pathVector_increments h s hs
  · intro h hh s hs k; exact pathVector_increment_lower h s hs k

theorem no_equivalent_AUC (A : EquivalentNorm Xv) : ¬A.AUC := by
  intro h
  have hp : 0 < A.lower/A.upper := div_pos A.lower_pos A.upper_pos
  have hh := h _ hp
  rw [one_sided_modulus_zero] at hh
  exact lt_irrefl _ hh

end Variable

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma eq_zero_of_coordinates_zero (x : TreeSpace T)
    (hx : ∀ s, coordinate T s x = 0) : x = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg x)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨v,hv⟩ := Completion.denseRange_coe.exists_dist_lt x (half_pos hε)
  have hvx : ‖(v : TreeSpace T)-x‖ < ε/2 := by simpa [dist_eq_norm,norm_sub_rev] using hv
  let H := T.head (show ι →₀ ℝ from v)
  have hH : T.Initial H := T.head_initial v
  have hxH : headCoordinates T H x = 0 := by ext s; exact hx s
  have hPx : projection T H hH x = 0 := by
    rw [projection_reconstructs,hxH,map_zero,Completion.coe_zero]
  have hPv : projection T H hH (v : TreeSpace T) = v := by
    rw [projection_coe]
    apply congrArg ((↑) : TreeVector T → TreeSpace T)
    change ι →₀ ℝ at v
    apply Finsupp.ext
    intro s
    change T.projectHead H v s = v s
    rw [T.projectHead_apply]
    split_ifs with hs
    · rfl
    · exact (Finsupp.notMem_support_iff.mp fun ht => hs (T.support_subset_head v ht)).symm
  have hp := projection_contracts T H hH ((v : TreeSpace T)-x)
  rw [map_sub,hPx,sub_zero,hPv] at hp
  have htri := norm_add_le (x-(v : TreeSpace T)) (v : TreeSpace T)
  rw [sub_add_cancel,norm_sub_rev] at htri
  linarith

lemma coordinates_ext {x y : TreeSpace T}
    (h : ∀ s, coordinate T s x = coordinate T s y) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_coordinates_zero T
  intro s
  rw [map_sub,h s,sub_self]

lemma projection_fixed_iff (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T) :
    projection T H hH x = x ↔ ∀ s ∉ H, coordinate T s x = 0 := by
  constructor
  · intro hx s hs
    have hh := coordinate_projection T H hH s x
    rwa [hx,ite_eq_right hs] at hh
  · intro hx
    apply coordinates_ext T
    intro s
    rw [coordinate_projection]
    split_ifs with hs
    · rfl
    · exact (hx s hs).symm

lemma mem_tail_iff (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T) :
    x ∈ tail T H hH ↔ ∀ s ∈ H, coordinate T s x = 0 := by
  rw [tail_eq_coordinate_kernel]
  change headCoordinates T H x = 0 ↔ _
  constructor
  · intro hx s hs
    exact congrFun hx ⟨s,hs⟩
  · intro hx
    ext s
    exact hx s s.2

lemma projection_finite_rank (H : Finset ι) (hH : T.Initial H) :
    FiniteDimensional ℝ (projection T H hH).range := by
  let : Module.Finite ℝ (TreeSpace T ⧸ (projection T H hH).ker) := tail_finite_codimension T H hH
  exact Module.Finite.of_surjective (projection T H hH).toLinearMap.quotKerEquivRange.toLinearMap
    (projection T H hH).toLinearMap.quotKerEquivRange.surjective

end TreeSpace

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

@[simp] lemma coordinate_coe (s : ι) (v : ZeroTreeVector T) :
    coordinate T s (v : ZeroTreeSpace T) = ZeroTreeVector.toTree T v s := by
  change TreeSpace.coordinate T s (inclusion T (v : ZeroTreeSpace T)) = _
  rw [inclusion_coe,TreeSpace.coordinate_coe]
  rfl

@[simp] lemma P_coe (s : ι) (v : ZeroTreeVector T) :
    P T s (v : ZeroTreeSpace T) = T.P (ZeroTreeVector.toTree T v) s := by
  unfold P
  rw [inclusion_coe,TreeSpace.P_coe]
  rfl

@[simp] lemma Q_coe (s : ι) (v : ZeroTreeVector T) :
    Q T s (v : ZeroTreeSpace T) = T.Q (ZeroTreeVector.toTree T v) s := by
  unfold Q
  rw [inclusion_coe,TreeSpace.Q_coe]
  rfl

lemma coordinates_ext {x y : ZeroTreeSpace T}
    (h : ∀ s, coordinate T s x = coordinate T s y) : x = y :=
  inclusion_injective T (TreeSpace.coordinates_ext T h)

lemma projection_fixed_iff (H : Finset ι) (hH : T.Initial H) (x : ZeroTreeSpace T) :
    projection T H hH x = x ↔ ∀ s ∉ H, coordinate T s x = 0 := by
  constructor
  · intro hx s hs
    have hh := coordinate_projection T H hH s x
    rwa [hx,ite_eq_right hs] at hh
  · intro hx
    apply coordinates_ext T
    intro s
    rw [coordinate_projection]
    split_ifs with hs
    · rfl
    · exact (hx s hs).symm

lemma mem_tail_iff (H : Finset ι) (hH : T.Initial H) (x : ZeroTreeSpace T) :
    x ∈ tail T H hH ↔ ∀ s ∈ H, coordinate T s x = 0 := by
  rw [tail_eq_coordinate_kernel]
  change headCoordinates T H x = 0 ↔ _
  constructor
  · intro hx s hs
    exact congrFun hx ⟨s,hs⟩
  · intro hx
    ext s
    exact hx s s.2

lemma projection_finite_rank (H : Finset ι) (hH : T.Initial H) :
    FiniteDimensional ℝ (projection T H hH).range := by
  let : Module.Finite ℝ (ZeroTreeSpace T ⧸ (projection T H hH).ker) := tail_finite_codimension T H hH
  exact Module.Finite.of_surjective (projection T H hH).toLinearMap.quotKerEquivRange.toLinearMap
    (projection T H hH).toLinearMap.quotKerEquivRange.surjective

end ZeroTreeSpace

theorem XZero_cubic_of_support (x : XZero) {H : Finset JoinedNode}
    (hH : joinedTree.Initial H) (hx : ∀ s ∉ H, ZeroTreeSpace.coordinate joinedTree s x = 0)
    (z : XZero) (hz : ∀ s ∈ H, ZeroTreeSpace.coordinate joinedTree s z = 0) (hz0 : z ≠ 0) :
    (‖x + z‖ + ‖x - z‖) / 2 ≥ ‖x‖ + ‖z‖ ^ 3 / (8 * (2 * ‖x‖ + ‖z‖) ^ 2) :=
  XZero_homogeneous_cubic x hH ((ZeroTreeSpace.projection_fixed_iff joinedTree H hH x).mpr hx)
    z ((ZeroTreeSpace.mem_tail_iff joinedTree H hH z).mpr hz) hz0

lemma rootSumCompletionStatement {ι : Type uIndex} [DecidableEq ι] [Infinite ι]
    (T : FiniteRootedTree ι) : RootSumCompletionStatement T where
  complete := inferInstance
  infinite_dimensional := TreeSpace.not_finite_dimensional T
  coordinate_continuous := fun s => (TreeSpace.coordinate T s).continuous
  coordinate_extends := TreeSpace.coordinate_coe T
  fields_continuous := fun s => ⟨TreeSpace.continuous_P T s,TreeSpace.continuous_Q T s⟩
  fields_extend := fun s v => ⟨TreeSpace.P_coe T s v,TreeSpace.Q_coe T s v⟩
  root_formula := TreeSpace.norm_eq T
  projections := fun H hH => ⟨TreeSpace.projection_contracts T H hH,TreeSpace.projection_idem T H hH,
    TreeSpace.coordinate_projection T H hH,TreeSpace.projection_finite_rank T H hH,
    TreeSpace.tail_closed T H hH,TreeSpace.tail_finite_codimension T H hH,
    fun x hx _ hε => TreeSpace.finite_tail_dense T H hH x hx hε⟩

lemma zeroRootCompletionStatement {ι : Type uIndex} [DecidableEq ι] [Infinite ι]
    (T : FiniteRootedTree ι) : ZeroRootCompletionStatement T where
  complete := inferInstance
  infinite_dimensional := ZeroTreeSpace.not_finite_dimensional T
  coordinate_continuous := fun s => (ZeroTreeSpace.coordinate T s).continuous
  coordinate_extends := ZeroTreeSpace.coordinate_coe T
  fields_continuous := fun s => ⟨ZeroTreeSpace.continuous_P T s,ZeroTreeSpace.continuous_Q T s⟩
  fields_extend := fun s v => ⟨ZeroTreeSpace.P_coe T s v,ZeroTreeSpace.Q_coe T s v⟩
  root_fixed := ZeroTreeSpace.root_zero T
  root_formula := ZeroTreeSpace.norm_eq_common T
  projections := fun H hH => ⟨ZeroTreeSpace.projection_contracts T H hH,ZeroTreeSpace.projection_idem T H hH,
    ZeroTreeSpace.coordinate_projection T H hH,ZeroTreeSpace.projection_finite_rank T H hH,
    ZeroTreeSpace.tail_closed T H hH,ZeroTreeSpace.tail_finite_codimension T H hH,
    fun x hx _ hε => ZeroTreeSpace.finite_tail_dense T H hH x hx hε⟩

theorem rec_completion : RootSumCompletionStatement sequenceTree ∧
    ZeroRootCompletionStatement joinedTree ∧ RootSumCompletionStatement joinedTree ∧
    IsReflexive XZero ∧ IsReflexive XJoined :=
  ⟨rootSumCompletionStatement sequenceTree,zeroRootCompletionStatement joinedTree,
    rootSumCompletionStatement joinedTree,XZero_isReflexive,XJoined_isReflexive⟩

theorem rec_main :
    (∀ t : ℝ, 0 < t → t < 1 → t^3/128 ≤ averagedModulus XSigma t ∧ t^3/128 ≤ averagedModulus XJoined t) ∧
    (∀ (H : Finset JoinedNode), joinedTree.Initial H → ∀ x : XZero,
      (∀ s ∉ H, ZeroTreeSpace.coordinate joinedTree s x = 0) → ∀ z : XZero,
      (∀ s ∈ H, ZeroTreeSpace.coordinate joinedTree s z = 0) → z ≠ 0 →
      (‖x+z‖+‖x-z‖)/2 ≥ ‖x‖+‖z‖^3/(8*(2*‖x‖+‖z‖)^2)) ∧
    (∀ A : EquivalentNorm XSigma, ¬A.AUC) ∧
    (∀ A : EquivalentNorm XZero, ¬A.AUC) ∧
    (∀ A : EquivalentNorm XJoined, ¬A.AUC) :=
  ⟨fun _ ht ht1 => ⟨XSigma_averaged_modulus ht ht1,XJoined_averaged_modulus ht ht1⟩,
    fun _ hH x hx z hz hz0 => XZero_cubic_of_support x hH hx z hz hz0,
    XSigma_no_equivalent_AUC,XZero_no_equivalent_AUC,XJoined_no_equivalent_AUC⟩

theorem stop_all_radii {t : ℝ} (ht : 0 < t) : 0 < averagedModulus XSigma t :=
  TreeSpace.averaged_modulus_pos sequenceTree ht

namespace Variable

open VariableExponent

lemma component_recursion (h : ℕ+) (x : Component h) (s : ComponentNode h) :
    (AggregationSpace.P (componentTree h) (exponent h) s x,
      AggregationSpace.Q (componentTree h) (exponent h) s x) =
    leastPair (componentCoordinate h s x)
      ((∑' c, if c ≠ (componentTree h).root ∧ (componentTree h).parent c = s then
        AggregationSpace.P (componentTree h) (exponent h) c x ^ heightExponent h else 0) ^ (1/heightExponent h))
      ((∑' c, if c ≠ (componentTree h).root ∧ (componentTree h).parent c = s then
        AggregationSpace.Q (componentTree h) (exponent h) c x ^ heightExponent h else 0) ^ (1/heightExponent h)) := by
  rw [AggregationSpace.recursion,AggregationSpace.childP_norm_formula,AggregationSpace.childQ_norm_formula]
  rfl

lemma norm_eq_nu (h : ℕ+) (x : Component h) : ‖x‖ = nu h (componentEquiv h x) := by
  rw [nu,(componentEquiv h).symm_apply_apply]
  exact AggregationSpace.norm_eq (componentTree h) (exponent h) x

lemma nu_comparisons (h : ℕ+) (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h)) :
    (h.val+1:ℝ)^(-1/heightExponent h)*‖v‖ ≤ nu h v ∧
    nu h v ≤ 2*(h.val+1:ℝ)^(1-1/heightExponent h)*‖v‖ := by
  have hh := component_comparisons h ((componentEquiv h).symm v)
  rwa [norm_eq_nu,(componentEquiv h).apply_symm_apply] at hh

lemma nu_eq_norm (h : ℕ+) (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h)) :
    nu h v = ‖(componentEquiv h).symm v‖ :=
  (AggregationSpace.norm_eq (componentTree h) (exponent h) ((componentEquiv h).symm v)).symm

lemma sourceNormStatement (h : ℕ+) : SourceNormStatement h where
  nonneg v := by rw [nu_eq_norm]; exact norm_nonneg _
  definite v := by
    rw [nu_eq_norm,norm_eq_zero]
    constructor
    · intro hv
      apply (componentEquiv h).symm.injective
      simpa only [map_zero] using hv
    · rintro rfl
      exact map_zero _
  triangle v w := by
    simp only [nu_eq_norm,map_add]
    exact norm_add_le _ _
  homogeneous a v := by
    simp only [nu_eq_norm,map_smul,norm_smul,Real.norm_eq_abs]

theorem space :
    (∀ h : ℕ+, CompleteSpace (Component h) ∧ IsReflexive (Component h) ∧
      SeparableSpace (Component h →L[ℝ] ℝ) ∧ SourceNormStatement h ∧
      ∀ v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h),
        (h.val+1:ℝ)^(-1/heightExponent h)*‖v‖ ≤ nu h v ∧
        nu h v ≤ 2*(h.val+1:ℝ)^(1-1/heightExponent h)*‖v‖) ∧
    CompleteSpace Xv ∧ IsReflexive Xv ∧ SeparableSpace (Xv →L[ℝ] ℝ) ∧
    Dense {x : Xv | FiniteTotalSupport x} ∧
    ∀ S : Finset Node, Continuous (projection S) ∧ FiniteDimensional ℝ (projection S).range ∧
      (∀ x : Xv, projection S (projection S x) = projection S x) ∧
      ∀ (s : Node) (x : Xv), coordinate s (projection S x) = if s ∈ S then coordinate s x else 0 :=
  ⟨fun h => ⟨inferInstance,component_reflexive h,inferInstance,sourceNormStatement h,nu_comparisons h⟩,
    inferInstance,reflexive,inferInstance,finite_support_dense,
    fun S => ⟨(projection S).continuous,projection_finite_rank S,projection_idem S,coordinate_projection S⟩⟩

lemma lpPotentials_recursion (h : ℕ+)
    (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h)) (s : ComponentNode h) :
    lpPotentials h v s = leastPair (v s)
      (aggregateChildren h s (fun c => (lpPotentials h v c).1))
      (aggregateChildren h s (fun c => (lpPotentials h v c).2)) := by
  have hc : componentCoordinate h s ((componentEquiv h).symm v) = v s := by
    rw [←componentEquiv_apply,(componentEquiv h).apply_symm_apply]
  simpa only [lpPotentials,aggregateChildren,hc] using
    component_recursion h ((componentEquiv h).symm v) s

lemma recursion_unique (h : ℕ+) (v : ComponentNode h → ℝ)
    (f g : ComponentNode h → ℝ × ℝ)
    (hf : ∀ s, f s = leastPair (v s)
      (aggregateChildren h s (fun c => (f c).1))
      (aggregateChildren h s (fun c => (f c).2)))
    (hg : ∀ s, g s = leastPair (v s)
      (aggregateChildren h s (fun c => (g c).1))
      (aggregateChildren h s (fun c => (g c).2))) : f = g := by
  have he : ∀ n : ℕ, ∀ s : ComponentNode h, h.val-s.1.length = n → f s = g s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs
      have hcEqual (c : ComponentNode h)
          (hc : c ≠ (componentTree h).root ∧ (componentTree h).parent c = s) : f c = g c := by
        have hstep := component_step h c hc.1
        rw [hc.2] at hstep
        change c.1.length = s.1.length+1 at hstep
        have hcHeight := c.2
        exact ih (h.val-c.1.length) (by omega) c rfl
      rw [hf s,hg s]
      have ha : aggregateChildren h s (fun c => (f c).1) = aggregateChildren h s (fun c => (g c).1) := by
        unfold aggregateChildren
        congr 1
        apply tsum_congr
        intro c
        split_ifs with hc
        · exact congrArg (fun z : ℝ × ℝ => z.1 ^ heightExponent h) (hcEqual c hc)
        · rfl
      have hb : aggregateChildren h s (fun c => (f c).2) = aggregateChildren h s (fun c => (g c).2) := by
        unfold aggregateChildren
        congr 1
        apply tsum_congr
        intro c
        split_ifs with hc
        · exact congrArg (fun z : ℝ × ℝ => z.2 ^ heightExponent h) (hcEqual c hc)
        · rfl
      rw [ha,hb]
  funext s
  exact he _ s rfl

theorem lp_model_exact (h : ℕ+)
    (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h))
    (f : ComponentNode h → ℝ × ℝ)
    (hf : ∀ s, f s = leastPair (v s)
      (aggregateChildren h s (fun c => (f c).1))
      (aggregateChildren h s (fun c => (f c).2))) :
    f = lpPotentials h v ∧ nu h v = (f (componentTree h).root).1+(f (componentTree h).root).2 := by
  have he := recursion_unique h v f (lpPotentials h v) hf (lpPotentials_recursion h v)
  refine ⟨he,?_⟩
  rw [he]
  rfl

end Variable

end RecursivePotentials

end

end OAI
