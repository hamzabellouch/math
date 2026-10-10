import OAI.Analysis.TreePotential.TreeObstruction

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

namespace FreeRoot
open TreeCalculus
open scoped Classical

/-- Free scalar labels: the first field includes the root, but the second field
    only tests genuine child increments. No root label is set equal to zero. -/
structure IsFreePotential (b : Node → ℝ) : Prop where
  label_bound : ∀ s, |b s| ≤ 1
  child_budget : QuadraticBudget .sibling (increments b)

lemma isFreePotential_iff (b : Node → ℝ) :
    IsFreePotential b ↔ IsTreeTest true .sibling (increments b) := by
  constructor
  · intro h
    exact ⟨by simp, by simpa using h.label_bound, h.child_budget, trivial⟩
  · intro h
    exact ⟨by simpa using h.potential_bound, h.quadratic_budget⟩

def includeEdge : TreeCoordinate false ↪ TreeCoordinate true where
  toFun := fun s => ⟨s.val, Or.inl rfl⟩
  inj' := by intro s t h; exact Subtype.ext (congrArg (fun u : TreeCoordinate true => u.val) h)

@[simp] lemma includeEdge_apply (s : TreeCoordinate false) :
    includeEdge s = (⟨s.val, Or.inl rfl⟩ : TreeCoordinate true) := rfl

@[simp] lemma includeEdge_child (s : Node) (n : ℕ) :
    includeEdge (childCoordinate false s n) = childCoordinate true s n := rfl

/-- The defining free-root norm uses only genuine edges. It is a restriction of
    the rooted-sibling test family, NOT the anchored rootless sibling family. -/
def freeTestFamily : TestFamily (TreeCoordinate false) :=
  restrictedTestFamily (treeTestFamily true .sibling) includeEdge

/-- The free-root test and norm correspondence retains the existence of a free root value. -/

theorem mem_freeTestFamily_iff (f : TreeCoordinate false → ℝ) :
    f ∈ freeTestFamily.carrier ↔ ∃ b : Node → ℝ, IsFreePotential b ∧
      ∀ s : TreeCoordinate false, f s = b s.val - b s.val.dropLast := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨potential (liftCoefficients true g.val), ?_, ?_⟩
    · apply (isFreePotential_iff _).mpr
      have hfun : increments (potential (liftCoefficients true g.val)) = liftCoefficients true g.val :=
        funext (increments_potential _)
      rw [hfun]
      exact g.property
    · intro s
      have hs : s.val ≠ [] := by simpa using s.property
      have h := increments_potential (liftCoefficients true g.val) s.val
      rw [increments, ite_eq_right hs] at h
      exact h.symm.trans (by simp only [])
  · rintro ⟨b, hb, hf⟩
    have htest := (isFreePotential_iff b).mp hb
    refine ⟨asTreeTest (increments b) htest, ?_⟩
    funext s
    have hs : s.val ≠ [] := by simpa using s.property
    apply (hf s).trans
    change b s.val - b s.val.dropLast = increments b s.val
    simp only [increments, ite_eq_right hs]

abbrev Space := TestCompletion freeTestFamily

def rootedInclusion : Space →L[ℝ] TestCompletion (treeTestFamily true .sibling) :=
  restrictedCompletionInclusion (treeTestFamily true .sibling) includeEdge

lemma rootedInclusion_norm (x : Space) : ‖rootedInclusion x‖ = ‖x‖ :=
  restrictedCompletionInclusion_norm _ _ x

lemma rootedInclusion_vector (i : TreeCoordinate false) :
    rootedInclusion (coordinateVector freeTestFamily i) =
      coordinateVector (treeTestFamily true .sibling) (includeEdge i) :=
  restrictedCompletionInclusion_vector _ _ i

/-- The edge space embeds isometrically as the root-coordinate-zero subspace of the rooted sibling model. The inherited estimate implies the free-root bound. -/


theorem freeRoot_stronger_modulus {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ((Real.sqrt (1+t^2/4)-1 : ℝ) : EReal) ≤ averagedModulus Space t := by
  apply averaged_tail_bound_pullback rootedInclusion rootedInclusion_norm
  intro x hx ε hε
  exact four_completed_tail_bound ht ht1 x hx hε

lemma distinct_bound_le_common (t : ℝ) :
    (Real.sqrt (1+t^2/576)-1)/4 ≤ Real.sqrt (1+t^2/4)-1 := by
  have hsmall : 1 ≤ Real.sqrt (1+t^2/576) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [sq_nonneg t]
  have hbig : Real.sqrt (1+t^2/576) ≤ Real.sqrt (1+t^2/4) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
  linarith

theorem freeRoot_averaged_modulus {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (((Real.sqrt (1+t^2/576)-1)/4 : ℝ) : EReal) ≤ averagedModulus Space t :=
  (EReal.coe_le_coe_iff.mpr (distinct_bound_le_common t)).trans (freeRoot_stronger_modulus ht ht1)

lemma rootless_restricted_potential (g : treeTestFamily true .sibling) (s : Node) :
    potential (liftCoefficients false (g.val ∘ includeEdge)) s =
      potential (liftCoefficients true g.val) s - liftCoefficients true g.val [] := by
  induction s using List.reverseRecOn with
  | nil => simp [liftCoefficients]
  | append_singleton s n ih =>
    rw [potential_child, potential_child, ih]
    have hc : liftCoefficients false (g.val ∘ includeEdge) (s ++ [n]) =
        liftCoefficients true g.val (s ++ [n]) := by
      simp [liftCoefficients]
    rw [hc]
    ring

def path (s : Node) : Space :=
  ((testVectorEquiv freeTestFamily).symm (pathArray false s) : TestVector freeTestFamily)

lemma norm_path_bounds (s : Node) (hs : s ≠ []) : 1 ≤ ‖path s‖ ∧ ‖path s‖ ≤ 2 := by
  simp only [path, UniformSpace.Completion.norm_coe, norm_testVector_equiv,
    LinearEquiv.apply_symm_apply]
  constructor
  · have h := coordinate_le_testNorm freeTestFamily (pathArray false s) ⟨s, Or.inr hs⟩
    simpa only [pathArray_apply, List.prefix_rfl, ite_true, abs_one] using h
  · apply ciSup_le
    rintro ⟨f, g, rfl⟩
    rw [finitePairing_pathArray, rootless_restricted_potential]
    calc
      _ ≤ |potential (liftCoefficients true g.val) s| + |liftCoefficients true g.val []| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (g.property.potential_bound s)
        (by simpa using g.property.potential_bound [])
      _ = 2 := by norm_num

lemma path_child_sub (s : Node) (n : ℕ) :
    path (s ++ [n]) - path s = coordinateVector freeTestFamily (childCoordinate false s n) := by
  simp only [path, pathArray_child, map_add, UniformSpace.Completion.coe_add, add_sub_cancel_left]
  simp only [nodeArray, show false = true ∨ s ++ [n] ≠ [] from Or.inr (by simp),
    dite_true, coordinateVector, childCoordinate]

lemma free_sibling_hilbert_upper (s : Node) (A : Finset ℕ) (a : ℕ → ℝ) :
    ‖∑ n ∈ A, a n • coordinateVector freeTestFamily (childCoordinate false s n)‖ ≤
      Real.sqrt (∑ n ∈ A, (a n)^2) := by
  rw [← rootedInclusion_norm]
  simp only [map_sum, map_smul, rootedInclusion_vector, includeEdge_child]
  exact sibling_hilbert_upper true .sibling s A a

lemma free_siblings_weaklyNull (s : Node) :
    WeaklyNull (fun n => coordinateVector freeTestFamily (childCoordinate false s n)) :=
  weaklyNull_of_hilbert_upper _ (free_sibling_hilbert_upper s)

def boundedTree (h : ℕ) (s : Tree h) : Space := path ([0] ++ s.val)

lemma boundedTree_difference (h : ℕ) (s : Tree h) (hs : s.val.length < h) (n : ℕ) :
    boundedTree h (child s hs n) - boundedTree h s =
      coordinateVector freeTestFamily (childCoordinate false ([0] ++ s.val) n) := by
  change path ([0] ++ (s.val ++ [n])) - path ([0] ++ s.val) = _
  rw [← List.append_assoc, path_child_sub]

theorem freeRoot_renorming_obstruction {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Space ≃L[ℝ] Y) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (he : ∀ x, α * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β * ‖x‖) :
    oneSidedModulus Y (α/(4*β)) = 0 := by
  have hb : ∀ h, 1 ≤ h → ∀ s : Tree h,
      (1 : ℝ) ≤ ‖boundedTree h s‖ ∧ ‖boundedTree h s‖ ≤ 2 := by
    intro h hh s
    exact norm_path_bounds _ (by simp)
  have hw : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => boundedTree h (child s hs n) - boundedTree h s) := by
    intro h hh s hs
    simp only [boundedTree_difference]
    exact free_siblings_weaklyNull _
  have hi : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      (1 : ℝ) ≤ ‖boundedTree h (child s hs n) - boundedTree h s‖ := by
    intro h hh s hs n
    simp only [boundedTree_difference, norm_coordinateVector, le_refl]
  have hz := bounded_tree_renorming_obstruction boundedTree zero_lt_one (by norm_num : (1:ℝ) ≤ 2)
    zero_lt_one hb hw hi e hα hαβ he
  convert hz using 1 ; congr 1 ; ring

theorem freeRoot_no_equivalent_AUC {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Space ≃L[ℝ] Y) : ¬ IsAUC Y := by
  obtain ⟨α, β, hα, hαβ, he⟩ := continuousEquiv_bounds e
  have hβ : 0 < β := hα.trans_le hαβ
  intro hauc
  have hp := hauc (α/(4*β)) (by positivity)
  rw [freeRoot_renorming_obstruction e hα hαβ he] at hp
  exact lt_irrefl _ hp

end FreeRoot


end BoundedTreePotentials

end

end OAI
