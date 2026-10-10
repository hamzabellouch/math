import OAI.Analysis.TreePotential.WeakNull

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

namespace TreeCalculus
open scoped Classical

def nodeArray (r : Bool) (s : Node) : TreeCoordinate r →₀ ℝ :=
  if h : r = true ∨ s ≠ [] then Finsupp.single ⟨s,h⟩ 1 else 0

def pathArray (r : Bool) (s : Node) : TreeCoordinate r →₀ ℝ :=
  (s.inits.map (nodeArray r)).sum

lemma finitePairing_nodeArray (r : Bool) (f : TreeCoordinate r → ℝ) (s : Node) :
    finitePairing f (nodeArray r s) = liftCoefficients r f s := by
  by_cases h : r = true ∨ s ≠ []
  · simp [nodeArray, h, finitePairing, liftCoefficients]
  · simp [nodeArray, h, liftCoefficients]

lemma finitePairing_pathArray (r : Bool) (f : TreeCoordinate r → ℝ) (s : Node) :
    finitePairing f (pathArray r s) = potential (liftCoefficients r f) s := by
  simp only [pathArray, map_list_sum, List.map_map, Function.comp_def,
    finitePairing_nodeArray, potential]

lemma pathArray_child (r : Bool) (s : Node) (n : ℕ) :
    pathArray r (s ++ [n]) = pathArray r s + nodeArray r (s ++ [n]) := by
  simp [pathArray, List.inits_append]

lemma pathArray_apply (r : Bool) (s : Node) (i : TreeCoordinate r) :
    pathArray r s i = if i.val <+: s then 1 else 0 := by
  rw [← finitePairing_single_test (pathArray r s) i, finitePairing_pathArray]
  trans potential (Pi.single i.val (1 : ℝ)) s
  · congr 1
    ext u
    by_cases hu : r = true ∨ u ≠ []
    · simp [liftCoefficients, hu, Pi.single_apply, Subtype.ext_iff]
    · have hn : u ≠ i.val := by rintro rfl; exact hu i.property
      simp [liftCoefficients, hu, hn]
  · exact potential_single i.val s

lemma testNorm_pathArray_le (r : Bool) (k : QuadraticKind) (s : Node) :
    testNorm (treeTestFamily r k) (pathArray r s) ≤ 1 := by
  apply ciSup_le
  intro f
  rw [finitePairing_pathArray]
  exact f.property.potential_bound s

lemma testNorm_pathArray (r : Bool) (k : QuadraticKind) (s : Node)
    (hs : r = true ∨ s ≠ []) : testNorm (treeTestFamily r k) (pathArray r s) = 1 := by
  apply le_antisymm (testNorm_pathArray_le r k s)
  have h := coordinate_le_testNorm (treeTestFamily r k) (pathArray r s) ⟨s,hs⟩
  simpa only [pathArray_apply, List.prefix_rfl, ite_true, abs_one] using h

def treePath (r : Bool) (k : QuadraticKind) (s : Node) : TestCompletion (treeTestFamily r k) :=
  ((testVectorEquiv (treeTestFamily r k)).symm (pathArray r s) : TestVector (treeTestFamily r k))

lemma norm_treePath (r : Bool) (k : QuadraticKind) (s : Node) (hs : r = true ∨ s ≠ []) :
    ‖treePath r k s‖ = 1 := by
  simp only [treePath, UniformSpace.Completion.norm_coe, norm_testVector_equiv,
    LinearEquiv.apply_symm_apply]
  exact testNorm_pathArray r k s hs

def childCoordinate (r : Bool) (s : Node) (n : ℕ) : TreeCoordinate r :=
  ⟨s ++ [n], Or.inr (by simp)⟩

lemma treePath_child_sub (r : Bool) (k : QuadraticKind) (s : Node) (n : ℕ) :
    treePath r k (s ++ [n]) - treePath r k s =
      coordinateVector (treeTestFamily r k) (childCoordinate r s n) := by
  simp only [treePath, pathArray_child, map_add, UniformSpace.Completion.coe_add,
    add_sub_cancel_left]
  simp only [nodeArray, show r = true ∨ s ++ [n] ≠ [] from Or.inr (by simp),
    dite_true, coordinateVector, childCoordinate]

lemma childNode_injective (s : Node) : Function.Injective (fun n : ℕ => s ++ [n]) := by
  intro n m h
  simpa using List.append_cancel_left h

lemma sibling_quadraticGroup (k : QuadraticKind) (s : Node) (A : Finset ℕ) :
    QuadraticGroup k (A.image (fun n => s ++ [n])) := by
  cases k with
  | sibling =>
    refine ⟨s, ?_⟩
    intro u hu
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨n, rfl⟩
  | antichain =>
    intro u hu v hv huv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
    constructor
    · intro hp
      apply huv
      exact hp.eq_of_length (by simp)
    · intro hp
      apply huv
      exact (hp.eq_of_length (by simp)).symm
  | global => trivial

lemma sibling_sq_sum_le {r : Bool} {k : QuadraticKind}
    (f : treeTestFamily r k) (s : Node) (A : Finset ℕ) :
    ∑ n ∈ A, f.val (childCoordinate r s n)^2 ≤ 1 := by
  have h := f.property.quadratic_budget (A.image (fun n => s ++ [n]))
    (sibling_quadraticGroup k s A)
  rw [Finset.sum_image (fun i hi j hj hij => childNode_injective s hij)] at h
  simpa only [← liftCoefficients_coord, childCoordinate] using h

lemma completedTestFunctional_vector {I : Type*} (K : TestFamily I) (f : K) (i : I) :
    completedTestFunctional K f (coordinateVector K i) = f.val i := by
  rw [coordinateVector, completedTestFunctional_coe]
  change finitePairing f.val (Finsupp.single i 1) = f.val i
  simp [finitePairing]

/-- Siblings have the asserted Hilbert upper estimate in each different model. -/
theorem sibling_hilbert_upper (r : Bool) (k : QuadraticKind) (s : Node)
    (A : Finset ℕ) (a : ℕ → ℝ) :
    ‖∑ n ∈ A, a n • coordinateVector (treeTestFamily r k) (childCoordinate r s n)‖ ≤
      Real.sqrt (∑ n ∈ A, (a n)^2) := by
  rw [completed_tests_norming]
  apply ciSup_le
  intro f
  simp only [map_sum, map_smul, completedTestFunctional_vector, smul_eq_mul]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq A a (fun n => f.val (childCoordinate r s n))
  have hf := sibling_sq_sum_le f s A
  have hS : 0 ≤ ∑ n ∈ A, (a n)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs : (∑ n ∈ A, a n * f.val (childCoordinate r s n))^2 ≤ ∑ n ∈ A, (a n)^2 :=
    hc.trans ((mul_le_mul_of_nonneg_left hf hS).trans_eq (mul_one _))
  nlinarith [Real.sq_sqrt hS, Real.sqrt_nonneg (∑ n ∈ A, (a n)^2)]

lemma siblings_weaklyNull (r : Bool) (k : QuadraticKind) (s : Node) :
    WeaklyNull (fun n => coordinateVector (treeTestFamily r k) (childCoordinate r s n)) :=
  weaklyNull_of_hilbert_upper _ (sibling_hilbert_upper r k s)

/-- Shift by the fixed nonroot vertex [0], so the rootless row also starts at a
    nonzero path. No root coefficient is inserted in that row. -/
def fourBoundedTree (r : Bool) (k : QuadraticKind) (h : ℕ) (s : Tree h) :
    TestCompletion (treeTestFamily r k) := treePath r k ([0] ++ s.val)

lemma fourBoundedTree_norm (r : Bool) (k : QuadraticKind) (h : ℕ) (s : Tree h) :
    ‖fourBoundedTree r k h s‖ = 1 := by
  exact norm_treePath r k _ (Or.inr (by simp))

lemma fourBoundedTree_difference (r : Bool) (k : QuadraticKind) (h : ℕ)
    (s : Tree h) (hs : s.val.length < h) (n : ℕ) :
    fourBoundedTree r k h (child s hs n) - fourBoundedTree r k h s =
      coordinateVector (treeTestFamily r k) (childCoordinate r ([0] ++ s.val) n) := by
  change treePath r k ([0] ++ (s.val ++ [n])) - treePath r k ([0] ++ s.val) = _
  rw [← List.append_assoc]
  exact treePath_child_sub r k _ n

/-- Exact zero radius for every equivalent norm represented on a continuous-linearly-equivalent real normed space. -/

theorem four_renorming_obstruction (r : Bool) (k : QuadraticKind)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (he : ∀ x, α * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β * ‖x‖) :
    oneSidedModulus Y (α / (2 * β)) = 0 := by
  have hb : ∀ h, 1 ≤ h → ∀ s : Tree h,
      (1 : ℝ) ≤ ‖fourBoundedTree r k h s‖ ∧ ‖fourBoundedTree r k h s‖ ≤ 1 := by
    intro h hh s
    simp only [fourBoundedTree_norm, le_refl, and_self]
  have hw : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => fourBoundedTree r k h (child s hs n) - fourBoundedTree r k h s) := by
    intro h hh s hs
    simp only [fourBoundedTree_difference]
    exact siblings_weaklyNull r k _
  have hi : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      (1 : ℝ) ≤ ‖fourBoundedTree r k h (child s hs n) - fourBoundedTree r k h s‖ := by
    intro h hh s hs n
    simp only [fourBoundedTree_difference, norm_coordinateVector, le_refl]
  simpa only [mul_one] using bounded_tree_renorming_obstruction
    (fourBoundedTree r k) zero_lt_one le_rfl zero_lt_one hb hw hi e hα hαβ he

end TreeCalculus
section EquivalenceBounds
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma continuousEquiv_bounds (e : E ≃L[ℝ] Y) :
    ∃ α β : ℝ, 0 < α ∧ α ≤ β ∧ ∀ x, α * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β * ‖x‖ := by
  let A := ‖e.symm.toContinuousLinearMap‖ + 1
  let B := ‖e.toContinuousLinearMap‖ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by dsimp [A]; linarith [norm_nonneg e.symm.toContinuousLinearMap]
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg e.toContinuousLinearMap]
  refine ⟨A⁻¹, B, inv_pos.mpr hA, (inv_le_one₀ hA).mpr hA1 |>.trans hB1, ?_⟩
  intro x
  constructor
  · have h := e.symm.toContinuousLinearMap.le_opNorm (e x)
    change ‖e.symm (e x)‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ at h
    rw [e.symm_apply_apply] at h
    have hu : ‖x‖ ≤ A * ‖e x‖ := by
      dsimp [A]
      nlinarith [norm_nonneg (e x)]
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hA), one_mul] using
      mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hA.le)
  · have h := e.toContinuousLinearMap.le_opNorm x
    change ‖e x‖ ≤ ‖e.toContinuousLinearMap‖ * ‖x‖ at h
    dsimp [B]
    nlinarith [norm_nonneg x]

end EquivalenceBounds

namespace TreeCalculus

theorem four_no_equivalent_AUC (r : Bool) (k : QuadraticKind)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) : ¬ IsAUC Y := by
  obtain ⟨α, β, hα, hαβ, he⟩ := continuousEquiv_bounds e
  have hβ : 0 < β := hα.trans_le hαβ
  intro hauc
  have hp := hauc (α/(2*β)) (by positivity)
  rw [four_renorming_obstruction r k e hα hαβ he] at hp
  exact lt_irrefl _ hp

end TreeCalculus

section RestrictedTests
open scoped Classical
variable {I J : Type*}

/-- Restrict coefficient tests to an injected coordinate set, without imposing
    any condition on the omitted coefficients. -/
def restrictedTestFamily (K : TestFamily I) (ι : J ↪ I) : TestFamily J where
  carrier := {g | ∃ f : K, g = f.val ∘ ι}
  zero_mem := ⟨⟨0, K.zero_mem⟩, rfl⟩
  neg_mem := by
    rintro g ⟨f, rfl⟩
    exact ⟨⟨-f.val, K.neg_mem _ f.property⟩, rfl⟩
  coeff_bound := by
    rintro g ⟨f, rfl⟩ j
    exact K.coeff_bound _ f.property (ι j)
  singleton_mem := by
    intro j
    refine ⟨⟨_, K.singleton_mem (ι j)⟩, ?_⟩
    funext l
    simp only [Function.comp_def, ι.injective.eq_iff]

lemma finitePairing_embDomain (ι : J ↪ I) (f : I → ℝ) (x : J →₀ ℝ) :
    finitePairing f (Finsupp.embDomain ι x) = finitePairing (f ∘ ι) x :=
  Finsupp.linearCombination_embDomain ℝ ι x

lemma testNorm_restricted (K : TestFamily I) (ι : J ↪ I) (x : J →₀ ℝ) :
    testNorm (restrictedTestFamily K ι) x = testNorm K (Finsupp.embDomain ι x) := by
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨g, f, rfl⟩
    rw [← finitePairing_embDomain ι f.val x]
    exact finitePairing_le_testNorm K f _
  · apply ciSup_le
    intro f
    rw [finitePairing_embDomain]
    exact finitePairing_le_testNorm (restrictedTestFamily K ι) ⟨_, f, rfl⟩ x

def restrictedVectorInclusion (K : TestFamily I) (ι : J ↪ I) :
    TestVector (restrictedTestFamily K ι) →ₗᵢ[ℝ] TestVector K where
  toLinearMap := (testVectorEquiv K).symm.toLinearMap.comp
    ((Finsupp.lmapDomain ℝ ℝ ι).comp (testVectorEquiv (restrictedTestFamily K ι)).toLinearMap)
  norm_map' := by
    intro x
    change testNorm K (Finsupp.mapDomain ι ((testVectorEquiv _ ) x)) =
      testNorm (restrictedTestFamily K ι) ((testVectorEquiv _) x)
    rw [← Finsupp.embDomain_eq_mapDomain, testNorm_restricted]

def restrictedCompletionInclusion (K : TestFamily I) (ι : J ↪ I) :
    TestCompletion (restrictedTestFamily K ι) →L[ℝ] TestCompletion K :=
  (UniformSpace.Completion.toComplL.comp (restrictedVectorInclusion K ι).toContinuousLinearMap).extend
    UniformSpace.Completion.toComplL

lemma restrictedCompletionInclusion_coe (K : TestFamily I) (ι : J ↪ I)
    (x : TestVector (restrictedTestFamily K ι)) :
    restrictedCompletionInclusion K ι x = (restrictedVectorInclusion K ι x : TestCompletion K) := by
  exact (UniformSpace.Completion.toComplL.comp (restrictedVectorInclusion K ι).toContinuousLinearMap).extend_eq
    UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformEmbedding_coe _).isUniformInducing x

lemma restrictedCompletionInclusion_norm (K : TestFamily I) (ι : J ↪ I)
    (x : TestCompletion (restrictedTestFamily K ι)) :
    ‖restrictedCompletionInclusion K ι x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (restrictedCompletionInclusion K ι).continuous.norm continuous_norm) ?_
  intro w
  rw [restrictedCompletionInclusion_coe, UniformSpace.Completion.norm_coe,
    LinearIsometry.norm_map, UniformSpace.Completion.norm_coe]

lemma restrictedCompletionInclusion_vector (K : TestFamily I) (ι : J ↪ I) (j : J) :
    restrictedCompletionInclusion K ι (coordinateVector (restrictedTestFamily K ι) j) =
      coordinateVector K (ι j) := by
  rw [coordinateVector, restrictedCompletionInclusion_coe]
  congr 1
  change (testVectorEquiv K).symm (Finsupp.mapDomain ι (Finsupp.single j 1)) = _
  rw [Finsupp.mapDomain_single]

end RestrictedTests

section ModulusPullback
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def pullbackFiniteCodim (e : E →L[ℝ] Y) (F : ClosedFiniteCodim Y) : ClosedFiniteCodim E := by
  letI : IsClosed (F.space : Set Y) := F.closed
  letI : Module.Finite ℝ (Y ⧸ F.space) := F.finiteCodim
  exact {
    space := (F.space.mkQL.comp e).ker
    closed := (F.space.mkQL.comp e).isClosed_ker
    finiteCodim := Module.Finite.equiv (F.space.mkQL.comp e).toLinearMap.quotKerEquivRange.symm }

lemma mem_pullbackFiniteCodim (e : E →L[ℝ] Y) (F : ClosedFiniteCodim Y) (x : E) :
    x ∈ (pullbackFiniteCodim e F).space ↔ e x ∈ F.space := by
  change F.space.mkQ (e x) = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero F.space

lemma averaged_tail_bound_pullback (e : E →L[ℝ] Y) (he : ∀ x, ‖e x‖ = ‖x‖)
    {t b : ℝ}
    (h : ∀ x : Y, ‖x‖ = 1 → ∀ ε : ℝ, 0 < ε → ∃ F : ClosedFiniteCodim Y,
      ∀ y : Y, y ∈ F.space → 1 ≤ ‖y‖ →
        b - ε ≤ (‖x + t • y‖ + ‖x - t • y‖)/2 - 1) :
    (b : EReal) ≤ averagedModulus E t := by
  apply averagedModulus_lower_bound
  intro x hx ε hε
  obtain ⟨F, hF⟩ := h (e x) (by rw [he, hx]) ε hε
  refine ⟨pullbackFiniteCodim e F, ?_⟩
  intro y hy hyn
  have hb := hF (e y) ((mem_pullbackFiniteCodim e F y).mp hy) (by rwa [he])
  simpa only [← map_smul, ← map_add, ← map_sub, he] using hb

end ModulusPullback

end BoundedTreePotentials

end

end OAI
