import OAI.Analysis.TreePotential.UniformProtocols

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

/-- The start antichain convention is equivalent to nodewise incomparability,
not merely disjointness of segments. -/

theorem incomparable_iff_nodewise (F : Finset Segment) :
    Incomparable F ↔ ∀ S ∈ F, ∀ T ∈ F, S ≠ T →
      ∀ s ∈ S.nodes, ∀ t ∈ T.nodes, ¬Prefix s t ∧ ¬Prefix t s := by
  constructor
  · intro h S hS T hT hne s hs t ht
    exact incomparable_nodes h hS hT hne hs ht
  · intro h S hS T hT hne
    exact h S hS T hT hne S.start S.start_mem T.start T.start_mem

/-- Literal finite segment evaluation, with each coordinate extended to the
completion by its proved continuous functional. -/
def completedSegmentEval (S : Segment) : Predual →L[ℝ] ℝ :=
  ∑ v ∈ S.nodes, coordinateFunctional atomTests v

@[simp] lemma completedSegmentEval_coe (S : Segment) (g : TestVector atomTests) :
    completedSegmentEval S (g : Predual)=S.eval (testVectorEquiv atomTests g) := by
  simp [completedSegmentEval,Segment.eval]

lemma completedAtomTest_eval (A : Atom) (g : Predual) :
    completedTestFunctional atomTests ⟨A.profile,⟨A,rfl⟩⟩ g=
      ∑ S ∈ A.family,A.coeff S*completedSegmentEval S g := by
  refine UniformSpace.Completion.induction_on g
    (isClosed_eq (completedTestFunctional atomTests _).continuous
      (continuous_finsetSum _ (fun S _ => continuous_const.mul (completedSegmentEval S).continuous))) ?_
  intro z
  simp only [completedTestFunctional_coe,completedSegmentEval_coe]
  change finitePairing A.profile (testVectorEquiv atomTests z)=_
  exact finitePairing_profile A (testVectorEquiv atomTests z)

lemma completed_predual_family_energy (g : Predual) (F : Finset Segment) (hF : Incomparable F) :
    (∑ S ∈ F,(completedSegmentEval S g)^2)≤‖g‖^2 := by
  refine UniformSpace.Completion.induction_on g
    (isClosed_le (continuous_finsetSum _ (fun S _ => (completedSegmentEval S).continuous.pow 2))
      (continuous_norm.pow 2)) ?_
  intro z
  simp only [completedSegmentEval_coe,UniformSpace.Completion.norm_coe]
  exact predual_family_energy (testVectorEquiv atomTests z) F hF

/-- The exact segment norm supremum on the full completion equals the atom-testing norm. -/

theorem predual_norm_formula (g : Predual) :
    ‖g‖=⨆ F : {F : Finset Segment // Incomparable F},
      Real.sqrt (∑ S ∈ F.val,(completedSegmentEval S g)^2) := by
  let : Nonempty {F : Finset Segment // Incomparable F} :=
    ⟨⟨∅,by intro S hS; simp at hS⟩⟩
  have hbound (F : {F : Finset Segment // Incomparable F}) :
      Real.sqrt (∑ S ∈ F.val,(completedSegmentEval S g)^2)≤‖g‖ := by
    have hh := completed_predual_family_energy g F.val F.property
    have hn : 0≤∑ S ∈ F.val,(completedSegmentEval S g)^2 :=
      Finset.sum_nonneg fun S _ => sq_nonneg _
    nlinarith [Real.sq_sqrt hn,Real.sqrt_nonneg (∑ S ∈ F.val,(completedSegmentEval S g)^2),norm_nonneg g]
  have hb : BddAbove (Set.range (fun F : {F : Finset Segment // Incomparable F} =>
      Real.sqrt (∑ S ∈ F.val,(completedSegmentEval S g)^2))) :=
    ⟨‖g‖,by rintro _ ⟨F,rfl⟩; exact hbound F⟩
  apply le_antisymm
  · rw [completed_tests_norming]
    apply ciSup_le
    rintro ⟨f,A,rfl⟩
    rw [completedAtomTest_eval]
    apply le_trans _ (le_ciSup hb ⟨A.family,A.incomparable⟩)
    have he : 0≤∑ S ∈ A.family,(completedSegmentEval S g)^2 :=
      Finset.sum_nonneg fun S _ => sq_nonneg _
    have hc := Finset.sum_mul_sq_le_sq_mul_sq A.family A.coeff (fun S => completedSegmentEval S g)
    have hp := mul_le_of_le_one_left he A.budget
    nlinarith [Real.sq_sqrt he,Real.sqrt_nonneg (∑ S ∈ A.family,(completedSegmentEval S g)^2)]
  · exact ciSup_le hbound

/-- The exact original c00 norm used to form the predual completion. -/
theorem predual_finite_norm_formula (g : Node →₀ ℝ) :
    testNorm atomTests g=⨆ F : {F : Finset Segment // Incomparable F},
      Real.sqrt (∑ S ∈ F.val,(S.eval g)^2) := by
  have hh := predual_norm_formula (((testVectorEquiv atomTests).symm g : TestVector atomTests) : Predual)
  simpa only [completedSegmentEval_coe,LinearEquiv.apply_symm_apply,
    UniformSpace.Completion.norm_coe,norm_testVector_equiv] using hh

end BoundedTreePotentials.Segments

namespace BoundedTreePotentials

/-- Canonical coordinates in every finite-height component, including the
last level (not only the shallower nodes used in the obstruction trees). -/
def linearOuterCoordinate (n : ℕ) (s : Tree (n+1)) : LinearOuter :=
  linearOuterInsert n ((linearBlockHilbertEquiv (n+1)).symm (lp.single 2 s 1))

def linearOuterPath (n : ℕ) (s : Tree (n+1)) : LinearOuter :=
  linearOuterInsert n ((linearBlockHilbertEquiv (n+1)).symm (rootPath s))

@[simp] theorem linearOuterCoordinate_norm (n : ℕ) (s : Tree (n+1)) :
    ‖linearOuterCoordinate n s‖=1 := by
  simp only [linearOuterCoordinate,linearOuterInsert,lp.singleContinuousLinearMap_apply,
    lp.norm_single (by norm_num : (0:ℝ≥0∞)<2)]
  exact linearBlockCost_singleton s

@[simp] theorem linearOuterPath_norm (n : ℕ) (s : Tree (n+1)) :
    ‖linearOuterPath n s‖=1 := by
  simp only [linearOuterPath,linearOuterInsert,lp.singleContinuousLinearMap_apply,
    lp.norm_single (by norm_num : (0:ℝ≥0∞)<2)]
  exact linearBlockCost_rootPath s

theorem linearOuter_children_weaklyNull (n : ℕ) (s : Tree (n+1)) (hs : s.val.length<n+1) :
    WeaklyNull (fun j => linearOuterCoordinate n (child s hs j)) := by
  have hw := single_sequence_weaklyNull (fun j => child s hs j) (by
    intro i j hij
    exact TreeCalculus.childNode_injective s.val (congrArg Subtype.val hij))
  exact (hw.map (linearBlockHilbertEquiv (n+1)).symm.toContinuousLinearMap).map (linearOuterInsert n)

namespace Segments

/-- The incomparable tail bound. -/
theorem incomparable_tail_head_zero {E : Finset Node} (hE : Initial (E : Set Node))
    (x y : Dual) (hx : dualHead E x=x) (hy : dualTail E y=y)
    (hp : ‖x+y‖≤1) (hm : ‖x-y‖≤1) :
    ‖y‖≤(Real.sqrt 2+Real.sqrt 6)*Real.sqrt (1-‖x‖) := by
  simpa only [hy] using incomparable_tail hE x y hx hp hm

end Segments

/-- Completeness statements for the literal infimal-cost norm instances. -/
theorem linearBlock_complete (n : ℕ) : CompleteSpace (LinearBlock n) := inferInstance
theorem linearOuter_complete : CompleteSpace LinearOuter := inferInstance
theorem quadraticBlock_complete (n : ℕ) : CompleteSpace (QuadraticBlock n) := inferInstance
theorem quadraticOuter_complete : CompleteSpace QuadraticOuter := inferInstance
theorem freeRoot_complete : CompleteSpace FreeRoot.Space := inferInstance

namespace CostHeads

/-- The exact real sphere-infimum formulation, with positive e_t chosen independently
of the unit center. -/

theorem quadratic_uniform_sphere_infimum {t : ℝ} (ht : 0<t) :
    ∃ e : ℝ,0<e ∧ ∀ x : QuadraticOuter,‖x‖=1 →
      ∃ F : ClosedFiniteCodim QuadraticOuter,
        1+e≤⨅ u : {u : QuadraticOuter // u ∈ F.space ∧ ‖u‖=1},
          max ‖x+t • u.val‖ ‖x-t • u.val‖ := by
  obtain ⟨e,he,hmain⟩ := quadratic_uniform_maximum ht
  refine ⟨e,he,?_⟩
  intro x hx
  obtain ⟨F,hF⟩ := hmain x hx
  obtain ⟨u,hu,hun⟩ := F.unit_exists QuadraticOuter
    (infiniteDimensional_of_not_isAUC _ (quadraticOuter_no_equivalent_AUC (.refl ℝ _)))
  have : Nonempty {u : QuadraticOuter // u ∈ F.space ∧ ‖u‖=1} := ⟨⟨u,hu,hun⟩⟩
  exact ⟨F,le_ciInf (fun v => hF v.val v.property.1 v.property.2)⟩

end CostHeads
namespace Segments

theorem predualBlock_complete (n : ℕ) : CompleteSpace (PredualBlock n) := inferInstance
theorem predual_complete : CompleteSpace Predual := inferInstance
theorem incomparable_complete : CompleteSpace Dual := inferInstance
theorem startBlock_complete (n : ℕ) : CompleteSpace (StartBlock n) := inferInstance
theorem start_complete : CompleteSpace StartSpace := inferInstance

end Segments
end BoundedTreePotentials

end

end OAI
