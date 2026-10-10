import OAI.Geometry.Arnold.Kernel

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field
open scoped ContDiff Topology

lemma rotation_finish_neg (z : CV) (hz : z 0 = 0) : rotationPath (1,z) = -z := by
  rw [rotationPath_finish]
  ext j
  by_cases hj : j = 0
  · subst j
    simp [hz]
  · simp [hj]

lemma forwardMid_zeroVector (t : ℝ) : forwardMid (t,zeroVector) = zeroVector :=
  Midpoint.step_equilibrium _ lipschitz parameter parameter_contract t zeroVector vectorField_zeroVector

lemma forwardMid_kernel (t : ℝ) :
    fderiv ℝ (fun w ↦ forwardMid (t,w)) zeroVector kernelVector = kernelVector :=
  Midpoint.step_kernel _ lipschitz vectorField_smooth parameter parameter_contract parameter_smooth
    t zeroVector kernelVector vectorField_zeroVector vectorField_kernel

/-- Fix the phase of the lift at the degenerate point. -/
def degenerateLift (w : CV) : CV := -forward (1,w)

lemma degenerateLift_smooth : ContDiff ℝ ∞ degenerateLift :=
  (forward_smooth.comp (contDiff_const.prodMk contDiff_id)).neg

lemma degenerateLift_zeroVector : degenerateLift zeroVector = zeroVector := by
  rw [degenerateLift, forward, forwardMid_zeroVector, rotation_finish_neg zeroVector (by rfl), neg_neg]

lemma degenerateLift_preserves (z : UnitQuadric) : IsUnitQuadric (degenerateLift z) := by
  have hu := forward_preserves 1 z
  change IsUnitQuadric (-forward (1,z))
  rw [← neg_one_smul ℂ (forward (1,z))]
  constructor
  · rw [normSquared_smul, Complex.normSq_neg, Complex.normSq_one, one_mul]
    exact hu.1
  · rw [quadricPolynomial_smul, hu.2, mul_zero]

lemma degenerateLift_project (z : UnitQuadric) :
    project ⟨degenerateLift z,degenerateLift_preserves z⟩ = mainEquiv (project z) := by
  rw [mainEquiv_project]
  apply (project_eq_iff_phase _ _).mpr
  exact ⟨-1, by norm_num, by simp [degenerateLift]⟩

lemma degenerateLift_kernel :
    fderiv ℝ degenerateLift zeroVector kernelVector = kernelVector := by
  have hM : ContDiff ℝ ∞ (fun w ↦ forwardMid (1,w)) :=
    forwardMid_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hD := ((pathLinear 1).hasFDerivAt.comp zeroVector
    ((hM.differentiable (by simp) zeroVector).hasFDerivAt)).neg
  change HasFDerivAt degenerateLift _ zeroVector at hD
  rw [hD.fderiv]
  change -(pathLinear 1 (fderiv ℝ (fun w ↦ forwardMid (1,w)) zeroVector kernelVector)) = kernelVector
  rw [forwardMid_kernel, pathLinear_apply, rotation_finish_neg kernelVector (by rfl), neg_neg]

lemma main_degenerate : HasDegenerateFixedPoint mainEquiv := by
  refine ⟨zeroLift,kernelVector,zeroLift_fixed,kernelVector_ne_zero,kernelVector_horizontal,
    Set.univ,degenerateLift,isOpen_univ,Set.mem_univ _,degenerateLift_smooth.contDiffOn,
    degenerateLift_zeroVector,?_,0,?_⟩
  · intro y _
    exact ⟨degenerateLift_preserves y,degenerateLift_project y⟩
  · change fderiv ℝ degenerateLift zeroVector kernelVector - kernelVector = (0:ℝ) • _
    rw [degenerateLift_kernel, sub_self, zero_smul]

end ArnoldCounterexample.Construction

end

end OAI
