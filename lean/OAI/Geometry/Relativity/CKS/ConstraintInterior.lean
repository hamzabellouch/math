import OAI.Geometry.Relativity.CKS.ConstraintDensityDefinitions

namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped ContDiff Topology
namespace CKSIntrinsicConstraints
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g K : InnerField I (M := M)} {x : M}

def inverseChartFrame (z : M) (u : E) : E →L[ℝ] TangentSpace I ((extChartAt I z).symm u) :=
  mfderivWithin 𝓘(ℝ,E) I (extChartAt I z).symm (range I) u

lemma ConstraintChart.interior_coordinate_smooth (c : ConstraintChart g K x) (z : M) {u : E}
    (hu : u ∈ interior (extChartAt I z).target)
    (hc : (extChartAt I z).symm u ∈ c.domain) :
    ContDiffAt ℝ ∞ (c.coordinate ∘ (extChartAt I z).symm) u := by
  exact (((c.smooth _ hc).contMDiffAt (c.isOpen.mem_nhds hc)).comp u
    ((contMDiffOn_extChartAt_symm z u (interior_subset hu)).contMDiffAt
      (mem_interior_iff_mem_nhds.mp hu))).contDiffAt

lemma ConstraintChart.interior_coordinate_deriv (c : ConstraintChart g K x) (z : M) {u : E}
    (hu : u ∈ interior (extChartAt I z).target)
    (hc : (extChartAt I z).symm u ∈ c.domain) :
    fderiv ℝ (c.coordinate ∘ (extChartAt I z).symm) u =
      (mfderiv I 𝓘(ℝ,E) c.coordinate ((extChartAt I z).symm u)).comp (inverseChartFrame z u) := by
  have h := (((c.smooth _ hc).contMDiffAt (c.isOpen.mem_nhds hc)).mdifferentiableAt
    (by simp)).hasMFDerivAt.comp_hasMFDerivWithinAt u
      (mdifferentiableWithinAt_extChartAt_symm (interior_subset hu)).hasMFDerivWithinAt
  have hd : HasFDerivWithinAt (c.coordinate ∘ (extChartAt I z).symm)
      ((mfderiv I 𝓘(ℝ,E) c.coordinate ((extChartAt I z).symm u)).comp (inverseChartFrame z u))
      (range I) u := h.hasFDerivWithinAt
  have hat : HasFDerivAt (c.coordinate ∘ (extChartAt I z).symm)
      ((mfderiv I 𝓘(ℝ,E) c.coordinate ((extChartAt I z).symm u)).comp (inverseChartFrame z u)) u :=
    hd.hasFDerivAt (mem_of_superset (mem_interior_iff_mem_nhds.mp hu)
      (extChartAt_target_subset_range z))
  exact HasFDerivAt.fderiv (E := E) (F := E) hat

lemma inverseChartFrame_bijective (z : M) {u : E}
    (hu : u ∈ (extChartAt I z).target) : Function.Bijective (inverseChartFrame z u) := by
  let : FiniteDimensional ℝ (TangentSpace I ((extChartAt I z).symm u)) :=
    (inferInstance : FiniteDimensional ℝ E)
  have hi : Function.Injective (inverseChartFrame z u) := by
    intro v w h
    have h' := congrArg (mfderiv I 𝓘(ℝ,E) (extChartAt I z) ((extChartAt I z).symm u)) h
    have he := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hu
    have hv := congrArg (fun L : E →L[ℝ] E => L v) he
    have hw := congrArg (fun L : E →L[ℝ] E => L w) he
    exact hv.symm.trans (h'.trans hw)
  exact ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩

lemma ConstraintChart.interior_coordinate_fullRank (c : ConstraintChart g K x) (z : M) {u : E}
    (hu : u ∈ interior (extChartAt I z).target)
    (hc : (extChartAt I z).symm u ∈ c.domain) :
    Function.Bijective (fderiv ℝ (c.coordinate ∘ (extChartAt I z).symm) u) := by
  rw [c.interior_coordinate_deriv z hu hc]
  exact (c.fullRank _ hc).comp (inverseChartFrame_bijective z (interior_subset hu))

lemma ConstraintChart.interior_pullback_equal (c d : ConstraintChart g K x) (z : M) {u : E}
    (hu : u ∈ interior (extChartAt I z).target)
    (hc : (extChartAt I z).symm u ∈ c.domain)
    (hd : (extChartAt I z).symm u ∈ d.domain) :
    spatialTensorPullback (c.coordinate ∘ (extChartAt I z).symm) c.metric u =
      spatialTensorPullback (d.coordinate ∘ (extChartAt I z).symm) d.metric u ∧
    spatialTensorPullback (c.coordinate ∘ (extChartAt I z).symm) c.tensor u =
      spatialTensorPullback (d.coordinate ∘ (extChartAt I z).symm) d.tensor u := by
  have heqg := (c.represents _ hc).1.symm.trans (d.represents _ hd).1
  have heqK := (c.represents _ hc).2.symm.trans (d.represents _ hd).2
  constructor
  · ext v w
    simp only [spatialTensorPullback,
      c.interior_coordinate_deriv z hu hc,d.interior_coordinate_deriv z hu hd]
    exact congrArg (fun A => A (inverseChartFrame z u v) (inverseChartFrame z u w)) heqg
  · ext v w
    simp only [spatialTensorPullback,
      c.interior_coordinate_deriv z hu hc,d.interior_coordinate_deriv z hu hd]
    exact congrArg (fun A => A (inverseChartFrame z u v) (inverseChartFrame z u w)) heqK
end CKSIntrinsicConstraints

end

end OAI
