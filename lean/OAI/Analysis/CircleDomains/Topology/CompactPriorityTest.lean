import OAI.Analysis.CircleDomains.Topology.CompactSourceCutoff
import OAI.Analysis.CircleDomains.Transfer.ModelHorizontalApproximation

namespace OAI

/-! The actual priority coordinate gives a compact admissible source test.
Its classical differential on the cutoff plateau is the original one. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem fderiv_cutoff_one_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {η f : E → ℝ}
    (hη : EqOn η (fun _ => 1) U) {x : E} (hx : x ∈ U) :
    fderiv ℝ (fun z => η z*f z) x = fderiv ℝ f x := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hU.mem_nhds hx] with z hz
  rw [hη hz, one_mul]

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_priority_test (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (b : ℕ → ℂ) (hb : ∀ n, (b n : Sphere) ∉ G)
    (c : ℕ → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → ℂ → ℝ) (hχ : ∀ n, ContDiff ℝ ∞ (χ n))
    (hχs : ∀ n, support (χ n) ⊆ ball (b n) (r n))
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hsη : HasCompactSupport η)
    {R : ℝ} (hsR : tsupport η ⊆ ball 0 R)
    (hp : Continuous (fun z : ℂ =>
      priorityInfiniteValue (fun n => χ n z) c (M.horizontalSection (z : Sphere))))
    (he : MemLp (fun z : ℂ => fderiv ℝ
      (fun q : ℂ => priorityInfiniteValue (fun n => χ n q) c (M.horizontalSection (q : Sphere))) z -
      fderiv ℝ (fun q : ℂ => M.horizontalSection (q : Sphere)) z)
      2 (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R))) :
    let p := fun z : ℂ => η z *
      priorityInfiniteValue (fun n => χ n z) c (M.horizontalSection (z : Sphere))
    Continuous p ∧ HasCompactSupport p ∧
      ContDiffOn ℝ ∞ p {z : ℂ | (z : Sphere) ∈ G} ∧
      Nonempty (DeGiorgi.MemW1pWitness 2 (p ∘ complexPlaneCoordinates) (physicalPlaneDomain G)) := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  let X := fun z : ℂ => M.horizontalSection (z : Sphere)
  let P := fun z : ℂ => priorityInfiniteValue (fun n => χ n z) c (X z)
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hX : ContDiffOn ℝ ∞ X Dᶜᶜ := by
    simpa only [compl_compl] using M.horizontalSection_plane_smooth hG
  have hP : ContDiffOn ℝ ∞ P D := by
    simpa only [compl_compl] using priorityInfiniteValue_smooth_off_dust
      hD.isClosed_compl b hb r hr χ hχ hχs c X hX
  have hPE : MemLp (fderiv ℝ P) 2 (volume.restrict (D ∩ ball 0 R)) := by
    have hm := he.norm.add (M.horizontalSection_plane_memLp hG hinf R).norm
    have hsm : AEStronglyMeasurable (fderiv ℝ P) (volume.restrict (D ∩ ball 0 R)) :=
      ((hP.mono inter_subset_left).continuousOn_fderiv_of_isOpen (hD.inter isOpen_ball)
        (by simp)).aestronglyMeasurable (hD.inter isOpen_ball).measurableSet
    apply hm.of_le hsm
    filter_upwards [] with z
    change ‖fderiv ℝ P z‖ ≤ ‖‖fderiv ℝ P z-fderiv ℝ X z‖+‖fderiv ℝ X z‖‖
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc
      _ = ‖(fderiv ℝ P z-fderiv ℝ X z)+fderiv ℝ X z‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hpc : Continuous (fun z => η z*P z) := hη.continuous.mul hp
  have hps : HasCompactSupport (fun z => η z*P z) := hsη.mul_right
  have hpd : ContDiffOn ℝ ∞ (fun z => η z*P z) D := hη.contDiffOn.mul hP
  have hpe := compact_source_cutoff_gradient_memLp_on hD hp hP hη hsη hsR hPE
  exact ⟨hpc, hps, hpd, complex_source_sobolev_witness hD hpc hps hpd hpe⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
