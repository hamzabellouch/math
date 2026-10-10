import Mathlib
import OAI.Geometry.PrescribedRicci.GlobalKahlerIntegral
import OAI.Geometry.PrescribedRicci.MatrixWirtinger
import OAI.Geometry.PrescribedRicci.MatrixWirtingerExtra
import OAI.Geometry.PrescribedRicci.VolumePathRicci

namespace OAI

/-! Curvature Compact Bounds. -/

section

 

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma curvatureMatrix_smooth (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (b a : Fin d) :
    ContDiffAt ℝ ∞ (fun y => g.curvatureMatrix q y b a) z := by
  have hs := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (g.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (g.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hs
  exact (contDiffAt_barDerivative (contDiffAt_holDerivative hs a) b).neg.add
    (matrix_mul_contDiffAt (matrix_mul_contDiffAt (contDiffAt_barDerivative hs b) hi)
      (contDiffAt_holDerivative hs a))

lemma curvatureRicci_smooth (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    ContDiffAt ℝ ∞ (g.curvatureRicci q) z := by
  apply (PotentialKaehler.potentialMatrix_smooth (g.ricciPotential_contDiffAt q hz)).congr_of_eventuallyEq
  filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
  exact g.curvatureRicci_eq q hy

def backgroundSize (g : KaehlerMetric A) (F : SmoothRealFunction A)
    (q : Fin A.count) (z : Coordinates d) : ℝ :=
  1+‖g.matrix q z‖+‖(g.matrix q z)⁻¹‖+‖g.curvatureRicci q z‖+
    ‖F.hessian q z‖+‖g.curvatureMatrix q z‖

def BackgroundComponentBound (g : KaehlerMetric A) (F : SmoothRealFunction A)
    (q : Fin A.count) (z : Coordinates d) (M : ℝ) : Prop :=
  (∀ i j, ‖g.matrix q z i j‖ ≤ M) ∧
  (∀ i j, ‖(g.matrix q z)⁻¹ i j‖ ≤ M) ∧
  (∀ i j, ‖g.curvatureRicci q z i j‖ ≤ M) ∧
  (∀ i j, ‖F.hessian q z i j‖ ≤ M) ∧
  (∀ a b i j, ‖g.curvatureMatrix q z b a i j‖ ≤ M)

lemma backgroundSize_continuousOn (g : KaehlerMetric A) (F : SmoothRealFunction A)
    (q : Fin A.count) : ContinuousOn (g.backgroundSize F q) (A.chart q).target := by
  intro z hz
  have hs := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun y => (g.matrix q y)⁻¹) z :=
    ((MongeAmpere.contDiffAt_inv _ (g.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hs
  have hR : ContDiffAt ℝ ∞ (g.curvatureMatrix q) z := by
    apply contDiffAt_pi.mpr
    intro b
    apply contDiffAt_pi.mpr
    intro a
    exact g.curvatureMatrix_smooth q hz b a
  exact (((((continuousAt_const.add hs.continuousAt.norm).add hi.continuousAt.norm).add
    (g.curvatureRicci_smooth q hz).continuousAt.norm).add
      ((F.hessian_smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)).continuousAt.norm).add
        hR.continuousAt.norm).continuousWithinAt

lemma backgroundComponents_of_size (g : KaehlerMetric A) (F : SmoothRealFunction A)
    (q : Fin A.count) (z : Coordinates d) {M : ℝ} (hb : g.backgroundSize F q z ≤ M) :
    g.BackgroundComponentBound F q z M := by
  have h1 : ‖g.matrix q z‖ ≤ M := by unfold backgroundSize at hb; linarith [norm_nonneg ((g.matrix q z)⁻¹),norm_nonneg (g.curvatureRicci q z),norm_nonneg (F.hessian q z),norm_nonneg (g.curvatureMatrix q z)]
  have h2 : ‖(g.matrix q z)⁻¹‖ ≤ M := by unfold backgroundSize at hb; linarith [norm_nonneg (g.matrix q z),norm_nonneg (g.curvatureRicci q z),norm_nonneg (F.hessian q z),norm_nonneg (g.curvatureMatrix q z)]
  have h3 : ‖g.curvatureRicci q z‖ ≤ M := by unfold backgroundSize at hb; linarith [norm_nonneg (g.matrix q z),norm_nonneg ((g.matrix q z)⁻¹),norm_nonneg (F.hessian q z),norm_nonneg (g.curvatureMatrix q z)]
  have h4 : ‖F.hessian q z‖ ≤ M := by unfold backgroundSize at hb; linarith [norm_nonneg (g.matrix q z),norm_nonneg ((g.matrix q z)⁻¹),norm_nonneg (g.curvatureRicci q z),norm_nonneg (g.curvatureMatrix q z)]
  have h5 : ‖g.curvatureMatrix q z‖ ≤ M := by unfold backgroundSize at hb; linarith [norm_nonneg (g.matrix q z),norm_nonneg ((g.matrix q z)⁻¹),norm_nonneg (g.curvatureRicci q z),norm_nonneg (F.hessian q z)]
  refine ⟨fun i j => ?_,fun i j => ?_,fun i j => ?_,fun i j => ?_,fun a b i j => ?_⟩
  · exact (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans h1)
  · exact (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans h2)
  · exact (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans h3)
  · exact (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans h4)
  · exact (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans
      ((norm_le_pi_norm _ a).trans ((norm_le_pi_norm _ b).trans h5)))

variable [T2Space X] [CompactSpace X]

lemma compact_background_bounds (g : KaehlerMetric A) (F : SmoothRealFunction A) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q : Fin A.count, ∀ x ∈ tsupport (chartPartition (A:=A) q).value,
      g.BackgroundComponentBound F q (A.chart q x) M := by
  have hb (q : Fin A.count) : ∃ M : ℝ, 1 ≤ M ∧ ∀ x ∈ tsupport (chartPartition (A:=A) q).value,
      g.backgroundSize F q (A.chart q x) ≤ M := by
    let K := (A.chart q) '' tsupport (chartPartition (A:=A) q).value
    have hK : IsCompact K := (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((A.chart q).continuousOn.mono (chartPartition_support q))
    have hKt : K ⊆ (A.chart q).target := by
      rintro z ⟨x,hx,rfl⟩
      exact (A.chart q).mapsTo (chartPartition_support q hx)
    obtain ⟨b,hb⟩ := hK.bddAbove_image ((g.backgroundSize_continuousOn F q).mono hKt)
    refine ⟨max 1 b,le_max_left _ _,fun x hx => ?_⟩
    exact (hb (mem_image_of_mem _ (mem_image_of_mem _ hx))).trans (le_max_right _ _)
  choose M hM hMb using hb
  refine ⟨1+∑ q, M q,?_,fun q x hx => g.backgroundComponents_of_size F q (A.chart q x) ?_⟩
  · have hn : 0 ≤ ∑ q, M q := Finset.sum_nonneg (fun q _ => (by norm_num : (0:ℝ)≤1).trans (hM q))
    linarith
  · have hle : M q ≤ ∑ j, M j := Finset.single_le_sum
      (fun j _ => (by norm_num : (0:ℝ)≤1).trans (hM j)) (Finset.mem_univ q)
    exact (hMb q x hx).trans (by linarith)

lemma exists_partition_chart (x : X) : ∃ q : Fin A.count,
    x ∈ tsupport (chartPartition (A:=A) q).value := by
  by_contra! hh
  have hz (q : Fin A.count) : (chartPartition (A:=A) q).value x = 0 := by
    by_contra hn
    exact hh q (subset_tsupport _ hn)
  have he := chartPartition_sum (A:=A) x
  simp only [hz,Finset.sum_const_zero] at he
  norm_num at he

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
