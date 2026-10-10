import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoulombNear

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace CoulombAnalysis

lemma tf_rotation_preserving (R : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) :
    MeasurePreserving e (ballMeasure R) (ballMeasure R) := by
  have he : e ⁻¹' ball (0 : TFSpace) R = ball 0 R := by
    ext x; simp
  have hp : MeasurePreserving e (volume : Measure TFSpace) volume := e.measurePreserving
  have hr := hp.restrict_preimage (s := ball (0 : TFSpace) R) measurableSet_ball
  rw [he] at hr
  exact hr

def tfRotate (R : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace)
    (f : TFLp (ballMeasure R)) : TFLp (ballMeasure R) :=
  Lp.compMeasurePreserving e (tf_rotation_preserving R e) f

lemma tfRotate_coe (R : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (f : TFLp (ballMeasure R)) :
    tfRotate R e f =ᵐ[ballMeasure R] fun x => f (e x) := Lp.coeFn_compMeasurePreserving _ _

lemma tfRotate_norm (R : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (f : TFLp (ballMeasure R)) :
    ‖tfRotate R e f‖ = ‖f‖ := Lp.norm_compMeasurePreserving _ _

lemma tfRotate_nonneg {R : ℝ} (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) : NonnegDensity (tfRotate R e f) := by
  filter_upwards [tfRotate_coe R e f, (tf_rotation_preserving R e).quasiMeasurePreserving.ae hf]
    with x hx hn
  rw [hx]; exact hn

lemma tfRotate_linear (R Z η : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (f : TFLp (ballMeasure R)) :
    tfBallLinear R Z η (tfRotate R e f) = tfBallLinear R Z η f := by
  have hi (g : TFSpace → ℝ) := (tf_rotation_preserving R e).integral_comp
    e.toHomeomorph.measurableEmbedding g
  simp only [tfBallLinear, sub_apply, smul_apply,
    smul_eq_mul, tfPairing_apply]
  congr 1
  · congr 1
    calc
      ∫ x, (1 : ℝ) * tfRotate R e f x ∂ballMeasure R =
        ∫ x, (1 : ℝ) * f (e x) ∂ballMeasure R := integral_congr_ae ((tfRotate_coe R e f).fun_comp _)
      _ = ∫ x, (1 : ℝ) * f x ∂ballMeasure R := hi (fun x => 1 * f x)
  · congr 1
    calc
      ∫ x, ‖x‖⁻¹ * tfRotate R e f x ∂ballMeasure R =
        ∫ x, ‖e x‖⁻¹ * f (e x) ∂ballMeasure R := by
          apply integral_congr_ae
          filter_upwards [tfRotate_coe R e f] with x hx
          rw [hx, e.norm_map]
      _ = ∫ x, ‖x‖⁻¹ * f x ∂ballMeasure R := hi (fun x => ‖x‖⁻¹ * f x)

lemma tfRotate_coulomb (R : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (f g : TFLp (ballMeasure R)) :
    tfCoulombL R (tfRotate R e f) (tfRotate R e g) = tfCoulombL R f g := by
  rw [tfCoulombL_apply, tfCoulombL_apply]
  calc
    _ = ∫ p : TFSpace × TFSpace, f (e p.1) * g (e p.2) / ‖e p.1 - e p.2‖
        ∂(ballMeasure R).prod (ballMeasure R) := by
      apply integral_congr_ae
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ballMeasure R)
        (ν := ballMeasure R)).ae (tfRotate_coe R e f),
        (Measure.quasiMeasurePreserving_snd (μ := ballMeasure R)
        (ν := ballMeasure R)).ae (tfRotate_coe R e g)] with p hf hg
      rw [hf, hg, ← e.map_sub, e.norm_map]
    _ = _ := (tf_rotation_preserving R e |>.prod (tf_rotation_preserving R e)).integral_comp
      (e.toHomeomorph.measurableEmbedding.prodMap e.toHomeomorph.measurableEmbedding)
      (fun p : TFSpace × TFSpace => f p.1 * g p.2 / ‖p.1 - p.2‖)

lemma tfRotate_functional (R T Z η : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (f : TFLp (ballMeasure R)) :
    tfBallFunctional R T Z η (tfRotate R e f) = tfBallFunctional R T Z η f := by
  simp only [tfBallFunctional, tfRotate_norm, tfRotate_linear, tfRotate_coulomb]

lemma tf_minimizer_rotation {R T Z η : ℝ} (hT : 0 < T) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hmin : ∀ g, NonnegDensity g →
      tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g)
    (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) : tfRotate R e f = f := by
  exact tfBallFunctional_min_unique R Z η hT (tfRotate_nonneg e hf) hf
    (fun g hg => by rw [tfRotate_functional]; exact hmin g hg) hmin

lemma tfBallPotential_rotation {R T Z η : ℝ} (hT : 0 < T) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hmin : ∀ g, NonnegDensity g →
      tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g)
    (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (x : TFSpace) :
    tfBallPotential R f (e x) = tfBallPotential R f x := by
  have hrot := tfRotate_coe R e f
  rw [tf_minimizer_rotation hT hf hmin e] at hrot
  unfold tfBallPotential
  calc
    _ = ∫ y, f (e y) / ‖e x - e y‖ ∂ballMeasure R :=
      ((tf_rotation_preserving R e).integral_comp e.toHomeomorph.measurableEmbedding
        (fun y => f y / ‖e x - y‖)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hrot] with y hy
      rw [← hy, ← e.map_sub, e.norm_map]

lemma tfField_extension_rotation {Z : ℝ} {f : TFLp (ballMeasure Z)}
    (hf : NonnegDensity f) (hmin : ∀ g, NonnegDensity g →
      tfBallFunctional Z CoulombAtom.tfKinetic Z 1 f ≤ tfBallFunctional Z CoulombAtom.tfKinetic Z 1 g)
    (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (x : TFSpace) :
    tfField Z (tfExtension Z f) (e x) = tfField Z (tfExtension Z f) x := by
  simp only [tfField, tfPotential_extension, e.norm_map,
    tfBallPotential_rotation tfKinetic_pos hf hmin]

lemma tfBallPotential_radial {R T Z η : ℝ} (hT : 0 < T) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hmin : ∀ g, NonnegDensity g →
      tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g)
    (x y : TFSpace) (hxy : ‖x‖ = ‖y‖) : tfBallPotential R f x = tfBallPotential R f y := by
  obtain ⟨e, he⟩ := exists_orthogonal_map_norm_eq x y hxy
  simpa only [he] using (tfBallPotential_rotation hT hf hmin e x).symm

lemma tfField_extension_radial {Z : ℝ} {f : TFLp (ballMeasure Z)}
    (hf : NonnegDensity f) (hmin : ∀ g, NonnegDensity g →
      tfBallFunctional Z CoulombAtom.tfKinetic Z 1 f ≤ tfBallFunctional Z CoulombAtom.tfKinetic Z 1 g)
    (x y : TFSpace) (hxy : ‖x‖ = ‖y‖) :
    tfField Z (tfExtension Z f) x = tfField Z (tfExtension Z f) y := by
  obtain ⟨e, he⟩ := exists_orthogonal_map_norm_eq x y hxy
  simpa only [he] using (tfField_extension_rotation hf hmin e x).symm

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian

end

end OAI
