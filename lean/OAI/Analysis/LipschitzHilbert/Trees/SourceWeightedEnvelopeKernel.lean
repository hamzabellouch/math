import OAI.Analysis.LipschitzHilbert.Trees.SourceTopWeightTransfer
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoxReproduction
import OAI.Analysis.LipschitzHilbert.Fourier.TileEnvelopeKernel

namespace OAI

/-! Weighted tile envelopes are controlled by the actual strong maximal
function. Only one quadratic top weight in each coordinate is needed. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

def topReciprocalWeight (a b L W : ℝ) (z : ℝ×ℝ) : ℝ :=
  lineEnvelope a L 1 z.1*lineEnvelope b W 1 z.2

theorem topReciprocalWeight_nonneg (a b L W : ℝ) (z : ℝ×ℝ) :
    0≤topReciprocalWeight a b L W z :=
  mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem topReciprocalWeight_le_one (a b L W : ℝ) (z : ℝ×ℝ) :
    topReciprocalWeight a b L W z≤1 := by
  have hx : lineEnvelope a L 1 z.1≤1 := by
    simpa only [lineEnvelope,pow_zero,inv_one] using lineEnvelope_antitone a L z.1 (by decide : 0≤1)
  have hy : lineEnvelope b W 1 z.2≤1 := by
    simpa only [lineEnvelope,pow_zero,inv_one] using lineEnvelope_antitone b W z.2 (by decide : 0≤1)
  exact (mul_le_mul hx hy (lineEnvelope_nonneg _ _ _ _) (by norm_num)).trans_eq (by ring)

theorem topReciprocalWeight_measurable (a b L W : ℝ) :
    Measurable (topReciprocalWeight a b L W) := by
  unfold topReciprocalWeight lineEnvelope
  fun_prop

theorem weighted_tile_envelope_transfer (a b L W sx sy ell : ℝ)
    (hell : 0<ell) (hW : 0<W) (hlen : ell≤L)
    (z v : ℝ×ℝ) (hv : v∈coordinateBox sx sy ell W) :
    topReciprocalWeight a b L W z*tileEnvelope sx sy ell W 2 z≤
      36*topReciprocalWeight a b L W v*tileEnvelope sx sy ell W 1 z := by
  have hx := top_weight_envelope_transfer a sx L ell z.1 v.1 hell hlen hv.1
  have hy := top_weight_envelope_transfer b sy W W z.2 v.2 hW le_rfl hv.2
  have hx0 : 0≤lineEnvelope a L 1 z.1*lineEnvelope sx ell 2 z.1 :=
    mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  have hy0 : 0≤lineEnvelope b W 1 z.2*lineEnvelope sy W 2 z.2 :=
    mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  have hh := mul_le_mul hx hy hy0 (hx0.trans hx)
  dsimp only [topReciprocalWeight,tileEnvelope]
  convert hh using 1 <;> ring

theorem weighted_tile_kernel_bound (a b L W sx sy ell : ℝ)
    (hell : 0<ell) (hW : 0<W) (hlen : ell≤L)
    (H : ℝ×ℝ → ℝ) (hHm : Measurable H) (hH2 : MemLp H 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hH0 : ∀ z, 0≤H z) (hHb : ∀ z, ‖H z‖≤B) :
    ∀ᵐ v ∂volume.prod volume, v∈coordinateBox sx sy ell W →
      (∫ z, topReciprocalWeight a b L W z*tileEnvelope sx sy ell W 2 z*H z ∂volume.prod volume)≤
        (36*9216)*(ell*W)*topReciprocalWeight a b L W v*DyadicLineGrid.threeStrongMaximal H v := by
  let D := topReciprocalWeight a b L W
  have hDb (z : ℝ×ℝ) : ‖D z‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (topReciprocalWeight_nonneg a b L W z)]
    exact topReciprocalWeight_le_one a b L W z
  have hleft : Integrable (fun z => D z*tileEnvelope sx sy ell W 2 z*H z)
      (volume.prod volume) :=
    (((tileEnvelope_integrable sx sy ell W (by decide : 1≤2) hell hW).bdd_mul
      (topReciprocalWeight_measurable a b L W).aestronglyMeasurable
      (Filter.Eventually.of_forall hDb)).mul_bdd hHm.aestronglyMeasurable
      (Filter.Eventually.of_forall hHb))
  have hright : Integrable (fun z => tileEnvelope sx sy ell W 1 z*H z)
      (volume.prod volume) :=
    (tileEnvelope_integrable sx sy ell W (by decide : 1≤1) hell hW).mul_bdd
      hHm.aestronglyMeasurable (Filter.Eventually.of_forall hHb)
  have heq : (∫ z, tileEnvelope sx sy ell W 1 z*H z ∂volume.prod volume)=
      (ell*W)*(∫ z, normalizedLineEnvelope sx ell z.1*normalizedLineEnvelope sy W z.2*H z
        ∂volume.prod volume) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    unfold tileEnvelope normalizedLineEnvelope
    field_simp
  filter_upwards [planar_kernel_le_strongMaximal hHm hH2 B hB hH0 hHb sx sy ell W hell hW] with v hv
  intro hvc
  calc
    _ ≤ ∫ z, (36*D v)*(tileEnvelope sx sy ell W 1 z*H z) ∂volume.prod volume := by
      apply integral_mono hleft (hright.const_mul _)
      intro z
      have h := mul_le_mul_of_nonneg_right
        (weighted_tile_envelope_transfer a b L W sx sy ell hell hW hlen z v hvc) (hH0 z)
      simpa only [mul_assoc] using h
    _ = (36*D v)*((ell*W)*(∫ z,
        normalizedLineEnvelope sx ell z.1*normalizedLineEnvelope sy W z.2*H z
          ∂volume.prod volume)) := by rw [integral_const_mul,heq]
    _ ≤ (36*D v)*((ell*W)*(9216*DyadicLineGrid.threeStrongMaximal H v)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hv hvc) (mul_pos hell hW).le)
        (mul_nonneg (by norm_num) (topReciprocalWeight_nonneg a b L W v))
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
