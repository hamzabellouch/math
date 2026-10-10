import OAI.Analysis.PlanarEndpoint.Extension
import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphDual
import OAI.Analysis.PlanarEndpoint.GraphTree
import OAI.Analysis.PlanarEndpoint.WeightedGraph

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace PlanarEndpoint

lemma weighted_cauchy_schwarz {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {W a b : X → ℝ} (hW : Measurable W) (hpos : ∀ x, 0 < W x)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x)
    (hia : Integrable (fun x => W x * a x^2) μ)
    (hib : Integrable (fun x => (W x)⁻¹ * b x^2) μ) :
    (∫ x, a x*b x ∂μ) ≤ Real.sqrt (∫ x, W x*a x^2 ∂μ) *
      Real.sqrt (∫ x, (W x)⁻¹*b x^2 ∂μ) := by
  let A := fun x => Real.sqrt (W x) * a x
  let B := fun x => (Real.sqrt (W x))⁻¹ * b x
  have hA0 x : 0 ≤ A x := mul_nonneg (Real.sqrt_nonneg _) (ha0 x)
  have hB0 x : 0 ≤ B x := mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (hb0 x)
  have hA x : ‖A x‖^2 = W x * a x^2 := by
    simp only [A, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hpos x).le]
  have hB x : ‖B x‖^2 = (W x)⁻¹ * b x^2 := by
    simp only [B, Real.norm_eq_abs, sq_abs, mul_pow, inv_pow, Real.sq_sqrt (hpos x).le]
  have hma : MemLp A 2 μ := (memLp_two_iff_integrable_sq_norm
    (show AEStronglyMeasurable A μ from hW.sqrt.aestronglyMeasurable.mul ha)).2
      (by simpa only [hA] using hia)
  have hmb : MemLp B 2 μ := (memLp_two_iff_integrable_sq_norm
    (show AEStronglyMeasurable B μ from hW.sqrt.inv.aestronglyMeasurable.mul hb)).2
      (by simpa only [hB] using hib)
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hma) (by simpa using hmb)
  simp only [Real.rpow_two, hA, hB] at hh
  norm_num only [show (1/(2:ℝ))=(1/2:ℝ) from rfl] at hh
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hA0 x), abs_of_nonneg (hB0 x)]
  dsimp [A,B]
  have hs : Real.sqrt (W x) ≠ 0 := (Real.sqrt_pos.2 (hpos x)).ne'
  field_simp

lemma hThirdNorm_energy_sqrt (f : L2) :
    Real.sqrt (∫ ξ, sobolevWeight ξ * ‖fourier f ξ‖^2) = (2*Real.pi)*hThirdNorm f := by
  rw [hThirdNorm, Real.sqrt_mul (by positivity), Real.sqrt_inv, Real.sqrt_sq (by positivity)]
  dsimp [sobolevWeight]
  field_simp

lemma BoundedFourierSupport.dyadic {f : L2} (hf : BoundedFourierSupport f) :
    ∃ n : ℕ, ∀ᵐ ξ ∂volume, ξ ∉ Metric.ball (0:Plane) ((2:ℝ)^n) → fourier f ξ=0 := by
  obtain ⟨R,hs⟩ := hf
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt R (by norm_num : (1:ℝ)<2)
  refine ⟨n,hs.mono ?_⟩
  intro ξ hξ hout
  apply hξ
  have ho : (2:ℝ)^n ≤ ‖ξ‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hout
  exact lt_of_lt_of_le hn ho

lemma graph_sobolev_pairing_bound {p : ℝ} (hp : 2 < p)
    (hshort : ShortTimeWeakEstimate (1/4) 4 p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : L2), BoundedFourierSupport f → InHThird f →
      ∀ (x₀ : Plane) (T : Plane → ℝ) (w : Plane → ℂ), Measurable T → Measurable w →
      (∀ x, ‖w x‖ ≤ 1) → (∀ x ∈ Metric.ball x₀ 1, T x ∈ Ico 0 1) →
      ‖∫ ξ, fourier f ξ * graphFourier (volume.restrict (Metric.ball x₀ 1)) T w ξ‖ ≤
        C*hThirdNorm f := by
  obtain ⟨C,hC,hbound⟩ := graph_weighted_sum_bound hp hshort
  refine ⟨(2*Real.pi)*Real.sqrt C,by positivity,?_⟩
  intro f hf hH x₀ T w hT hw hb ht
  obtain ⟨n,hn⟩ := hf.dyadic
  let S := Metric.ball (0:Plane) ((2:ℝ)^n)
  let G := graphFourier (volume.restrict (Metric.ball x₀ 1)) T w
  have hg : Continuous G := continuous_graphFourier _ hT hw hb
  have he : (∫ ξ, fourier f ξ*G ξ) = ∫ ξ in S, fourier f ξ*G ξ := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [hn] with ξ hξ
    by_cases hs : ξ ∈ S
    · rw [indicator_of_mem hs]
    · rw [indicator_of_notMem hs,hξ hs,zero_mul]
  rw [he]
  have hnorm := norm_integral_le_integral_norm (fun ξ => fourier f ξ*G ξ)
    (μ := volume.restrict S)
  simp only [norm_mul] at hnorm
  have hia : Integrable (fun ξ => sobolevWeight ξ*‖fourier f ξ‖^2) (volume.restrict S) :=
    hH.mono_measure Measure.restrict_le_self
  have hib : Integrable (fun ξ => (sobolevWeight ξ)⁻¹*‖G ξ‖^2) (volume.restrict S) :=
    graph_weighted_integrableOn x₀ hT hw hb _
  have hcs := weighted_cauchy_schwarz (volume.restrict S) continuous_sobolevWeight.measurable
    sobolevWeight_pos ((fourier_memLp f).aestronglyMeasurable.restrict.norm)
    (hg.aestronglyMeasurable.norm) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hia hib
  apply hnorm.trans (hcs.trans ?_)
  have hleft : (∫ ξ in S, sobolevWeight ξ*‖fourier f ξ‖^2) ≤
      ∫ ξ, sobolevWeight ξ*‖fourier f ξ‖^2 :=
    integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun ξ => mul_nonneg (sobolevWeight_pos ξ).le (sq_nonneg _))) hH
  have hright := hbound x₀ T w hT hw hb ht n
  calc
    _ ≤ Real.sqrt (∫ ξ, sobolevWeight ξ*‖fourier f ξ‖^2) * Real.sqrt C :=
      mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [hThirdNorm_energy_sqrt]; ring

end PlanarEndpoint
end

end OAI
