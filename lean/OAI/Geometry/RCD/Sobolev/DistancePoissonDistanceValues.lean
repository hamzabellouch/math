import OAI.Geometry.RCD.Sobolev.DistancePoissonValueL1
import OAI.Geometry.RCD.Sobolev.DistancePoissonRepresentative
import OAI.Geometry.RCD.Coordinates.NormalizedSupportedCompression

namespace OAI

/-! # Replacing compact Poisson values by the actual squared distance -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {Q : QuadraticCheegerEnergy μ}
  {n : ℕ} {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}
  {F : DistancePoissonFamily μ Q n κ B J C p r hr} (D : DistancePoissonMeanData F)

theorem DistancePoissonMeanData.scaled_distance_error_ae (k : ℕ) :
    SobolevSpace.toLp μ Q (((r k)^2)⁻¹ • (F.datum k-F.replacement k))
      =ᵐ[μ.restrict (ball (p k) (r k/16))]
      fun x => (dist (p k) x^2/2-D.representative k x)/(r k)^2 := by
  have hq := positiveSquaredDistance_representative μ Q
    (mul_nonneg (by norm_num : (0:ℝ)≤4) (hr k).le) (F.cutoff k)
  filter_upwards [ae_restrict_of_ae hq,D.representative_local_eq k,
    ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (Lp.coeFn_smul ((r k)^2)⁻¹
      (SobolevSpace.toLp μ Q (F.datum k-F.replacement k))),
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ Q (F.datum k))
      (SobolevSpace.toLp μ Q (F.replacement k)))] with x hqx hDx hx hs hd
  have hx4 : x∈ball (p k) (4*r k) :=
    ball_subset_ball (show r k/16≤4*r k by linarith [hr k]) hx
  have hqx' : SobolevSpace.toLp μ Q (F.datum k) x=dist (p k) x^2/2 :=
    hqx.trans (positiveSquaredDistanceValue_on_ball μ Q (F.cutoff k) hx4)
  rw [map_smul,hs,Pi.smul_apply,smul_eq_mul,map_sub,hd,Pi.sub_apply,hqx',← hDx]
  ring

theorem DistancePoissonMeanData.normalized_distance_mean_error {P Cν : ℝ}
    (hP : 0≤P) (hCν : 0≤Cν) (hV : ∀ k, 0<μ.real (ball (p k) (r k)))
    (hpoin : ∀ k, ∀ v : SobolevSpace.dirichlet μ Q (ball (p k) (r k)),
      ‖SobolevSpace.toLp μ Q v.val‖^2≤P*(r k)^2*energyForm μ Q v.val v.val)
    (hmass : Tendsto (fun k => (F.source k).real (ball (p k) (r k))/μ.real (ball (p k) (r k)))
      atTop (𝓝 0))
    (ν : ℕ → Measure X) [∀ k, IsFiniteMeasure (ν k)] (Bν : ℕ → ℝ≥0∞)
    (hBν : ∀ k, Bν k≠∞) (hν : ∀ k, ν k≤Bν k • μ)
    (hs : ∀ k, ∀ᵐ x ∂ν k, x∈ball (p k) (r k/16))
    (hcompression : ∀ k, (Bν k).toReal*μ.real (ball (p k) (r k))≤Cν) :
    Tendsto (fun k => ((∫ x, dist (p k) x^2/2 ∂ν k)-
      (∫ x, D.representative k x ∂ν k))/(r k)^2) atTop (𝓝 0) := by
  let w k := ((r k)^2)⁻¹ • (F.datum k-F.replacement k)
  have hi k : IntegrableOn (SobolevSpace.toLp μ Q (w k)) (ball (p k) (r k)) μ := by
    let : IsFiniteMeasure (μ.restrict (ball (p k) (r k))) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact ((Lp.memLp _).restrict (ball (p k) (r k))).integrable (by norm_num)
  have hlarge k : ν k≤ENNReal.ofReal (Cν/μ.real (ball (p k) (r k))) • μ.restrict (ball (p k) (r k)) :=
    normalized_supported_compression μ (ν k) (hBν k) (hν k)
      ((hs k).mono fun _ hx => ball_subset_ball (show r k/16≤r k by linarith [hr k]) hx)
      (hV k) (hcompression k)
  have hlim := normalized_local_L1_domination μ (fun k => ball (p k) (r k)) ν
    (fun k => SobolevSpace.toLp μ Q (w k)) hCν hV hlarge hi
    (F.normalized_value_L1_tendsto_zero hP hV hpoin hmass)
  apply hlim.congr'
  apply Eventually.of_forall
  intro k
  have hac : ν k ≪ μ.restrict (ball (p k) (r k/16)) :=
    Measure.absolutelyContinuous_of_le_smul ((compression_iff_localized μ (ν k) (hs k) (Bν k)).mp (hν k))
  have he := hac.ae_eq (D.scaled_distance_error_ae k)
  dsimp only [w]
  rw [integral_congr_ae he]
  have hq : Integrable (fun x => dist (p k) x^2/2) (ν k) := by
    apply Integrable.of_bound (by fun_prop) ((r k)^2/2)
    filter_upwards [hs k] with x hx
    have hdist : dist (p k) x<r k/16 := by simpa only [mem_ball,dist_comm] using hx
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    nlinarith [dist_nonneg (x := p k) (y := x),hr k]
  obtain ⟨L,A,hL,hc,_he,_hA⟩ := D.representative_spec k
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hL.continuous
  have hu : Integrable (D.representative k) (ν k) :=
    Integrable.of_bound hL.continuous.aestronglyMeasurable M (Eventually.of_forall hM)
  rw [integral_div,integral_sub hq hu]

end RegularPointCoordinates

end

end OAI
