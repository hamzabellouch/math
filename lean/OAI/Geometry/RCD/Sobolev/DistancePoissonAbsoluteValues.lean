import OAI.Geometry.RCD.Sobolev.DistancePoissonDistanceValues

namespace OAI

/-! # Absolute squared-distance value errors under normalized compression -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {Q : QuadraticCheegerEnergy μ}
  {n : ℕ} {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}
  {F : DistancePoissonFamily μ Q n κ B J C p r hr} (D : DistancePoissonMeanData F)

theorem DistancePoissonMeanData.normalized_distance_L1_error {P Cν : ℝ}
    (hP : 0≤P) (hCν : 0≤Cν) (hV : ∀ k, 0<μ.real (ball (p k) (r k)))
    (hpoin : ∀ k, ∀ v : SobolevSpace.dirichlet μ Q (ball (p k) (r k)),
      ‖SobolevSpace.toLp μ Q v.val‖^2≤P*(r k)^2*energyForm μ Q v.val v.val)
    (hmass : Tendsto (fun k => (F.source k).real (ball (p k) (r k))/μ.real (ball (p k) (r k)))
      atTop (𝓝 0))
    (ν : ℕ → Measure X) [∀ k, IsFiniteMeasure (ν k)] (Bν : ℕ → ℝ≥0∞)
    (hBν : ∀ k, Bν k≠∞) (hν : ∀ k, ν k≤Bν k • μ)
    (hs : ∀ k, ∀ᵐ x ∂ν k, x∈ball (p k) (r k/16))
    (hcompression : ∀ k, (Bν k).toReal*μ.real (ball (p k) (r k))≤Cν) :
    Tendsto (fun k => (∫ x, |dist (p k) x^2/2-D.representative k x| ∂ν k)/(r k)^2)
      atTop (𝓝 0) := by
  let w k := ((r k)^2)⁻¹ • (F.datum k-F.replacement k)
  have hi k : IntegrableOn (SobolevSpace.toLp μ Q (w k)) (ball (p k) (r k)) μ := by
    let : IsFiniteMeasure (μ.restrict (ball (p k) (r k))) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact ((Lp.memLp _).restrict (ball (p k) (r k))).integrable (by norm_num)
  have hlarge k : ν k≤ENNReal.ofReal (Cν/μ.real (ball (p k) (r k))) • μ.restrict (ball (p k) (r k)) :=
    normalized_supported_compression μ (ν k) (hBν k) (hν k)
      ((hs k).mono fun _ hx => ball_subset_ball (show r k/16≤r k by linarith [hr k]) hx)
      (hV k) (hcompression k)
  have hinput := F.normalized_value_L1_tendsto_zero hP hV hpoin hmass
  have hlim := normalized_local_L1_domination μ (fun k => ball (p k) (r k)) ν
    (fun k x => |SobolevSpace.toLp μ Q (w k) x|) hCν hV hlarge (fun k => (hi k).abs)
    (by simpa only [abs_abs] using hinput)
  apply hlim.congr'
  apply Eventually.of_forall
  intro k
  have hac : ν k ≪ μ.restrict (ball (p k) (r k/16)) :=
    Measure.absolutelyContinuous_of_le_smul ((compression_iff_localized μ (ν k) (hs k) (Bν k)).mp (hν k))
  have he' : SobolevSpace.toLp μ Q (w k) =ᵐ[ν k]
      fun x => (dist (p k) x^2/2-D.representative k x)/(r k)^2 :=
    hac.ae_eq (D.scaled_distance_error_ae k)
  have he : (fun x => |SobolevSpace.toLp μ Q (w k) x|) =ᵐ[ν k]
      fun x => |(dist (p k) x^2/2-D.representative k x)/(r k)^2| := by
    filter_upwards [he'] with x hx
    exact congrArg abs hx
  dsimp only [w]
  rw [integral_congr_ae he]
  simp_rw [abs_div,abs_of_pos (sq_pos_of_pos (hr k))]
  rw [integral_div]

end RegularPointCoordinates

end

end OAI
