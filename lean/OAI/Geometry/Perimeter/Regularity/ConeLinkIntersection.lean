import OAI.Geometry.Perimeter.Regularity.CoupledConeLink
import OAI.Geometry.Perimeter.Regularity.ConeLinkSupport

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
namespace RPISingularHarnack
namespace SphericalFrankel

def fullLink {n : ℕ} (E : Set (Euc n)) : Set (Euc n) :=
  perimeterSupport E ∩ Metric.sphere 0 1

lemma fullLink_compact {n : ℕ} (E : Set (Euc n)) : IsCompact (fullLink E) :=
  (isCompact_sphere (0 : Euc n) 1).inter_left (isClosed_perimeterSupport E)

lemma fullLink_nonempty {n : ℕ} (hn : 1 < n) {E : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) (hc : IsCone E)
    (hv : (0 : Euc n) ∈ perimeterSupport E) : (fullLink E).Nonempty := by
  obtain ⟨x,hx,hx0⟩ := minimizing_support_nonzero_point hn hE hv
  refine ⟨radialUnit x, (isCone_perimeterSupport hE.1 hc _
    (inv_pos.mpr (norm_pos_iff.mpr hx0)) x).mpr hx, ?_⟩
  simpa [Metric.mem_sphere] using radialUnit_norm hx0

lemma product_ne_zero_of_ne_zero {n : ℕ} {μ ν : Measure (Frame n)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≠ 0) (hν : ν ≠ 0) : μ.prod ν ≠ 0 := by
  intro hz
  have hp : μ Set.univ * ν Set.univ = 0 := by
    rw [← Measure.prod_prod, Set.univ_prod_univ, hz]
    simp
  rcases mul_eq_zero.mp hp with h | h
  · exact hμ (Measure.measure_univ_eq_zero.mp h)
  · exact hν (Measure.measure_univ_eq_zero.mp h)

theorem minimizing_cone_links_intersect {n : ℕ} (hn : 2 < n) {E F : Set (Euc n)}
    (hE : IsLocallyPerimeterMinimizing E) (hF : IsLocallyPerimeterMinimizing F)
    (hcE : IsCone E) (hcF : IsCone F)
    (hvE : (0 : Euc n) ∈ perimeterSupport E)
    (hvF : (0 : Euc n) ∈ perimeterSupport F) :
    (fullLink E ∩ fullLink F).Nonempty := by
  have hn1 : 1 < n := by omega
  let μ := annularLink E
  let ν := annularLink F
  let : IsFiniteMeasure μ := annularLink_finite hE
  let : IsFiniteMeasure ν := annularLink_finite hF
  have hμ0 : μ ≠ 0 := annularLink_ne_zero hn1 hE hcE hvE
  have hν0 : ν ≠ 0 := annularLink_ne_zero hn1 hF hcF hvF
  have hμ := annularLink_frames hn1 hE hcE
  have hν := annularLink_frames hn1 hF hcF
  have hS := minimizing_cones_coupledStationarity hn1 hE hF hcE hcF
  have hC : Continuous (fun p : Euc n × Euc n ↦ inner ℝ p.1 p.2) :=
    continuous_fst.inner continuous_snd
  obtain ⟨p, hp, hmax⟩ := ((fullLink_compact E).prod (fullLink_compact F)).exists_isMaxOn
    ((fullLink_nonempty hn1 hE hcE hvE).prod (fullLink_nonempty hn1 hF hcF hvF))
    hC.continuousOn
  have hpn : ‖p.1‖ = 1 := by simpa [Metric.mem_sphere] using hp.1.2
  have hqn : ‖p.2‖ = 1 := by simpa [Metric.mem_sphere] using hp.2.2
  have hle : inner ℝ p.1 p.2 ≤ 1 := by
    exact le_trans (le_abs_self _) (by simpa [hpn,hqn] using abs_real_inner_le_norm p.1 p.2)
  by_cases heq : p.1 = p.2
  · exact ⟨p.1,hp.1,heq ▸ hp.2⟩
  · have hlt : inner ℝ p.1 p.2 < 1 := lt_of_le_of_ne hle (by
      intro he
      exact heq ((inner_eq_one_iff_of_norm_eq_one hpn hqn).mp he))
    have hbound : ∀ᵐ q ∂μ.prod ν, angle q.1 q.2 ≤ max 0 (inner ℝ p.1 p.2) := by
      apply (Measure.ae_prod_iff_ae_ae
        (isClosed_le continuous_angle continuous_const).measurableSet).mpr
      filter_upwards [annularLink_radial_support hn1 hE hcE] with e he
      filter_upwards [annularLink_radial_support hn1 hF hcF] with f hf
      apply le_trans _ (le_max_right _ _)
      change inner ℝ e.1 f.1 ≤ inner ℝ p.1 p.2
      exact hmax (a := (e.1,f.1)) ⟨⟨he.1, by simpa [Metric.mem_sphere] using he.2⟩,
        ⟨hf.1, by simpa [Metric.mem_sphere] using hf.2⟩⟩
    exact (no_positive_angle_gap hn (product_ne_zero_of_ne_zero hμ0 hν0)
      (product_frames hμ hν) hS (le_max_left _ _) (max_lt (by norm_num) hlt) hbound).elim

end SphericalFrankel
end RPISingularHarnack

end

end OAI
