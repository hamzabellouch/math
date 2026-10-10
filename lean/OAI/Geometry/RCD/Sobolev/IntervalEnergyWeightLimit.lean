import OAI.Geometry.RCD.Sobolev.WeightedEnergyWeightLimit
import OAI.Geometry.RCD.Coordinates.IntervalBilinearEnergy

namespace OAI

/-! # Changing spatial weights in an interval energy integral -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem integral_intervalExtension_subinterval {a b s t : ℝ}
    (hsub : Icc s t ⊆ Ioo a b) (f : Ioo a b → ℝ) :
    (∫ u in Icc s t, intervalExtension f u) =
      ∫ u : Ioo a b, (Icc s t).indicator (fun _ => (1:ℝ)) u*f u
        ∂volume.comap Subtype.val := by
  rw [← integral_intervalExtension]
  have he : (fun u => (Icc s t).indicator (fun _ => (1:ℝ)) u*intervalExtension f u) =
      (Icc s t).indicator (intervalExtension f) := by
    funext u
    by_cases hu : u ∈ Icc s t <;> simp [hu]
  rw [he,setIntegral_indicator measurableSet_Icc,inter_eq_right.mpr hsub]

theorem weighted_energy_interval_weight_tendsto
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
    (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    (w : ℕ → X → ℝ) (v : X → ℝ) (hw : ∀ k, AEStronglyMeasurable (w k) μ)
    {M : ℝ≥0} (hM : ∀ k, ∀ᵐ x ∂μ, ‖w k x‖ ≤ M)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun k => w k x) atTop (𝓝 (v x)))
    {a b s t : ℝ} (hsub : Icc s t ⊆ Ioo a b)
    (u : Ioo a b → SobolevSpace μ Q)
    (hu : AEStronglyMeasurable u (volume.comap Subtype.val))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ τ, ‖u τ‖ ≤ C) :
    Tendsto (fun k => ∫ τ in Icc s t, intervalExtension
      (fun q => weightedGamma μ Q (w k) (u q) (u q)) τ) atTop
      (𝓝 (∫ τ in Icc s t, intervalExtension
        (fun q => weightedGamma μ Q v (u q) (u q)) τ)) := by
  have hfin : volume (Ioo a b) ≠ ∞ :=
    ((measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne
  have hi : Integrable (fun _ : Ioo a b => (1:ℝ)) (volume.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp (integrableOn_const hfin)
  have hm : MeasurableSet {q : Ioo a b | (q:ℝ) ∈ Icc s t} :=
    measurableSet_Icc.preimage measurable_subtype_coe
  have hθ : Integrable (fun q : Ioo a b => (Icc s t).indicator (fun _ => (1:ℝ)) q)
      (volume.comap Subtype.val) := by
    convert hi.indicator hm using 1
    funext q
    simp only [indicator_apply,mem_ofPred_eq]
  simpa only [integral_intervalExtension_subinterval hsub] using
    weighted_energy_time_weight_tendsto μ Q (volume.comap Subtype.val) w v hw hM hc u hu
      hC (Eventually.of_forall hb) _ hθ

end RegularPointCoordinates

end

end OAI
