import OAI.Probability.SLE.Stochastic.PlanarHarmonicLocalization
import OAI.Probability.SLE.Geometry.ExtendedStopLocalization

namespace OAI

/-! Concrete compact localization stops for planar Brownian motion. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

lemma planarWiener_zero (b : Driver×Driver) : planarWiener 0 b=0 := by
  simp [planarWiener]

lemma planarWiener_adapted : Adapted planarWienerFiltration planarWiener :=
  (Filtration.stronglyAdapted_natural (fun t => (measurable_planarWiener t).stronglyMeasurable)).adapted

def planarCutoffHit (χ : ℝ×ℝ → ℝ) : Driver×Driver → WithTop ℝ≥0 :=
  hittingAfter (fun t b => χ (planarWiener t b)) {0} 0

def planarCutoffStop (χ : ℝ×ℝ → ℝ) (T : ℝ≥0) : Driver×Driver → ℝ≥0 :=
  cutoffStop (planarCutoffHit χ) T

lemma planarCutoffHit_stopping (χ : ℝ×ℝ → ℝ) (hχ : Continuous χ) :
    IsStoppingTime planarWienerFiltration (planarCutoffHit χ) :=
  continuous_zero_hit_stopping planarWienerFiltration (fun t b => χ (planarWiener t b))
    (fun t => hχ.measurable.comp (planarWiener_adapted t))
    (fun b => hχ.comp (planarWiener_continuous b)) 0

lemma planarCutoffStop_stopping (χ : ℝ×ℝ → ℝ) (hχ : Continuous χ) (T : ℝ≥0) :
    IsStoppingTime planarWienerFiltration (fun b => (planarCutoffStop χ T b : WithTop ℝ≥0)) :=
  cutoffStop_stopping planarWienerFiltration _ (planarCutoffHit_stopping χ hχ) T

lemma planarCutoffStop_le (χ : ℝ×ℝ → ℝ) (T : ℝ≥0) (b : Driver×Driver) :
    planarCutoffStop χ T b ≤ T := cutoffStop_le_horizon _ _ _

lemma planarCutoffStop_before (χ : ℝ×ℝ → ℝ) (T : ℝ≥0) (b : Driver×Driver)
    (t : ℝ≥0) (ht : t < planarCutoffStop χ T b) : χ (planarWiener t b) ≠ 0 := by
  have hhit : (t : WithTop ℝ≥0)<planarCutoffHit χ b :=
    (WithTop.coe_lt_coe.mpr ht).trans_le (cutoffStop_le_stop _ _ _)
  exact fun hz => notMem_of_lt_hittingAfter hhit (zero_le : (0:ℝ≥0) ≤ t) hz

lemma planarCutoffStop_in_support (χ : ℝ×ℝ → ℝ) (h0 : χ 0≠0)
    (T : ℝ≥0) (b : Driver×Driver) (t : ℝ≥0) (ht : t ≤ planarCutoffStop χ T b) :
    planarWiener t b ∈ tsupport χ := by
  by_cases hlt : t < planarCutoffStop χ T b
  · exact subset_tsupport χ (planarCutoffStop_before χ T b t hlt)
  have he : t=planarCutoffStop χ T b := le_antisymm ht (le_of_not_gt hlt)
  by_cases ht0 : t=0
  · rw [ht0,planarWiener_zero]
    exact subset_tsupport χ h0
  have htpos : 0<t := pos_iff_ne_zero.mpr ht0
  have hcl : t∈closure (Iio t) := by
    rw [closure_Iio' (show (Iio t).Nonempty from ⟨0,htpos⟩)]
    change t ≤ t
    exact le_rfl
  have hm : MapsTo (fun s => planarWiener s b) (Iio t) (tsupport χ) := by
    intro s hs
    exact subset_tsupport χ (planarCutoffStop_before χ T b s (he ▸ hs))
  have hx := (planarWiener_continuous b).continuousWithinAt.mem_closure hcl hm
  simpa only [(isClosed_tsupport χ).closure_eq] using hx

lemma planarCutoffStop_ge_of_nonzero (χ : ℝ×ℝ → ℝ) (hχ : Continuous χ)
    (T t : ℝ≥0) (ht : t ≤ T) (b : Driver×Driver)
    (hn : ∀ s ≤ t, χ (planarWiener s b)≠0) : t ≤ planarCutoffStop χ T b := by
  apply WithTop.coe_le_coe.mp
  rw [planarCutoffStop,cutoffStop_coe,le_min_iff]
  refine ⟨?_,WithTop.coe_le_coe.mpr ht⟩
  apply le_of_lt
  apply lt_of_not_ge
  intro hh
  have hc : ∀ b : Driver×Driver, Continuous (fun s => χ (planarWiener s b)) :=
    fun b => hχ.comp (planarWiener_continuous b)
  obtain ⟨s,hs,hz⟩ := (hittingAfter_zero_le_iff (fun s b => χ (planarWiener s b)) hc 0 t b).mp hh
  exact hn s hs.2 hz

end SLEExactGauge

end

end OAI
