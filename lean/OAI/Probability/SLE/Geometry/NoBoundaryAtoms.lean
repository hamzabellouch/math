import OAI.Probability.SLE.Geometry.HolomorphicBoundaryAtoms

namespace OAI

/-! A centered conformal disk chart has no atom at any prescribed
boundary point on finite physical exits. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

theorem planarDiskExitAtom_null
    (W : WienerLaw) (hW : IsWiener W) {D : Set ℂ} (hD : IsOpen D)
    (w : ℂ) (hw : w∈D) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F D)
    (hFD : MapsTo F D (ball 0 1)) (hF0 : F w=0)
    (a : ℂ) (ha : ‖a‖=1) (T : ℝ≥0) :
    (W.prod W) (planarDiskExitAtom D F w a T)=0 := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let p := (W.prod W) (planarDiskExitAtom D F w a T)
  have hpn : p ≠ ∞ := measure_ne_top _ _
  have hbound (n : ℕ) : p.toReal ≤ 1/((n:ℝ)+1) := by
    let r : ℝ := n/((n:ℝ)+1)
    have hr : 0 ≤ r := by dsimp only [r]; positivity
    have hr1 : r<1 := (div_lt_one (by positivity)).mpr (by norm_num)
    have hh := planarDiskExitAtom_peak_bound W hW hD w hw hF hFD hF0 a ha T r hr hr1
    have hcoef : (1+r)/(1-r)=2*(n:ℝ)+1 := by
      dsimp only [r]
      field_simp
      ring
    rw [hcoef] at hh
    have hhR : (2*(n:ℝ)+1)*p.toReal ≤ 1 := by
      simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*(n:ℝ)+1),
        ENNReal.toReal_one] using ENNReal.toReal_mono (by simp) hh
    apply (le_div_iff₀ (by positivity : (0:ℝ)<n+1)).mpr
    nlinarith [ENNReal.toReal_nonneg (a := p)]
  have hp0 : p.toReal=0 := le_antisymm
    (ge_of_tendsto (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      (Eventually.of_forall hbound)) ENNReal.toReal_nonneg
  exact ((ENNReal.toReal_eq_zero_iff p).mp hp0).resolve_right hpn

end SLEExactGauge

end

end OAI
