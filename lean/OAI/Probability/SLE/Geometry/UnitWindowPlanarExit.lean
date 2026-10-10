import OAI.Probability.SLE.Geometry.PublishedConformalExitLaw
import OAI.Probability.SLE.Loewner.HalfPlaneFiniteExit
import OAI.Probability.SLE.Loewner.HalfPlaneExitBounds

namespace OAI

/-! The exact deterministic rescaling between the published unit-window
exit events and the original planar Wiener process. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target RibbonCoordinates

def unitWindowStop (τ : ℝ) : ℝ≥0 := (τ/3).toNNReal

lemma unitWindowStop_coe {τ : ℝ} (hτ : 0 ≤ τ) : (unitWindowStop τ:ℝ)=τ/3 :=
  Real.coe_toNNReal (τ/3) (by positivity)

lemma unitWindowStop_bounds {τ : ℝ} (hτ : τ∈Ioc (0:ℝ) 3) :
    0 < unitWindowStop τ ∧ unitWindowStop τ ≤ 1 := by
  constructor
  · exact_mod_cast (show (0:ℝ)<(unitWindowStop τ:ℝ) by
      rw [unitWindowStop_coe hτ.1.le]
      exact div_pos hτ.1 (by norm_num))
  · apply NNReal.coe_le_coe.mp
    rw [unitWindowStop_coe hτ.1.le,NNReal.coe_one]
    linarith [hτ.2]

lemma physicalUnitBrownianPath_at_scale (w : ℂ) (b : Driver×Driver) (s : ℝ≥0) (hs : s ≤ 1) :
    physicalUnitBrownianPath w b (3*(s:ℝ))=w+Complex.equivRealProdCLM.symm (planarWiener s b) := by
  have hclip : unitClipPoint (3*(s:ℝ)/3)=(⟨(s:ℝ),s.coe_nonneg,by exact_mod_cast hs⟩ : unitInterval) := by
    apply Subtype.ext
    change unitClip (3*(s:ℝ)/3)=(s:ℝ)
    rw [mul_div_cancel_left₀ _ (by norm_num : (3:ℝ)≠0)]
    exact unitClip_of_mem ⟨s.coe_nonneg,by exact_mod_cast hs⟩
  rw [physicalUnitBrownianPath,hclip]
  change w+((b.1 s:ℂ)+(b.2 s:ℂ)*Complex.I)=_
  rw [Complex.equivRealProdCLM_symm_apply]
  rfl

lemma physicalUnitBrownianPath_eq_planar (w : ℂ) (b : Driver×Driver) {t : ℝ}
    (ht : t∈Icc (0:ℝ) 3) :
    physicalUnitBrownianPath w b t=w+Complex.equivRealProdCLM.symm (planarWiener (unitWindowStop t) b) := by
  have hs : unitWindowStop t ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    rw [unitWindowStop_coe ht.1,NNReal.coe_one]
    linarith [ht.2]
  have he : 3*(unitWindowStop t:ℝ)=t := by rw [unitWindowStop_coe ht.1]; ring
  simpa only [he] using physicalUnitBrownianPath_at_scale w b (unitWindowStop t) hs

lemma unitWindowFirstExit_planar {D : Set ℂ} {w : ℂ} {b : Driver×Driver} {τ : ℝ}
    (h : UnitWindowFirstExit D (physicalUnitBrownianPath w b) τ) :
    0 < unitWindowStop τ ∧ unitWindowStop τ ≤ 1 ∧
      (∀ s<unitWindowStop τ, w+Complex.equivRealProdCLM.symm (planarWiener s b)∈D) ∧
      w+Complex.equivRealProdCLM.symm (planarWiener (unitWindowStop τ) b)∉D := by
  have hs := unitWindowStop_bounds h.1
  refine ⟨hs.1,hs.2,?_,?_⟩
  · intro s hsτ
    have ht : 3*(s:ℝ)<τ := by
      have hh : (s:ℝ)<unitWindowStop τ := hsτ
      rw [unitWindowStop_coe h.1.1.le] at hh
      linarith
    have hh := h.2.2 ⟨by positivity,ht⟩
    rwa [physicalUnitBrownianPath_at_scale w b s (hsτ.le.trans hs.2)] at hh
  · simpa only [physicalUnitBrownianPath_eq_planar w b ⟨h.1.1.le,h.1.2⟩] using h.2.1

lemma unitWindow_map_limit_iff (w : ℂ) (b : Driver×Driver) (g : ℂ → ℂ)
    {τ : ℝ} (hτ : τ∈Ioc (0:ℝ) 3) (z : ℂ) :
    Tendsto (fun t => g (physicalUnitBrownianPath w b t)) (𝓝[<] τ) (𝓝 z) ↔
      Tendsto (fun s => g (w+Complex.equivRealProdCLM.symm (planarWiener s b)))
        (𝓝[<] (unitWindowStop τ)) (𝓝 z) := by
  have hs := unitWindowStop_bounds hτ
  have hscale : 3*(unitWindowStop τ:ℝ)=τ := by rw [unitWindowStop_coe hτ.1.le]; ring
  constructor
  · intro hh
    have ht : Tendsto (fun s : ℝ≥0 => 3*(s:ℝ)) (𝓝[<] unitWindowStop τ) (𝓝[<] τ) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hc : Continuous (fun s : ℝ≥0 => 3*(s:ℝ)) := continuous_const.mul NNReal.continuous_coe
        have hh := hc.tendsto (unitWindowStop τ)
        rw [hscale] at hh
        exact hh.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hst
        have hh : (s:ℝ)<unitWindowStop τ := hst
        rw [unitWindowStop_coe hτ.1.le] at hh
        change 3*(s:ℝ)<τ
        linarith
    apply (hh.comp ht).congr'
    filter_upwards [self_mem_nhdsWithin] with s hst
    exact congrArg g (physicalUnitBrownianPath_at_scale w b s (le_of_lt hst |>.trans hs.2))
  · intro hh
    have ht : Tendsto unitWindowStop (𝓝[<] τ) (𝓝[<] unitWindowStop τ) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · exact ((continuous_real_toNNReal.comp (continuous_id.div_const 3)).tendsto τ).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Ioi_mem_nhds hτ.1)] with t htt ht0
        apply NNReal.coe_lt_coe.mp
        rw [unitWindowStop_coe (le_of_lt ht0),unitWindowStop_coe hτ.1.le]
        exact div_lt_div_of_pos_right htt (by norm_num)
    apply (hh.comp ht).congr'
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Ioi_mem_nhds hτ.1)] with t htt ht0
    exact congrArg g (physicalUnitBrownianPath_eq_planar w b ⟨ht0.le,htt.le.trans hτ.2⟩).symm

end SLEExactGauge

end

end OAI
