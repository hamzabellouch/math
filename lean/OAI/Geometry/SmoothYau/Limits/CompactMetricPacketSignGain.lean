import Mathlib
import OAI.Geometry.SmoothYau.Estimates.LocalizedPacketSignProbability
import OAI.Geometry.SmoothYau.SphereMetric.ScaledThreeAxisEnergy

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace YauCounterexamples

theorem compact_metric_packet_sign_gain
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ → ∃ c₀ > 0,
    ∀ T c M rₑ Q : ℝ, 0 < T → 0 < c → 0 < M → 0 < rₑ → 0 < Q →
    ∃ N : ℝ, 2 ≤ N ∧ ∀ t : ℝ, N ≤ t → ∀ (I : Type) [Fintype I] [DecidableEq I]
      (q : I → NormalWaveParameter) (z : I → Fin 3 → ℂ)
      (U : I → NormalWaveSpace → ℂ) (b : NormalWaveSpace → ℝ),
      (Fintype.card I : ℝ) ≤ Q*(t^4)^3 →
      (∀ i, q i ∈ metricFrameSet g K) →
      (∀ i, (∑ j, z i j*z i j = -1) ∧
        ‖phaseRealVector (z i)-gradient (normalWaveProfile g φ (q i)) 0‖ ≤ (Real.sqrt (t^4))⁻¹) →
      (∀ y ∈ K, ∃ i, t^4*‖y-(q i).1‖ ≤ 1) →
      (∀ i, U i (q i).1 = Complex.exp (((t^4 : ℝ) : ℂ)*(φ (q i).1 : ℂ))) →
      (∀ i y, ‖U i y‖ ≤ T*Real.exp (t^4*φ y)*Real.exp (-c*t^4*‖y-(q i).1‖^2)) →
      (∀ i (r : ℝ), 0 ≤ r → r < rₑ → (Real.sqrt (t^4))⁻¹ ≤ r →
        ∀ x y : NormalWaveSpace, ‖x-(q i).1‖ ≤ r → ‖y-(q i).1‖ ≤ r → t^4*‖y-x‖ ≤ 1 →
        ‖U i y-(Real.exp (t^4*fderiv ℝ φ x (y-x)) : ℂ)*
          Complex.exp (((t^4*normalImagCovector (q i) (z i) (y-x) : ℝ) : ℂ)*Complex.I)*U i x‖ ≤
        (M*r)*‖(Real.exp (t^4*fderiv ℝ φ x (y-x)) : ℂ)*
          Complex.exp (((t^4*normalImagCovector (q i) (z i) (y-x) : ℝ) : ℂ)*Complex.I)*U i x‖) →
      (∀ y ∈ K, |b y| ≤ c₀*Real.exp (t^4*φ y)) →
      ∀ x ∈ K, ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
      (∀ j, packetAxisShift x (t^4) ε ℓ j ∈ K) →
      ∃ j, ENNReal.ofReal p ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (b x+complexGaussianRealValue (fun i => U i x) γ)*
          (b (packetAxisShift x (t^4) ε ℓ j)+
            complexGaussianRealValue (fun i => U i (packetAxisShift x (t^4) ε ℓ j)) γ) < 0} := by
  obtain ⟨ε,hε,hε1,κ,hκ,hκ1,hgap⟩ := compact_packet_angular_gap g hK
  obtain ⟨Hs,hHs,hslope⟩ := compact_profile_slope_bound g hK
  obtain ⟨p,hp,hprob⟩ := localized_packet_sign_probability hκ hκ1
  refine ⟨ε,hε,hε1,p,hp,?_⟩
  intro φ hφ
  obtain ⟨rₐ,hrₐ,hang⟩ := hgap φ hφ
  obtain ⟨H,hH,hφbound⟩ := compact_profile_unit_lipschitz φ hφ hK
  let c₀ := Real.exp (-2*H)/2
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨c₀,hc₀,?_⟩
  intro T c M rₑ Q hT hc hM hrₑ hQ
  let δ := min (1/16) (κ/96)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1/16 := min_le_left _ _
  have hδκ : δ ≤ κ/96 := min_le_right _ _
  let r := min rₑ (min rₐ (δ/(2*(M+1))))
  have hr : 0 < r := lt_min hrₑ (lt_min hrₐ (by positivity))
  have htend : Tendsto (fun t : ℝ => 2/t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hevent := htend.eventually_lt_const hr
  have htail := quartic_tail_budget_eventually (B := Q*T*Real.exp H)
    (a := c/4) (δ := δ/2) (c := Real.exp (-Hs)*c₀) (by positivity) (half_pos hδ) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((eventually_ge_atTop (2 : ℝ)).and (hevent.and htail))
  refine ⟨max 2 N,le_max_left _ _,?_⟩
  intro t ht I _ _ q z U b hcount hq hz hcov hcenter hloc hend hb x hx ℓ hℓ hℓ' hy
  obtain ⟨ht2,htr,htail'⟩ := hN t ((le_max_right _ _).trans ht)
  have ht1 : 1 ≤ t := by linarith
  obtain ⟨ht0,hn1,hinv,hsqrt⟩ := quartic_inverse_bounds ht1
  have hrad : 0 ≤ 2/t := by positivity
  have htre : 2/t < rₑ := htr.trans_le (min_le_left _ _)
  have htra : 2/t ≤ rₐ := htr.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMr : M*(2/t) ≤ δ/2 := by
    have hh : 2/t ≤ δ/(2*(M+1)) := htr.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (show 0 < 2*(M+1) by positivity)).mp hh
    nlinarith
  have hinvra : t⁻¹ ≤ rₐ := le_trans (by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr ht0]) htra
  have hbudget : (Fintype.card I : ℝ)*T*Real.exp H*Real.exp (-c*t^2/4) ≤
      (δ/2)*Real.exp (-Hs)*(Real.exp (-2*H)/2) := by
    have hh : (Fintype.card I : ℝ) ≤ Q*t^12 := by simpa only [←pow_mul] using hcount
    calc
      _ ≤ (Q*t^12)*T*Real.exp H*Real.exp (-c*t^2/4) := by gcongr
      _ = (Q*T*Real.exp H)*(t^12*Real.exp (-(c/4)*t^2)) := by
        rw [show -(c/4)*t^2 = -c*t^2/4 by ring]
        ring
      _ ≤ _ := by simpa only [c₀,mul_assoc] using htail'
  apply hprob I φ K (fun i => (q i).1) (fun i => normalImagCovector (q i) (z i)) U b
    H Hs ε ℓ t T c M δ x (by linarith) hHs.le hε hε1
    ((profileFrequencyScale_ge_one g φ x).trans hℓ) ht2 hT hc hM.le hδ hδ1 hδκ hMr
    (fun i => (hq i).1) hx hy hcov hφbound
    (fun j => (normalized_real_growth_bounds
      (lt_of_lt_of_le zero_lt_one (profileFrequencyScale_ge_one g φ x)) hℓ hε.le hε1 hHs.le
      (fderiv ℝ φ x) (hslope φ hφ x hx) j).1)
    hcenter hloc (fun i => hend i (2/t) hrad htre hsqrt) ?_ hbudget hb
  intro i hi
  exact hang (q i) (hq i) (z i) x (hz i).1 (hi.trans hinvra)
    ((hz i).2.trans (hsqrt.trans htra)) ℓ hℓ hℓ'
end YauCounterexamples
end

end OAI
