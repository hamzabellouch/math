import OAI.Probability.GammaPassage.EndpointCoarseGeometry

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Filter
open scoped Topology

/-- The coarse mesh dominates the transverse scale at every fixed level.
The integer unit-mesh cutoff requires no separate limiting argument. -/
lemma endpoint_mesh_ratio_tendsto {ι : Type*} {l : Filter ι} (k m : ι → ℕ)
    (hratio : Tendsto (fun i => (2 : ℝ)^(m i)/(2 : ℝ)^(k i)) l atTop) (J : ℕ) :
    Tendsto (fun i => (gridMesh (m i) J : ℝ)/(2 : ℝ)^(k i)) l atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [hratio.eventually (eventually_ge_atTop (B*(2 : ℝ)^(4*J+1)))] with i hi
  have hs : (0 : ℝ) < 2^(k i) := by positivity
  have hc : (0 : ℝ) < 2^(4*J+1) := by positivity
  have hh := (le_div_iff₀ hs).mp hi
  have hm := gridMesh_scale_bound (m i) J
  apply (le_div_iff₀ hs).mpr
  nlinarith

lemma endpoint_levels_eventually {ι : Type*} {l : Filter ι} (k m : ι → ℕ)
    (hk : Tendsto k l atTop)
    (hratio : Tendsto (fun i => (2 : ℝ)^(m i)/(2 : ℝ)^(k i)) l atTop)
    (hm : ∀ᶠ i in l, m i ≤ 3*k i) (J : ℕ) :
    ∀ᶠ i in l, J ≤ gridLastLevel (m i) ∧ gridLastLevel (m i) ≤ k i := by
  filter_upwards [hratio.eventually (eventually_ge_atTop ((2 : ℝ)^(4*J+1))),
    hk.eventually (eventually_ge_atTop 2),hm] with i hi hki hmi
  have hs : (1 : ℝ) ≤ 2^(k i) := one_le_pow₀ (by norm_num)
  have hpow : (2 : ℝ)^(4*J+1) ≤ (2 : ℝ)^(m i) := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 2^(k i))).mp hi
    have hc : (0 : ℝ) ≤ 2^(4*J+1) := by positivity
    nlinarith
  have hexp : 4*J+1 ≤ m i := by
    by_contra hh
    have hh' := pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (show m i < 4*J+1 by omega)
    exact (not_lt_of_ge hpow) hh'
  unfold gridLastLevel
  omega

lemma endpoint_error_eventually {ι : Type*} {l : Filter ι} (k : ι → ℕ)
    (hk : Tendsto k l atTop) (shape rate K a ε : ℝ) (hε : 0 < ε) (J : ℕ)
    (hJ : 32*(Grid.attachmentAllowance shape rate K)*endpointErrorTail J ≤ ε/4) :
    ∀ᶠ i in l, 2*endpointExtensionError shape rate K (k i) J+2*|a| ≤ ε*(2 : ℝ)^(k i)/2 := by
  have hs := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hk
  filter_upwards [hs.eventually (eventually_ge_atTop (8*|a| /ε))] with i hi
  have hh := (div_le_iff₀ hε).mp hi
  have hj := mul_le_mul_of_nonneg_right hJ (show 0 ≤ (2 : ℝ)^(k i) by positivity)
  simp only [Function.comp_apply] at hh
  unfold endpointExtensionError
  nlinarith

end GammaFPP.CrossingBridge

end OAI
