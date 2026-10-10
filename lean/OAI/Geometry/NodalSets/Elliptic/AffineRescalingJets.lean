import OAI.Geometry.NodalSets.Elliptic.CommonLocalExtension
import OAI.Geometry.NodalSets.Elliptic.NormalizedRescaling

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma affine_rescaling_derivative_power (f : Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    (x v : Coord) {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z ↦ f (x+r • z)) v‖ ≤
      r^k*‖iteratedFDeriv ℝ k f (x+r • v)‖ := by
  let L : Coord →L[ℝ] Coord := r • ContinuousLinearMap.id ℝ Coord
  have hL : ‖L‖ ≤ r := by
    apply ContinuousLinearMap.opNorm_le_bound _ hr
    intro z
    change ‖r • z‖ ≤ r*‖z‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  change ‖iteratedFDeriv ℝ k ((fun z ↦ f (x+z)) ∘ L) v‖ ≤ _
  have htrans : ContDiff ℝ ∞ (fun z : Coord ↦ f (x+z)) := hf.comp (contDiff_const.add contDiff_id)
  rw [L.iteratedFDeriv_comp_right htrans v
    (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)),iteratedFDeriv_comp_add_left]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg L) hL k) (norm_nonneg _)).trans_eq (mul_comm _ _)

lemma smoothOn_global_germ {U : Set Coord} (hU : IsOpen U)
    (f : Coord → ℂ) (hf : ContDiffOn ℝ ∞ f U) {x : Coord} (hx : x ∈ U) :
    ∃ F : Coord → ℂ, ContDiff ℝ ∞ F ∧ F =ᶠ[𝓝 x] f := by
  obtain ⟨r,F,hr,hF,_,_,_,_,he⟩ := common_local_smooth_extension hU f hf hx
  exact ⟨F,hF,he x (by simpa using hr)⟩

lemma affine_rescaling_derivative_power_on {U : Set Coord} (hU : IsOpen U)
    (f : Coord → ℂ) (hf : ContDiffOn ℝ ∞ f U) (x v : Coord)
    {r : ℝ} (hr : 0 ≤ r) (hz : x+r • v ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z ↦ f (x+r • z)) v‖ ≤
      r^k*‖iteratedFDeriv ℝ k f (x+r • v)‖ := by
  obtain ⟨F,hF,he⟩ := smoothOn_global_germ hU f hf hz
  have hc : Continuous (fun z : Coord ↦ x+r • z) := continuous_const.add (continuous_id.const_smul r)
  have hh := he.comp_tendsto hc.continuousAt
  change (fun z ↦ F (x+r • z)) =ᶠ[𝓝 v] (fun z ↦ f (x+r • z)) at hh
  rw [← (hh.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds,← (he.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
  exact affine_rescaling_derivative_power F hF x v hr k

lemma radius_high_power {N s : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s) {k : ℕ} (hk : 2 ≤ k) :
    N*((N*s)⁻¹)^k ≤ N⁻¹ := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  obtain ⟨hr0,hr1,hNr⟩ := rescaling_radius_bound hN hs
  have hrN : (N*s)⁻¹ ≤ N⁻¹ := (inv_le_inv₀ (mul_pos hN0 (lt_of_lt_of_le zero_lt_one hs)) hN0).mpr (by nlinarith)
  have hpow := pow_le_pow_of_le_one hr0 hr1 hk
  calc
    _ ≤ N*((N*s)⁻¹)^2 := mul_le_mul_of_nonneg_left hpow hN0.le
    _ ≤ N*(N⁻¹)^2 := by gcongr
    _ = N⁻¹ := by field_simp

end
end Yau.Geometry

end OAI
