import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import OAI.Geometry.NodalSets.Charts.SphereEnergyCompactness
import OAI.Geometry.NodalSets.Charts.SphereEnergyL2Map

namespace OAI

namespace Yau.Target
open MeasureTheory Filter Metric Set
open scoped Topology
noncomputable section
local instance sphereEnergyL2CompactMeasurable : MeasurableSpace Base := borel Base
local instance sphereEnergyL2CompactBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereEnergyL2_smooth_subsequence (d : SphereEnergyData)
    (u : ℕ → SphereEnergySmooth d) {C : ℝ} (hC : 0 < C) (hb : ∀ j, ‖u j‖ ≤ C) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ CauchySeq (fun j ↦ sphereEnergyL2Linear d (u (nu j))) := by
  obtain ⟨nu,hnu,hc⟩ := sphere_energy_subsequence d.tensor d.smooth d.symm d.pos
    d.density d.continuous d.positive (fun j ↦ SphereEnergySmooth.toSmooth d (u j))
    (fun j ↦ (SphereEnergySmooth.toSmooth d (u j)).property) (sq_pos_of_pos hC)
    (fun j ↦ by rw [← SphereEnergySmooth.norm_sq]; nlinarith [hb j,norm_nonneg (u j)])
  refine ⟨nu,hnu,Metric.cauchySeq_iff.mpr ?_⟩
  intro eps heps
  obtain ⟨N,hN⟩ := hc (eps^2) (sq_pos_of_pos heps)
  refine ⟨N,fun i hi j hj ↦ ?_⟩
  have h := hN i hi j hj
  have heq := sphereEnergyL2Linear_norm_sq d (u (nu i)-u (nu j))
  rw [map_sub] at heq
  rw [dist_eq_norm]
  change sphereWeightedPairing d.density
    (SphereEnergySmooth.toSmooth d (u (nu i)-u (nu j)))
    (SphereEnergySmooth.toSmooth d (u (nu i)-u (nu j))) < eps^2 at h
  nlinarith [norm_nonneg (sphereEnergyL2Linear d (u (nu i))-sphereEnergyL2Linear d (u (nu j)))]

theorem sphereEnergyL2_bounded_subsequence (d : SphereEnergyData)
    (z : ℕ → SphereEnergyHilbert d) {C : ℝ} (hC : 0 < C) (hb : ∀ j, ‖z j‖ ≤ C) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∃ v : SphereWeightedL2 d,
      Tendsto (fun j ↦ sphereEnergyL2Map d (z (nu j))) atTop (𝓝 v) := by
  have he (j : ℕ) : 0 < 1/((j:ℝ)+1) := by positivity
  choose u hu using (fun j ↦ (sphereEnergyToCompletion_dense d).exists_dist_lt (z j) (he j))
  have hu_bound (j : ℕ) : ‖u j‖ ≤ C+1 := by
    have hn : ‖sphereEnergyToCompletion d (u j)‖ ≤ ‖z j‖ + 1/((j:ℝ)+1) :=
      norm_le_norm_add_const_of_dist_le (by rw [dist_comm]; exact (hu j).le)
    rw [(sphereEnergyToCompletion d).norm_map] at hn
    have he1 : 1/((j:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    linarith [hb j,hu j]
  obtain ⟨nu,hnu,hc⟩ := sphereEnergyL2_smooth_subsequence d u (by positivity) hu_bound
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨nu,hnu,v,hv.congr_dist ?_⟩
  have he0 : Tendsto (fun j : ℕ ↦ 1/((nu j:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hnu.tendsto_atTop
  apply squeeze_zero (fun j ↦ dist_nonneg) (fun j ↦ ?_) he0
  rw [← sphereEnergyL2Map_coe,dist_eq_norm,← map_sub]
  have h := sphereEnergyL2Map_apply_norm_le d (sphereEnergyToCompletion d (u (nu j))-z (nu j))
  apply h.trans
  simpa only [← dist_eq_norm,dist_comm] using (hu (nu j)).le

theorem sphereEnergyL2Map_compact (d : SphereEnergyData) : IsCompactOperator (sphereEnergyL2Map d) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (sphereEnergyL2Map d).toLinearMap zero_lt_one).mpr
  apply IsSeqCompact.isCompact
  intro y hy
  have he (j : ℕ) : 0 < 1/((j:ℝ)+1) := by positivity
  have ha (j : ℕ) := Metric.mem_closure_iff.mp (hy j) _ (he j)
  choose w hw hd using ha
  choose z hz hzw using hw
  have hb (j : ℕ) : ‖z j‖ ≤ (1:ℝ) := by simpa only [mem_closedBall,dist_zero_right] using hz j
  obtain ⟨nu,hnu,v,hv⟩ := sphereEnergyL2_bounded_subsequence d z zero_lt_one hb
  have hconv : Tendsto (y ∘ nu) atTop (𝓝 v) := by
    apply hv.congr_dist
    apply squeeze_zero (fun j ↦ dist_nonneg) (fun j ↦ ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hnu.tendsto_atTop)
    have hh := (hd (nu j)).le
    rw [← hzw (nu j)] at hh
    simpa only [Function.comp_apply,dist_comm] using! hh
  refine ⟨v,?_,nu,hnu,hconv⟩
  exact isClosed_closure.mem_of_tendsto hconv (Eventually.of_forall (fun j ↦ hy (nu j)))

end
end Yau.Target

end OAI
