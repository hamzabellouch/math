import OAI.Analysis.LienardCycles.RegionBarrier

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ReferenceCharacteristic
open QuadraticCoordinates PartialCalculus

lemma monotone_zero_nonneg {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 0))
    (hm : MonotoneOn f (Ioc 0 r)) : 0 ≤ f r := by
  apply le_of_tendsto hf
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hr).filter_mono inf_le_left] with s hs hsr
  exact hm ⟨hs,hsr.le⟩ ⟨hr,le_rfl⟩ hsr.le

lemma strictMono_zero_pos {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 0))
    (hm : StrictMonoOn f (Ioc 0 r)) : 0 < f r := by
  have hhalf : 0 < r/2 := half_pos hr
  have hle : r/2 ≤ r := by linarith
  have hn := monotone_zero_nonneg hhalf hf (hm.monotoneOn.mono (Ioc_subset_Ioc_right hle))
  exact hn.trans_lt (hm ⟨hhalf,hle⟩ ⟨hr,le_rfl⟩ (by linarith))

lemma J_strictAnti {z k : ℝ} (hk : 0 < k) :
    StrictAntiOn (fun r => J ((z,k),r)) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun s hs => (J_deriv hs).continuousAt.continuousWithinAt)
  intro s hs
  have hs' : 0 < s := interior_subset hs
  rw [(J_deriv (z := z) (k := k) hs').deriv]
  have h := mul_pos (mul_pos hk hs') (A_gap_pos (q := ((z,k),s)) hs')
  linarith

lemma AH_tendsto (z k : ℝ) :
    Tendsto (fun r => r^2*A ((z,k),r)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hlow : Tendsto (fun r : ℝ => -r^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using! (((tendsto_id.mono_left inf_le_left).pow 2).neg :
      Tendsto (fun r : ℝ => -r^2) (𝓝[>] (0:ℝ)) (𝓝 (-0^2)))
  have hupp : Tendsto (fun r : ℝ => r^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using! ((tendsto_id.mono_left inf_le_left).pow 2 :
      Tendsto (fun r : ℝ => r^2) (𝓝[>] (0:ℝ)) (𝓝 (0^2)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have h := (abs_lt.mp (A_abs_lt (q := ((z,k),r)) hr)).1
    nlinarith [mul_nonneg (sq_nonneg r) (show 0 ≤ A ((z,k),r)+1 by linarith)]
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have h := (abs_lt.mp (A_abs_lt (q := ((z,k),r)) hr)).2
    nlinarith [mul_nonneg (sq_nonneg r) (show 0 ≤ 1-A ((z,k),r) by linarith)]

lemma AH_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => s^2*A ((z,k),s)) (r^2*J ((z,k),r)*(1-A ((z,k),r)^2)) r := by
  have hd := ((hasDerivAt_id r).pow 2).mul (A_deriv (z := z) (k := k) hr)
  convert! hd using 1
  dsimp only [Pi.pow_apply,id_eq]
  field_simp
  ring

lemma A_pos_before {z k r : ℝ} (hk : 0 < k) (_hr : 0 < r)
    (hA : 0 ≤ A ((z,k),r)) {s : ℝ} (hs : 0 < s) (hsr : s < r) :
    0 < A ((z,k),s) := by
  have hj := J_strictAnti (z := z) hk
  have hpos (t : ℝ) (ht : 0 < t) (hjt : 0 ≤ J ((z,k),t)) : 0 < A ((z,k),t) := by
    have hm : StrictMonoOn (fun u => u^2*A ((z,k),u)) (Ioc 0 t) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioc 0 t)
        (fun u hu => (AH_deriv hu.1).continuousAt.continuousWithinAt)
      intro u hu
      rw [interior_Ioc] at hu
      rw [(AH_deriv (z := z) (k := k) hu.1).deriv]
      exact mul_pos (mul_pos (sq_pos_of_pos hu.1)
        (hjt.trans_lt (hj hu.1 ht hu.2))) (A_gap_pos hu.1)
    have hmul : 0 < t^2*A ((z,k),t) := strictMono_zero_pos (f := fun u => u^2*A ((z,k),u)) (r := t) ht (AH_tendsto z k) hm
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos ht)).mp hmul
  by_contra! hnon
  have hjs : J ((z,k),s) < 0 := by
    by_contra! h
    exact (hpos s hs h).not_ge hnon
  have hm : StrictAntiOn (fun u => u^2*A ((z,k),u)) (Icc s r) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc s r)
      (fun u hu => (AH_deriv (hs.trans_le hu.1)).continuousAt.continuousWithinAt)
    intro u hu
    have hu' := interior_subset (s := Icc s r) hu
    have hu0 := hs.trans_le hu'.1
    rw [(AH_deriv (z := z) (k := k) hu0).deriv]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (sq_pos_of_pos hu0)
        ((hj.antitoneOn hs hu0 hu'.1).trans_lt hjs)) (A_gap_pos hu0)
  have hh := hm ⟨le_rfl,hsr.le⟩ ⟨hsr.le,le_rfl⟩ hsr
  have hleft := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) hnon
  have hright := mul_nonneg (sq_nonneg r) hA
  linarith

end QuinticLienard.ReferenceCharacteristic

end OAI
