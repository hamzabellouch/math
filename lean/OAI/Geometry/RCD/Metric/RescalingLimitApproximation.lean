import OAI.Geometry.RCD.Metric.RescalingLimitProper
import OAI.Geometry.RCD.Coordinates.RegularTangents

namespace OAI

/-! # Pointed approximations from the convergent finite nets -/

open Set Metric Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates.RescalingNetFamily

variable {X : Type*} [MetricSpace X] {p : X} {r : ℕ → ℝ}
  (s : RescalingNetFamily p r) (phi : ℕ → ℕ)
  [PseudoMetricSpace s.Index]

def netIndex (R k : ℕ) : Option (Fin (s.size R k)) → s.Index
  | none => none
  | some j => some ⟨R,k,j⟩

/-- Send a point in the working ball to the corresponding limiting net
point. Outside that ball the map takes the base-point value. -/
def netMap (R k i : ℕ) (x : X) : UniformSpace.Completion s.Index := by
  classical
  exact if h : dist x p ≤ ((R:ℝ)+1)*r (phi i) then
    ((some ⟨R,k,Classical.choose (s.covers (phi i) R k x h)⟩ : s.Index) :
      UniformSpace.Completion s.Index)
  else (none : s.Index)

theorem netMap_data (R k i : ℕ) (x : X)
    (hx : dist x p ≤ ((R:ℝ)+1)*r (phi i)) :
    ∃ j : Fin (s.size R k),
      s.netMap phi R k i x = ((some ⟨R,k,j⟩ : s.Index) : UniformSpace.Completion s.Index) ∧
      dist x (s.point (phi i) R k j) < r (phi i)/((k:ℝ)+1) := by
  classical
  refine ⟨Classical.choose (s.covers (phi i) R k x hx), ?_,
    Classical.choose_spec (s.covers (phi i) R k x hx)⟩
  simp only [netMap, dite_eq_left hx]

variable (hr : ∀ i, 0 < r i)
  (hconv : ∀ a b, Tendsto
    (fun i => dist (s.sample (phi i) a) (s.sample (phi i) b) / r (phi i))
    atTop (𝓝 (dist a b)))

include hconv in
/-- A single tail controls every pair of labels in a finite net and the
base-point label simultaneously. -/
theorem eventually_net_dist (R k : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ i in atTop, ∀ a b : Option (Fin (s.size R k)),
      |dist (s.netIndex R k a) (s.netIndex R k b) -
        dist (s.sample (phi i) (s.netIndex R k a))
          (s.sample (phi i) (s.netIndex R k b)) / r (phi i)| < delta := by
  apply Filter.eventually_all.mpr
  intro a
  apply Filter.eventually_all.mpr
  intro b
  have h := Metric.tendsto_nhds.mp (hconv (s.netIndex R k a) (s.netIndex R k b)) delta hdelta
  simpa only [Real.dist_eq, abs_sub_comm] using h

include hr hconv in
/-- The completed sampled limit is a pointed limit of the original
rescalings, using maps constructed directly from the finite nets. -/
theorem rescalingsConverge :
    RescalingsConverge p ((none : s.Index) : UniformSpace.Completion s.Index) (r ∘ phi) := by
  intro R hR epsilon hepsilon
  obtain ⟨M, hM⟩ := exists_nat_gt R
  have hmesh : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨k, hk⟩ := (hmesh.eventually (gt_mem_nhds (by positivity : 0 < epsilon/16))).exists
  let alpha : ℝ := 1/((k:ℝ)+1)
  have halpha : 0 < alpha := by dsimp only [alpha]; positivity
  have hsmall : alpha < epsilon/16 := hk
  let delta := epsilon/16
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hsum : 3*alpha+delta < epsilon := by dsimp only [delta]; linarith only [hsmall, hepsilon]
  have hsum' : 2*alpha+delta < epsilon := by linarith only [hsum, halpha]
  have hmeshEq (i : ℕ) : r (phi i)/((k:ℝ)+1) = alpha*r (phi i) := by
    dsimp only [alpha]; ring
  filter_upwards [s.eventually_net_dist phi hconv M k hdelta] with i hi
  let f := s.netMap phi M k i
  have hri : 0 < r (phi i) := hr (phi i)
  have hroom (x : X) (hx : dist x p ≤ R*r (phi i)) :
      dist x p ≤ ((M:ℝ)+1)*r (phi i) :=
    hx.trans (mul_le_mul_of_nonneg_right (by linarith only [hM]) hri.le)
  have hpair (j l : Fin (s.size M k)) :
      |dist (some ⟨M,k,j⟩ : s.Index) (some ⟨M,k,l⟩) -
        dist (s.point (phi i) M k j) (s.point (phi i) M k l)/r (phi i)| < delta :=
    hi (some j) (some l)
  have hbase (j : Fin (s.size M k)) :
      |dist (some ⟨M,k,j⟩ : s.Index) none -
        dist (s.point (phi i) M k j) p/r (phi i)| < delta := hi (some j) none
  refine ⟨f, ?_, ?_, ?_⟩
  · obtain ⟨j, hj, hnear⟩ := s.netMap_data phi M k i p
      (by rw [dist_self]; positivity)
    change dist (f p) ((none : s.Index) : UniformSpace.Completion s.Index) ≤ epsilon
    change f p = _ at hj
    rw [hj, UniformSpace.Completion.dist_eq]
    rw [hmeshEq i, dist_comm] at hnear
    have hnear' := (div_lt_iff₀ hri).mpr hnear
    have hh := (abs_lt.mp (hbase j)).2
    linarith only [hh, hnear', hsum', halpha]
  · intro x z hx hz
    obtain ⟨j, hj, hxj⟩ := s.netMap_data phi M k i x (hroom x hx)
    obtain ⟨l, hl, hzl⟩ := s.netMap_data phi M k i z (hroom z hz)
    change f x = _ at hj
    change f z = _ at hl
    rw [hj, hl, UniformSpace.Completion.dist_eq]
    rw [hmeshEq i] at hxj hzl
    have hdist := dist_dist_dist_le x z (s.point (phi i) M k j) (s.point (phi i) M k l)
    rw [Real.dist_eq] at hdist
    have hnear : |dist x z/r (phi i) -
        dist (s.point (phi i) M k j) (s.point (phi i) M k l)/r (phi i)| < 2*alpha := by
      rw [← sub_div, abs_div, abs_of_pos hri]
      apply (div_lt_iff₀ hri).mpr
      exact hdist.trans_lt (by linarith only [hxj, hzl])
    have habs := abs_sub_le
      (dist (some ⟨M,k,j⟩ : s.Index) (some ⟨M,k,l⟩))
      (dist (s.point (phi i) M k j) (s.point (phi i) M k l)/r (phi i))
      (dist x z/r (phi i))
    rw [abs_sub_comm (dist (s.point (phi i) M k j) (s.point (phi i) M k l)/r (phi i))] at habs
    have hp := hpair j l
    dsimp only [Function.comp_apply]
    linarith only [habs, hp, hnear, hsum']
  · intro y hy
    have hyM : dist y ((none : s.Index) : UniformSpace.Completion s.Index) ≤ M := by
      linarith only [hy, hM, hepsilon]
    obtain ⟨j, hj⟩ := s.completion_limit_cover phi hr hconv M k y hyM
    have hmeshTwo : 2/((k:ℝ)+1) = 2*alpha := by dsimp only [alpha]; ring
    rw [hmeshTwo] at hj
    have htri := dist_triangle ((some ⟨M,k,j⟩ : s.Index) : UniformSpace.Completion s.Index)
      y ((none : s.Index) : UniformSpace.Completion s.Index)
    rw [UniformSpace.Completion.dist_eq, dist_comm _ y] at htri
    have hb := (abs_lt.mp (hbase j)).1
    have hsource : dist (s.point (phi i) M k j) p/r (phi i) < R := by
      linarith only [htri, hj, hy, hb, hsum']
    let x := s.point (phi i) M k j
    have hx : dist x p ≤ R*r (phi i) := ((div_lt_iff₀ hri).mp hsource).le
    obtain ⟨l, hl, hxl⟩ := s.netMap_data phi M k i x (hroom x hx)
    change f x = _ at hl
    refine ⟨x, hx, ?_⟩
    change dist (f x) y ≤ epsilon
    rw [hl]
    rw [hmeshEq i] at hxl
    have hxl' := (div_lt_iff₀ hri).mpr hxl
    have hp := (abs_lt.mp (hpair j l)).2
    have hlim : dist (some ⟨M,k,j⟩ : s.Index) (some ⟨M,k,l⟩) < alpha+delta := by
      linarith only [hp, hxl']
    have ht := dist_triangle ((some ⟨M,k,l⟩ : s.Index) : UniformSpace.Completion s.Index)
      ((some ⟨M,k,j⟩ : s.Index) : UniformSpace.Completion s.Index) y
    rw [UniformSpace.Completion.dist_eq, dist_comm (some ⟨M,k,l⟩ : s.Index), dist_comm _ y] at ht
    have hj' : dist ((some ⟨M,k,j⟩ : s.Index) : UniformSpace.Completion s.Index) y < 2*alpha := by
      simpa only [dist_comm] using hj
    rw [dist_comm]
    linarith only [ht, hlim, hj', hsum]

end RegularPointCoordinates.RescalingNetFamily

end

end OAI
