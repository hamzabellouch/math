import OAI.Analysis.LipschitzHilbert.Estimates.PopularTopCount

namespace OAI

/-! The count exponent C_as + 3 max(k,C_as) in the manuscript follows
from the actual witness density and a common polynomial base dilation. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem popular_top_count_powers (hLL : LaceyLiInput) (a k d : ℝ)
    (ha : 0 ≤ a) (hd : 4 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox) (l r : ℝ),
      (∀ i, |(T i).slope| ≤ 1) → ∀ (u : Plane → ℝ) (K : ℝ≥0),
      LipschitzWith K u → 300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^a) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-a)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) → ∀ t : ℝ, 0 < t →
      (volume.prod volume) ({z | z.1 ∈ Icc l r} ∩ {z | t < ∑ i, (T i).weight (L^k) d z}) ≤
        ENNReal.ofReal ((C*L^(a+3*max k a)*Real.sqrt (∑ i, (T i).area))^2/t^2) := by
  classical
  obtain ⟨C,hC,hcount⟩ := popular_top_count_weak_two hLL
  refine ⟨16*4^d*C, by positivity, ?_⟩
  intro L hL ι _ T l r hs u K hu hlength E hEmeas hdisj hE hclose hsize t ht
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  let α : ℝ≥0 := ⟨L^(-a), by positivity⟩
  have hα : 0 < α := by change (0:ℝ)<L^(-a); positivity
  have hα1 : α ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hpka : L^k ≤ L^(max k a) := Real.rpow_le_rpow_of_exponent_le hL (le_max_left _ _)
  have hpaa : L^a ≤ L^(max k a) := Real.rpow_le_rpow_of_exponent_le hL (le_max_right _ _)
  have hR : 1 ≤ 2*L^(max k a) := by
    have hp : 1 ≤ L^(max k a) := Real.one_le_rpow hL (ha.trans (le_max_right _ _))
    linarith
  have hPR : L^k ≤ 2*L^(max k a) := hpka.trans (by nlinarith [Real.rpow_nonneg hLpos.le (max k a)])
  have hER (i : ι) (z : ℝ × ℝ) (hz : z ∈ E i) :
      z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation (2*L^(max k a)) := by
    refine ⟨(hE i z hz).1, ?_⟩
    change (T i).radius z ≤ 2*L^(max k a)
    exact (hE i z hz).2.trans (hpaa.trans (by nlinarith [Real.rpow_nonneg hLpos.le (max k a)]))
  have h := hcount ι T l r (2*L^(max k a)) hR hs u K α hu hα hα1 hlength E
    hEmeas hdisj hER hclose hsize (L^k) d (by positivity) hPR hd t ht
  have hp : L^a*(L^(max k a))^3 = L^(a+3*max k a) := by
    rw [← Real.rpow_mul_natCast hLpos.le]
    rw [← Real.rpow_add hLpos]
    congr 1
    norm_num [mul_comm]
  have heq : 2*4^d*(C/(α:ℝ))*Real.sqrt (∑ i, (T i).area)*(2*L^(max k a))^3 =
      (16*4^d*C)*L^(a+3*max k a)*Real.sqrt (∑ i, (T i).area) := by
    change 2*4^d*(C/L^(-a))*Real.sqrt (∑ i, (T i).area)*(2*L^(max k a))^3 = _
    rw [Real.rpow_neg hLpos.le, div_inv_eq_mul, ← hp]
    ring
  simpa only [heq] using h

end LipschitzHilbert

end

end OAI
