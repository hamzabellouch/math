import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Combining the two one-sided evolution inequalities on a time diagonal -/

open Set Filter MeasureTheory
open scoped Topology
namespace RegularPointCoordinates

theorem two_rate_evi_frequent_slope {D G H : ℝ → ℝ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hG : ∀ a b : ℝ, 0 < a → 0 < b → ContinuousAt (Function.uncurry G) (a,b))
    (hH : ∀ a b : ℝ, 0 < a → 0 < b → ContinuousAt (Function.uncurry H) (a,b))
    (hI : ∀ a b s : ℝ, 0 < a → a ≤ b → 0 < s →
      (D b s-D a s)/2 ≤ ∫q in a..b, G q s)
    (hJ : ∀ a b s : ℝ, 0 < a → a ≤ b → 0 < s →
      (D s b-D s a)/2 ≤ ∫q in a..b, H s q) :
    ∀ r, 2*(G t t+H t t) < r → ∃ᶠ z in 𝓝[>] t,
      slope (fun q => D q q) t z < r := by
  intro r hr
  let ε := (r-2*(G t t+H t t))/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  let F : ℝ × ℝ → ℝ := fun z => G z.1 z.2+H t z.1
  have hHc : ContinuousAt (fun z : ℝ × ℝ => H t z.1) (t,t) :=
    (hH t t ht ht).comp (x := (t,t)) (f := fun z : ℝ × ℝ => (t,z.1))
      (continuousAt_const.prodMk continuousAt_fst)
  have hF : ContinuousAt F (t,t) := (hG t t ht ht).add hHc
  obtain ⟨δ,hδ,hnear⟩ := Metric.continuousAt_iff.mp hF ε hε
  have he : ∀ᶠ z in 𝓝[>] t, slope (fun q => D q q) t z < r := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show t < t+δ by linarith)),
      self_mem_nhdsWithin] with z hz hz'
    change z < t+δ at hz
    have htz : t < z := hz'
    have hz0 : 0 < z := ht.trans htz
    have hbound : ∀ q ∈ Icc t z, F (q,z) ≤ G t t+H t t+ε := by
      intro q hq
      have hd : dist (q,z) (t,t) < δ := by
        rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hq.1),
          abs_of_pos (sub_pos.mpr htz)]
        exact max_lt_iff.mpr ⟨by linarith [hq.2],by linarith⟩
      have hh := hnear hd
      rw [Real.dist_eq] at hh
      change |F (q,z)-(G t t+H t t)| < ε at hh
      linarith [(abs_lt.mp hh).2]
    have hi : IntervalIntegrable (fun q => G q z) volume t z :=
      ContinuousOn.intervalIntegrable_of_Icc htz.le (fun q hq =>
        ((hG q z (ht.trans_le hq.1) hz0).comp (f := fun w : ℝ => (w,z))
          (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt)
    have hj : IntervalIntegrable (fun q => H t q) volume t z :=
      ContinuousOn.intervalIntegrable_of_Icc htz.le (fun q hq =>
        ((hH t q ht (ht.trans_le hq.1)).comp (f := fun w : ℝ => (t,w))
          (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt)
    have hB := intervalIntegral.integral_mono_on htz.le (hi.add hj) intervalIntegrable_const hbound
    rw [intervalIntegral.integral_const,smul_eq_mul] at hB
    rw [intervalIntegral.integral_add hi hj] at hB
    have hi' := hI t z z ht htz.le hz0
    have hj' := hJ t z t ht htz.le ht
    have hsec : (D z z-D t t)/(z-t) ≤ 2*(G t t+H t t+ε) := by
      apply (div_le_iff₀ (sub_pos.mpr htz)).mpr
      nlinarith only [hi',hj',hB]
    rw [slope_def_field]
    exact hsec.trans_lt (by dsimp [ε]; linarith)
  exact he.frequently

end RegularPointCoordinates

end OAI
