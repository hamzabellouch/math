import OAI.Geometry.RCD.Metric.RescaledEvolution
import OAI.Geometry.RCD.Metric.DimensionalRateContinuity
import OAI.Geometry.RCD.Metric.DimensionalRatePair

namespace OAI

/-! # Dimensional transport expansion from the two evolution inequalities -/

open Set Filter MeasureTheory
open scoped Topology
namespace RegularPointCoordinates

theorem dimensional_evi_expansion {D : ℝ → ℝ → ℝ} {P Q : ℝ → ℝ}
    {K N α β a b : ℝ} (hK : K ≤ 0) (hN : 0 < N)
    (hα : 0 < α) (hβ : 0 < β) (ha : 0 < a) (hab : a ≤ b)
    (hD0 : ∀ u v, 0 < u → 0 < v → 0 ≤ D u v)
    (hD : ∀ u v, 0 < u → 0 < v → ContinuousAt (Function.uncurry D) (u,v))
    (hP : ∀ u, 0 < u → ContinuousAt P u)
    (hQ : ∀ u, 0 < u → ContinuousAt Q u)
    (hI : ∀ u v s, 0 < u → u ≤ v → 0 < s →
      (D v s-D u s)/2 ≤ ∫q in u..v, dimensionalEntropyRate K N (D q s,P q,Q s))
    (hJ : ∀ u v s, 0 < u → u ≤ v → 0 < s →
      (D s v-D s u)/2 ≤ ∫q in u..v, dimensionalEntropyRate K N (D s q,Q q,P s)) :
    D (α*b) (β*b) ≤ gronwallBound (D (α*a) (β*a)) (-K*(α+β))
      (2*N*(Real.sqrt α-Real.sqrt β)^2) (b-a) := by
  let G := fun u v => dimensionalEntropyRate K N (D u v,P u,Q v)
  let H := fun u v => dimensionalEntropyRate K N (D u v,Q v,P u)
  have hGc : ∀ u v, 0 < u → 0 < v → ContinuousAt (Function.uncurry G) (u,v) := by
    intro u v hu hv
    exact (continuous_dimensionalEntropyRate hK hN).continuousAt.comp
      ((hD u v hu hv).prodMk (((hP u hu).comp continuousAt_fst).prodMk
        ((hQ v hv).comp continuousAt_snd)))
  have hHc : ∀ u v, 0 < u → 0 < v → ContinuousAt (Function.uncurry H) (u,v) := by
    intro u v hu hv
    exact (continuous_dimensionalEntropyRate hK hN).continuousAt.comp
      ((hD u v hu hv).prodMk (((hQ v hv).comp continuousAt_snd).prodMk
        ((hP u hu).comp continuousAt_fst)))
  apply evolution_gronwall hab
  · intro t ht
    exact ((hD _ _ (mul_pos hα (ha.trans_le ht.1)) (mul_pos hβ (ha.trans_le ht.1))).comp (x := t)
      (f := fun q : ℝ => (α*q,β*q)) (by fun_prop)).continuousWithinAt
  · intro t ht r hr
    exact two_rate_evi_rescaled hα hβ (ha.trans_le ht.1) hGc hHc hI hJ r hr
  · intro t ht
    have hd := hD0 (α*t) (β*t) (mul_pos hα (ha.trans_le ht.1)) (mul_pos hβ (ha.trans_le ht.1))
    have hc : 0 ≤ -(K*D (α*t) (β*t)/N) := neg_nonneg.mpr
      (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hK hd) hN.le)
    have hh := dimensional_rate_pair hN.le hc hα.le hβ.le
      (Real.exp_pos (-P (α*t)/N)) (Real.exp_pos (-Q (β*t)/N))
    change 2*(α*dimensionalEntropyRate K N (D (α*t) (β*t),P (α*t),Q (β*t))+
      β*dimensionalEntropyRate K N (D (α*t) (β*t),Q (β*t),P (α*t))) ≤ _
    rw [dimensionalEntropyRate_eq hd,dimensionalEntropyRate_eq hd]
    have he : N*(-(K*D (α*t) (β*t)/N))*(α+β)/2 =
        (-K*(α+β)*D (α*t) (β*t))/2 := by field_simp
    rw [he] at hh
    linarith only [hh]

end RegularPointCoordinates

end OAI
