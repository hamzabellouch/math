import OAI.Dynamics.StandardMap.ScaledChart

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_liftProjection : Continuous liftProjection :=
  (((AddCircle.continuous_mk' (1:ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd))
lemma interval_small_move (y y' : ℝ) (hy : y ∈ Icc (0:ℝ) 1) (hmove : |y'-y| ≤ 1) :
    y' ∈ Ioc (-2:ℝ) 2 := by
  have hh := abs_le.mp hmove
  constructor <;> linarith [hy.1,hy.2,hh.1,hh.2]
lemma actual_backward_slice (k : ℝ) (n B : ℕ) (hn : 1 ≤ n) (hB : B=n ∨ B=n+1) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (ha : 24/growthBase k^((4/5:ℝ)) ≤ 1/2)
    (D : Set ℝ) (hD : MeasurableSet D) (X X' : ℝ → ℝ) (l u : ℝ)
    (hlen : u-l < 1/4) (hlu : Icc l u ⊆ Icc (0:ℝ) 1)
    (hDunit : D ⊆ Icc (0:ℝ) 1)
    (hXI : ∀ y ∈ D, X y ∈ Icc l u)
    (hX : ∀ y ∈ D, HasStrictDerivAt X (X' y) y)
    (hXs : ∀ y ∈ D, |X' y| ≤ 24/growthBase k^((4/5:ℝ)))
    (hXL : ∀ y ∈ D, ∀ z ∈ D, |X y-X z| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z|)
    (ht : ∀ y ∈ D, tSolution (orbitCoefficient k (X y) y) (n+1) ≠ 0)
    (hU : ∀ y ∈ D, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k (X y) y) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)))
    (W : Torus → ℝ) (hW : Continuous W) (hW0 : ∀ z, 0 ≤ W z) (δ : ℝ) (hδ : 0 ≤ δ)
    (htransport : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(B:ℤ)) z) (liftIter k (-(B:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(B-1:ℕ)) →
      |W (liftProjection z)-W (liftProjection w)| ≤ δ) :
    (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc l u))*
      (∫⁻ y in D, ENNReal.ofReal (W (liftProjection (X y,y)))) ≤
    16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc l u))*
        ENNReal.ofReal δ*volume D := by
  classical
  have hp : 0 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have ha0 : 0 ≤ 24/growthBase k^((4/5:ℝ)) := by positivity
  have htrans : (24/growthBase k^((4/5:ℝ)))^2 < 1 := by nlinarith
  obtain ⟨Θ,J,hΘ,hbase,hlevel,hinj,hJ,hdet,hclose⟩ := actual_backward_carry_full k n hn hk hq hsmall D X X' l u hlen hXI hX hXs hXL htrans ht hU
  let w : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (W (liftProjection (X y,y)))
  have hwc : ContinuousOn w D := by
    apply ENNReal.continuous_ofReal.comp_continuousOn
    apply hW.comp_continuousOn
    apply continuous_liftProjection.comp_continuousOn
    have hxc : ContinuousOn X D := fun y hy => (hX y hy).hasDerivAt.continuousAt.continuousWithinAt
    exact hxc.prodMk continuousOn_id
  have hwm : Measurable (D.indicator w) := by
    exact hwc.measurable_piecewise continuousOn_const hD
  have hbound : (fun z : ℝ × ℝ => (z.1,Θ z)) '' (Icc l u ×ˢ D) ⊆
      Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2 := by
    rintro z ⟨v,hv,rfl⟩
    have hvu := hlu hv.1
    have hxu := hlu (hXI v.2 hv.2)
    have hd : |v.1-X v.2| ≤ 1 := by apply abs_le.mpr; constructor <;> linarith [hvu.1,hvu.2,hxu.1,hxu.2]
    have hc := (hclose v.2 hv.2 v.1 hv.1).1
    refine ⟨⟨by linarith [hvu.1],by linarith [hvu.2]⟩,interval_small_move v.2 (Θ v) (hDunit hv.2) ?_⟩
    exact hc.trans (by nlinarith [abs_nonneg (v.1-X v.2)])
  have htpt (z : ℝ × ℝ) (hz : z ∈ Icc l u ×ˢ D) :
      D.indicator w z.2 ≤ ENNReal.ofReal (W (liftProjection (z.1,Θ z)))+ENNReal.ofReal δ := by
    rw [indicator_of_mem hz.2]
    have he := graph_backward_endpoint_close k hk (z.1,Θ z) (X z.2,z.2) n B hn hB
      (hlevel z.2 hz.2 z.1 hz.1) (hclose z.2 hz.2 z.1 hz.1).2
    have hh := htransport (X z.2,z.2) (z.1,Θ z) (by simpa only [dist_comm] using he)
    calc
      _ ≤ ENNReal.ofReal (W (liftProjection (z.1,Θ z))+δ) := ENNReal.ofReal_le_ofReal (by have := (abs_le.mp hh).2; linarith)
      _ = _ := ENNReal.ofReal_add (hW0 _) hδ
  have hh := sweep_slice_bound (Icc l u) D (fun z : ℝ × ℝ => (z.1,Θ z)) J
    (D.indicator w) (fun z => ENNReal.ofReal (W z)) _ (ENNReal.ofReal δ)
    measurableSet_Icc hD hwm (ENNReal.continuous_ofReal.comp hW).measurable
    hJ hinj (fun z hz => (hdet z hz).1) hbound htpt
  simpa only [setLIntegral_indicator hD,inter_self,w] using hh
end StandardMapEntropy

end OAI
