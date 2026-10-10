import OAI.Geometry.RCD.Heat.HeatFisherRiccati
import OAI.Geometry.RCD.Coordinates.RegularizedFisherContinuity
import OAI.Geometry.RCD.Heat.LiYauFisherBound

namespace OAI

/-! # The actual weighted parameter-two Li--Yau estimate

The initial heat data and weight are bounded nonnegative L² functions. A
positive finite weight mass suffices; the heat source may be unbounded.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem heat_liYau_weighted (hK : K≤0)
    (f w : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (hw0 : 0≤w) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) (hw : ∀ᵐ x ∂hausdorff n X, |w x|≤B)
    (hwi : Integrable w (hausdorff n X)) (hwm : 0<∫ x, w x ∂hausdorff n X)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) :
    (∫ x, w x*localGamma (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic T hT f)
      (heatSobolev (hausdorff n X) hX.quadratic T hT f) x /
      (ε+heatAt (hausdorff n X) hX.quadratic T f x) ∂hausdorff n X)-
      2*inner ℝ w (-heatGeneratorAt (hausdorff n X) hX.quadratic T f) ≤
    2*(n:ℝ)*(ε*(∫ x, w x ∂hausdorff n X)+
      inner ℝ w (heatAt (hausdorff n X) hX.quadratic T f))*(|K|+1/T) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let I := regularizedFisherInterpolation μ Q f w ε T
  let M := ε*(∫ x, w x ∂μ)+inner ℝ w (heatAt μ Q T f)
  let D := inner ℝ w (-heatGeneratorAt μ Q T f)
  have hn0 : 0<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) hn)
  have hip : 0 ≤ inner ℝ w (heatAt μ Q T f) := by
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [(Lp.coeFn_nonneg _).mpr hw0,
      (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q T f hf0)] with x hx hy
    simpa only [Real.inner_apply,Pi.zero_apply] using mul_nonneg hx hy
  have hM : 0<M := add_pos_of_pos_of_nonneg (mul_pos hε hwm) hip
  have hIc : ContinuousOn I (Ico 0 T) := by
    intro t ht
    exact (hX.regularizedFisherInterpolation_continuousAt hn p f w hf0 A hf ht.2 hε).continuousWithinAt
  have hI0 : ContinuousAt I 0 :=
    hX.regularizedFisherInterpolation_continuousAt hn p f w hf0 A hf hT hε
  have hIpos (t : ℝ) (ht : t∈Ioo 0 T) : 0≤I t := by
    dsimp only [I,regularizedFisherInterpolation]
    rw [dite_eq_left (sub_pos.mpr ht.2)]
    apply integral_nonneg_of_ae
    filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q t w hw0),
      (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q (T-t) f hf0),
      localGamma_self μ Q (heatSobolev μ Q (T-t) (sub_pos.mpr ht.2) f)] with x hx hy hz
    rw [hz]
    exact div_nonneg (mul_nonneg hx (sq_nonneg _)) (add_nonneg hε.le hy)
  have hId (t : ℝ) (ht : t∈Ioo 0 T) :
      ∃ rate : ℝ, HasDerivAt I rate t ∧
        (2/(n:ℝ))*(D-I t)^2-2*|K| * M*I t≤M*rate := by
    obtain ⟨rate,hrate,hbound⟩ := hX.regularizedFisherInterpolation_riccati hn p
      hK f w hf0 hw0 A B hf hw hwi ht.1 ht.2 hε
    refine ⟨rate,hrate,?_⟩
    change (2/(n:ℝ))*(D-I t)^2+2*K*M*I t≤M*rate at hbound
    rw [abs_of_nonpos hK]
    nlinarith only [hbound]
  have hb := liYau_fisher_bound hT hn0 hM (abs_nonneg K) hI0 hIc hIpos hId
  simpa only [I,D,M,regularizedFisherInterpolation,sub_zero,heatAt_zero,one_apply_eq_self,
    dite_eq_left hT] using hb

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
