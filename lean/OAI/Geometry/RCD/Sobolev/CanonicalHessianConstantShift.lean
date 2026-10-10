import OAI.Geometry.RCD.Sobolev.CanonicalHessianApproximation

namespace OAI

/-! # Local constant shifts preserve the canonical Hessian direction -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem canonical_hessian_locality_of_constant (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (v z : SobolevSpace (hausdorff n X) hX.quadratic)
    (V Z : X → ℝ) (Lv Lz Av Az : ℝ≥0)
    (hV : LipschitzWith Lv V) (hZ : LipschitzWith Lz Z)
    (hVc : HasCompactSupport V) (hZc : HasCompactSupport Z)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X] V)
    (hz : SobolevSpace.toLp (hausdorff n X) hX.quadratic z =ᵐ[hausdorff n X] Z)
    (hAv : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic v x| ≤ Av)
    (hAz : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic z x| ≤ Az)
    (c : ℝ)
    (hvz : (fun x => SobolevSpace.toLp (hausdorff n X) hX.quadratic z x-
      SobolevSpace.toLp (hausdorff n X) hX.quadratic v x)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)] fun _ => c)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ D) (hφz : ∀ x∉closedBall p r, φ x=0)
    (I J : Lp ℝ 1 ((hausdorff n X).restrict (closedBall p r)))
    (hI : IsCanonicalHeatHessian (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic s hs f) v p r φ I)
    (hJ : IsCanonicalHeatHessian (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic s hs f) z p r φ J) : I=J := by
  let m := hausdorff n X
  let q := hX.quadratic
  let w := heatSobolev m q s hs f
  obtain ⟨u,du,U,Lu,Pu,hu,hdu,hU,hur,huA,hPu,hgu,huc⟩ :=
    hX.compact_lipschitz_heat_directions hn p v V Lv Av hV hVc hv hAv
  obtain ⟨y,dy,Y,Ly,Py,hy,hdy,hY,hyr,hyA,hPy,hgy,hyc⟩ :=
    hX.compact_lipschitz_heat_directions hn p z Z Lz Az hZ hZc hz hAz
  obtain ⟨AU,UU,hAU,hUU,hIl⟩ := hI
  obtain ⟨AY,YY,hAY,hYY,hJl⟩ := hJ
  have hD2 : ∀ᵐ x ∂m, ‖(φ x)^2‖ ≤ (D^2:ℝ≥0) := by
    filter_upwards [hD] with x hx
    simpa only [norm_pow,Real.norm_eq_abs,NNReal.coe_pow] using pow_le_pow_left₀ (abs_nonneg _) hx 2
  let P := weightedGammaCLM m q (hφ.pow 2) hD2
  have hPc : Continuous (fun b : SobolevSpace m q => P (b-v) (b-v)) := by fun_prop
  have hezero : P (z-v) (z-v)=0 := by
    have hvz' : SobolevSpace.toLp m q (z-v) =ᵐ[m.restrict (closedBall p r)] fun _ => c := by
      simp only [map_sub]
      filter_upwards [hvz,ae_restrict_of_ae
        (Lp.coeFn_sub (SobolevSpace.toLp m q z) (SobolevSpace.toLp m q v))] with x hx he
      exact he.trans hx
    change (∫ x, (φ x)^2*localGamma m q (z-v) (z-v) x ∂m)=0
    apply integral_eq_zero_of_ae
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp hvz',
      localGamma_zero_on_level m q (z-v) (z-v) c] with x hx hh
    change (φ x)^2*localGamma m q (z-v) (z-v) x = (0:ℝ)
    by_cases hm : x∈closedBall p r
    · rw [hh (hx hm),mul_zero]
    · rw [hφz x hm,zero_pow (by decide : (2:ℕ)≠0),zero_mul]
  have huE : Tendsto (fun k => weightedGamma m q (fun x => (φ x)^2) (u k-v) (u k-v))
      atTop (𝓝 0) := by
    have hh := (hPc.tendsto v).comp huc
    change Tendsto (fun k => P (u k-v) (u k-v)) atTop (𝓝 0)
    simpa only [Function.comp_apply,sub_self,map_zero,zero_apply] using! hh
  have hyE : Tendsto (fun k => weightedGamma m q (fun x => (φ x)^2) (y k-v) (y k-v))
      atTop (𝓝 0) := by
    change Tendsto (fun k => P (y k-v) (y k-v)) atTop (𝓝 0)
    simpa only [Function.comp_apply,hezero] using! (hPc.tendsto z).comp hyc
  exact hX.bounded_heat_hessian_approximation_independent hn p hK f A hf hs hr
    u y du dy hdu hdy U Y Lu Ly (fun _ => Av) (fun _ => Az) hU hY hur hyr huA hyA
    (hPu.trans (le_max_left Pu Py))
    (fun k => (ae_restrict_of_ae (hgu k)).mono fun x hx => hx.trans (le_max_left Pu Py))
    (fun k => (ae_restrict_of_ae (hgy k)).mono fun x hx => hx.trans (le_max_right Pu Py))
    φ hφ D hD hφz v huE hyE AU AY UU YY
    (fun k => by simpa only [hu k] using hAU k)
    (fun k => by simpa only [hy k] using hAY k)
    (fun k => by simpa only [hu k] using hUU k)
    (fun k => by simpa only [hy k] using hYY k)
    I J (by simpa only [hu] using hIl) (by simpa only [hy] using hJl)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
