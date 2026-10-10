import OAI.Geometry.RCD.Sobolev.ComposedGammaPairingVariation
import OAI.Geometry.RCD.Heat.HeatTailGradient
import OAI.Geometry.RCD.Coordinates.ShiftedLogarithmJets

namespace OAI

/-! # Exact weighted Fisher variation along actual RCD heat tails -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem heat_fisher_tail_hasDerivAt
    (f w : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) (hw : ∀ᵐ x ∂hausdorff n X, |w x|≤B)
    {a T t ε : ℝ} (ha : 0<a) (ht : 0<t) (htT : a<T-t) (hε : 0<ε) :
    let F := fun s => heatTail (hausdorff n X) hX.quadratic a ha f (T-s)
    let D := heatSobolevMap (hausdorff n X) hX.quadratic a ha
      (-heatGeneratorAt (hausdorff n X) hX.quadratic (T-t-a) f)
    HasDerivAt (fun s => ∫ x, heatAt (hausdorff n X) hX.quadratic s w x *
      localGamma (hausdorff n X) hX.quadratic (F s) (F s) x /
        (ε+SobolevSpace.toLp (hausdorff n X) hX.quadratic (F s) x) ∂hausdorff n X)
      ((∫ x, (-heatGeneratorAt (hausdorff n X) hX.quadratic t w) x *
        localGamma (hausdorff n X) hX.quadratic (F t) (F t) x /
          (ε+SobolevSpace.toLp (hausdorff n X) hX.quadratic (F t) x) ∂hausdorff n X)+
       (∫ x, heatAt (hausdorff n X) hX.quadratic t w x *
        SobolevSpace.toLp (hausdorff n X) hX.quadratic D x *
        localGamma (hausdorff n X) hX.quadratic (F t) (F t) x /
          (ε+SobolevSpace.toLp (hausdorff n X) hX.quadratic (F t) x)^2 ∂hausdorff n X)-
       2*(∫ x, heatAt (hausdorff n X) hX.quadratic t w x *
        localGamma (hausdorff n X) hX.quadratic (F t) D x /
          (ε+SobolevSpace.toLp (hausdorff n X) hX.quadratic (F t) x) ∂hausdorff n X)) t := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let F := fun s => heatTail μ Q a ha f (T-s)
  let D := heatSobolevMap μ Q a ha (-heatGeneratorAt μ Q (T-t-a) f)
  obtain ⟨L,hL⟩ := hX.heatTail_gradient_bound hn p f A hf ha
  have hFl : ∀ s, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q (F s) x≤L := fun s => hL (T-s)
  have hFd : HasDerivAt F (-D) t := by
    have hh := (heatTail_hasDerivAt μ Q a ha f (T-t) htT).scomp t
      ((hasDerivAt_const t T).sub (hasDerivAt_id t))
    simpa only [F,D,Function.comp_def,zero_sub,neg_smul,one_smul] using hh
  have hval (s : ℝ) : ∀ᵐ x ∂μ, SobolevSpace.toLp μ Q (F s) x∈Icc 0 (A:ℝ) := by
    have hP := heatAt_nonneg μ Q a (heatAt μ Q (T-s-a) f)
      (heatAt_nonneg μ Q (T-s-a) f hf0)
    have hA := heatAt_abs_le_const μ Q a A (heatAt μ Q (T-s-a) f)
      (heatAt_abs_le_const μ Q (T-s-a) A f hf)
    filter_upwards [(Lp.coeFn_nonneg _).mpr hP,hA] with x hx hy
    exact ⟨hx,(le_abs_self _).trans hy⟩
  obtain ⟨φ,b,db,C,J,N,E,H,hφ,hb,hdb,hφ0,hdφ,hdb',hE,hH,he⟩ :=
    shifted_logarithm_jets hε A.coe_nonneg
  let W := heatAt μ Q t w
  have hWb := heatAt_abs_le_const μ Q t B w hw
  have hWi : MemLp W ∞ μ := memLp_top_of_bound (Lp.aestronglyMeasurable W) B
    (by simpa only [Real.norm_eq_abs] using hWb)
  let θ := hWi.toLp W
  have hθ : θ =ᵐ[μ] W := hWi.coeFn_toLp
  have hθb : ∀ᵐ x ∂μ, |θ x|≤B := by
    filter_upwards [hθ,hWb] with x hx hy
    exact hx ▸ hy
  have hh := composed_gamma_pairing_hasDerivAt μ Q hFd (heatAt_hasDerivAt μ Q t ht w)
    L hFl θ hθ B hθb hb hdb hdb' E hE
  have hfun (s : ℝ) : (∫ x, heatAt μ Q s w x*b (SobolevSpace.toLp μ Q (F s) x)*
      localGamma μ Q (F s) (F s) x ∂μ) =
      ∫ x, heatAt μ Q s w x*localGamma μ Q (F s) (F s) x /
        (ε+SobolevSpace.toLp μ Q (F s) x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hval s] with x hx
    rw [(he _ hx).2.1]
    ring
  have hfirst : (∫ x, (-heatGeneratorAt μ Q t w) x*b (SobolevSpace.toLp μ Q (F t) x)*
      localGamma μ Q (F t) (F t) x ∂μ) =
      ∫ x, (-heatGeneratorAt μ Q t w) x*localGamma μ Q (F t) (F t) x /
        (ε+SobolevSpace.toLp μ Q (F t) x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hval t] with x hx
    rw [(he _ hx).2.1]
    ring
  have hsecond : (∫ x, heatAt μ Q t w x*db (SobolevSpace.toLp μ Q (F t) x)*
      SobolevSpace.toLp μ Q (-D) x*localGamma μ Q (F t) (F t) x ∂μ) =
      ∫ x, heatAt μ Q t w x*SobolevSpace.toLp μ Q D x*
        localGamma μ Q (F t) (F t) x /(ε+SobolevSpace.toLp μ Q (F t) x)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hval t,Lp.coeFn_neg (SobolevSpace.toLp μ Q D)] with x hx hy
    change SobolevSpace.toLp μ Q (-D) x = _ at hy
    rw [(he _ hx).2.2,hy]
    simp only [Pi.neg_apply]
    ring
  have hthird : (∫ x, heatAt μ Q t w x*b (SobolevSpace.toLp μ Q (F t) x)*
      localGamma μ Q (F t) (-D) x ∂μ) =
      -(∫ x, heatAt μ Q t w x*localGamma μ Q (F t) D x /
        (ε+SobolevSpace.toLp μ Q (F t) x) ∂μ) := by
    rw [←integral_neg]
    apply integral_congr_ae
    have hneg := localGamma_smul_right μ Q (-1) (F t) D
    simp only [neg_one_smul] at hneg
    filter_upwards [hval t,hneg] with x hx hy
    rw [(he _ hx).2.1,hy]
    ring
  simpa only [hfun,hfirst,hsecond,hthird,mul_neg,←sub_eq_add_neg] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
