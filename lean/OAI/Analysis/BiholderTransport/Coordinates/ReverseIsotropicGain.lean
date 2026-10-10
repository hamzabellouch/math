import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.HessianMixedOperator
import OAI.Analysis.BiholderTransport.LinearAlgebra.RescaledJoinOperator
import OAI.Analysis.BiholderTransport.Regularity.InverseDifferenceGain

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteReverseGain (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma exists_reverse_exp_rescaled_fixedJoin_factor {x y : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {q : TangentSpace 𝓘(ℝ,Model n) y}
    (hh : 0<h) (hhT : h<T) (hp : T • p∈injectivityDomain x)
    (hq : q∈injectivityDomain y) (hpx : riemannianExp x (T • p)=y)
    (hqy : riemannianExp y q=x) :
    ∃ R : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
      (∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w) ∧
      fixedJoinOperator x h T p=(fderiv ℝ R q).comp
        (T • (normalEndpointMixedOperator x y (h/T) (T • p)).adjoint) := by
  have hT : 0<T := hh.trans hhT
  have ht : 0<h/T := div_pos hh hT
  have ht1 : h/T<1 := (div_lt_one hT).mpr hhT
  obtain ⟨R,hR,hRq,hRi,hfac⟩ := exists_reverse_exp_fixedJoin_factor ht ht1 hp hq hpx hqy
  refine ⟨R,hR,hRq,hRi,?_⟩
  rw [fixedJoinOperator_regular_rescale hp hh hhT,hfac]
  ext v
  simp only [smul_apply,ContinuousLinearMap.comp_apply,map_smul]

lemma exists_reverse_exp_divided_isotropic_gain {x y : M} {h s t a c : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {q : TangentSpace 𝓘(ℝ,Model n) y}
    (hh : 0<h) (hhs : h<s) (hht : h<t)
    (hps : s • p∈injectivityDomain x) (hpt : t • p∈injectivityDomain x)
    (hq : q∈injectivityDomain y) (hpx : riemannianExp x (s • p)=y)
    (hqy : riemannianExp y q=x) (ha : 0<a) (hc : 0≤c)
    (hcross : ∀ v : TangentSpace 𝓘(ℝ,Model n) x,
      c*‖v‖^2≤fixedJoinMiddle x h s p v v-fixedJoinMiddle x h t p v v)
    (hbound : s*‖normalEndpointMixedOperator x y (h/s) (s • p)‖≤a) :
    ∃ R : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
      (∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w) ∧
      ∀ w : TangentSpace 𝓘(ℝ,Model n) y,
        (c/a^2)*‖w‖^2 ≤ hessianValue x (s • p) (fderiv ℝ R q w)/s-
          hessianValue x (t • p) (fderiv ℝ R q w)/t := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let W := TangentSpace 𝓘(ℝ,Model n) y
  let D := fixedJoinOperator x h s p
  let B := fixedJoinOperator x h t p
  let C := s • (normalEndpointMixedOperator x y (h/s) (s • p)).adjoint
  have hs : 0<s := hh.trans hhs
  obtain ⟨R,hR,hRq,hRi,hfactor⟩ := exists_reverse_exp_rescaled_fixedJoin_factor hh hhs hps hq hpx hqy
  obtain ⟨S,hDS,hAs⟩ := fixedJoinAction_schur hps hh hhs
  obtain ⟨U,hBU,hAt⟩ := fixedJoinAction_schur hpt hh hht
  have hDs : ∀ v:V, D (S v)=v := fun v => inverse_of_bilinear_pairing hDS v
  have hBu : ∀ v:V, B (U v)=v := fun v => inverse_of_bilinear_pairing hBU v
  have hBs : B.toLinearMap.IsSymmetric := fixedJoinOperator_symmetric
    ((fixedJoinAction_regular_contDiffAt hpt hh hht).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hUn : ∀ v:V, 0 ≤ inner ℝ (U v) v :=
    fixedJoinOperator_inverse_nonneg hpt hh hht hBu
  have hfac : ∀ v:V, D v=fderiv ℝ R q (C v) := fun v =>
    congrArg (fun A : V →L[ℝ] V => A v) hfactor
  have hCs : Function.Surjective C := factor_surjective_of_right_inverse
    (show finrank ℝ V=finrank ℝ W from rfl) hDs hfac
  have hCn : ‖C‖≤a := by
    dsimp only [C]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs,LinearIsometryEquiv.norm_map]
    exact hbound
  have hC : ∀ v:V, ‖C v‖≤a*‖v‖ := fun v =>
    (C.le_opNorm v).trans (mul_le_mul_of_nonneg_right hCn (norm_nonneg v))
  have hcross' : ∀ v:V, c*‖v‖^2≤ inner ℝ ((D-B) v) v := by
    intro v
    simpa only [sub_apply,inner_sub_left,D,B,fixedJoinOperator_inner]
      using hcross v
  refine ⟨R,hR,hRq,hRi,?_⟩
  intro w
  have H := inverse_difference_isotropic_of_factor ha hc hBs hBu
    (left_inverse_of_right_inverse hDs) hUn hcross' hfac hCs hC w
  rw [inner_sub_left] at H
  linarith only [H,hAs (fderiv ℝ R q w),hAt (fderiv ℝ R q w)]

end WeakMTWTransport

end

end OAI
