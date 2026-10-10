import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.BranchCost2
import OAI.Analysis.BiholderTransport.Regularity.Reversal
import OAI.Analysis.BiholderTransport.Coordinates.NormalEikonal
import OAI.Analysis.BiholderTransport.Calculus.SecondDerivativeSlice
import OAI.Analysis.BiholderTransport.LinearAlgebra.RadialHessian

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section RadialFactor
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma normal_log_fderiv_exp_norm {x y : M}
    {q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hq : DifferentiableAt ℝ q 0)
    (hqr : ∀ᶠ a in 𝓝 0, riemannianExp y (q a)=riemannianExp x a)
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) y) 𝓘(ℝ,Model n)
      (riemannianExp y) (q 0) (fderiv ℝ q 0 v)‖=‖v‖ := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  have he := (contMDiff_riemannianExp_fiber y (q 0)).mdifferentiableAt (by simp)
  have hD := (he.hasMFDerivAt.comp 0 hq.hasFDerivAt.hasMFDerivAt)
  have hqr' : (riemannianExp y ∘ q) =ᶠ[𝓝 0] riemannianExp x := hqr
  have hD' := hD.congr_of_eventuallyEq hqr'.symm
  have hE := hD'.mfderiv
  have hN := mfderiv_exp_zero_norm x v
  rw [hE] at hN
  have he0 := hqr.self_of_nhds
  convert! hN using 1
  congr 1
  rw [he0]

lemma normalHessian_radial_derivative_factor {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    ∃ L : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
        TangentSpace 𝓘(ℝ,Model n) (reverseRay (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      Function.Injective L ∧
      (∀ v, ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) (reverseRay (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
        𝓘(ℝ,Model n) (riemannianExp (reverseRay (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
        (reverseRay (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 (L v)‖=‖v‖) ∧ ∀ v,
      HasDerivAt (fun s : ℝ => normalHessian x (s • p) v v)
        (normalHessian x p v v-‖L v‖^2) 1 := by
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let y := (reverseRay z).1
  let r := (reverseRay z).2
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  have hr : r∈injectivityDomain y := reverseRay_injectivityDomain hp
  have he : riemannianExp y r=x := reverseRay_endpoint z
  obtain ⟨q,hq0,hq,hqr,hqeq⟩ := exists_normal_eikonal_log hr he
  let L := fderiv ℝ q 0
  refine ⟨L,normal_log_fderiv_injective (hq.differentiableAt (by simp)) hqr,?_,?_⟩
  · intro v
    have H := normal_log_fderiv_exp_norm (hq.differentiableAt (by simp)) hqr v
    rw [hq0] at H
    exact H
  intro v
  let B := doubleNormalCost (n := n) x y
  have hB : ContDiffAt ℝ 3 B (0,0) := (doubleNormalCost_contDiffAt hr he).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hq2 : ContDiffAt ℝ 2 q 0 := hq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have heik : (fun a : X => B (a,0))=ᶠ[𝓝 0] fun a => ‖-q a‖^2/2 := by
    filter_upwards [hqeq] with a ha
    simpa only [norm_neg] using ha.1
  have hgrad : ∀ᶠ a : X in 𝓝 0, ∀ w : Y,
      fderiv ℝ B (a,0) (0,w)=inner ℝ (-q a) w := by
    have hBa : ∀ᶠ a : X in 𝓝 0, ContDiffAt ℝ 3 B (a,0) :=
      (continuousAt_id.prodMk continuousAt_const).eventually (hB.eventually (by norm_num))
    filter_upwards [hqeq,hBa] with a ha hBa
    intro w
    have hd := (hBa.differentiableAt (by norm_num)).hasFDerivAt.comp 0
      ((hasFDerivAt_const a (0:Y)).prodMk (hasFDerivAt_id 0))
    have hv := congrArg (fun D : Y →L[ℝ] ℝ => D w) hd.fderiv
    change fderiv ℝ (fun b => doubleNormalCost x y (a,b)) 0 w=
      fderiv ℝ B (a,0) (0,w) at hv
    rw [ha.2] at hv
    exact hv.symm
  have heik3 := eikonal_third_derivative hB hq2.neg heik hgrad (v := v)
  have hS := second_derivative_source_slice (hB.of_le (by norm_num)) v v
  have hBzero : (fun a : X => B (a,0))=normalCost x p := by
    funext a
    simp only [B,doubleNormalCost,normalCost,riemannianExp_zero]
    rw [riemannianExp_eq_sprayFlow x p]
    rfl
  rw [hBzero] at hS
  change normalHessian x p v v=_ at hS
  have hneg : fderiv ℝ (fun a : X => -q a) 0 = -L := by
    exact fderiv_fun_neg
  rw [hq0,hneg] at heik3
  change fderiv ℝ (fderiv ℝ B) (0,0) (v,0) (v,0)=
    ‖-(L v)‖^2+fderiv ℝ (fderiv ℝ (fderiv ℝ B)) (0,0) (0,-r) (v,0) (v,0) at heik3
  rw [norm_neg,←hS] at heik3
  have hline := hasDerivAt_source_hessian_line (a := (0:X)) (b := (0:Y))
    (w := -r) (t := 1) (v := v) hB
  have hf : (fun s : ℝ => fderiv ℝ (fderiv ℝ
      (fun a : X => B (a,(0:Y)+(s-1) • (-r)))) 0 v v)=
        (fun s : ℝ => normalHessian x (s • p) v v) := by
    funext s
    congr 3
    funext a
    dsimp [B,doubleNormalCost,normalCost]
    have hs : (0:Y)+(s-1) • (-r)=(1-s) • r := by
      simp only [zero_add,smul_neg,←neg_smul]
      congr 1
      ring
    rw [hs,exp_reverseRay_line z s]
    rfl
  rw [hf] at hline
  convert hline using 1
  linarith

end RadialFactor
end WeakMTWTransport

end

end

end

end OAI
