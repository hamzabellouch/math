import Mathlib
import OAI.Analysis.BiholderTransport.Contact.ActiveLocalGrowth
import OAI.Analysis.BiholderTransport.Calculus.SecondFderivScalarComp

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def scalarCostSupport (φ : ℝ → ℝ) (v0 : ℝ) (x : M)
    (p : TangentSpace 𝓘(ℝ,Model n) x) (s : ℝ) (y : M) : ℝ :=
  φ (v0+cost x (riemannianExp x (s • p))/s-cost y (riemannianExp x (s • p))/s)

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma scalarCostSupport_self (φ : ℝ → ℝ) (v0 : ℝ) (x : M)
    (p : TangentSpace 𝓘(ℝ,Model n) x) (s : ℝ) :
    scalarCostSupport φ v0 x p s x=φ v0 := by simp [scalarCostSupport]

lemma scalarCostSupport_lower {u v : M → ℝ} (hu : Continuous u)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} (hφ : Monotone φ) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    (hc : contactGap v u x (riemannianExp x p)=0) {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (y : M) : scalarCostSupport φ (v x) x p s y≤φ (v y) := by
  have ha : contactGap (cTransform u) u x (riemannianExp x p)=0 := by rwa [←hdual.2]
  have H := active_split_lower_support hu hp ha hs hs1 y
  rw [←hdual.2] at H
  apply hφ
  rw [neg_sub,sub_div] at H
  linarith only [H]

lemma scalarCostSupport_normal_jet {φ : ℝ → ℝ} {v0 l : ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {s : ℝ} (hs : s≠0)
    (hp : s • p∈injectivityDomain x) (hφ : ContDiffAt ℝ 2 φ v0)
    (hl : deriv φ v0=l) :
    ContDiffAt ℝ 2 (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      scalarCostSupport φ v0 x p s (riemannianExp x h)) 0 ∧
    HasFDerivAt (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      scalarCostSupport φ v0 x p s (riemannianExp x h)) (innerSL ℝ (l • p)) 0 ∧
    ∀ ξ : TangentSpace 𝓘(ℝ,Model n) x,
      fderiv ℝ (fderiv ℝ (fun h => scalarCostSupport φ v0 x p s (riemannianExp x h))) 0 ξ ξ =
        -(l/s)*hessianValue x (s • p) ξ+iteratedDeriv 2 φ v0*(inner ℝ p ξ)^2 := by
  let C := normalCost x (s • p)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x => v0+C 0/s+(-s⁻¹)*C h
  have hf0 : f 0=v0 := by dsimp [f]; ring
  have hC : ContDiffAt ℝ 2 C 0 :=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hf : ContDiffAt ℝ 2 f 0 := contDiffAt_const.add (contDiffAt_const.mul hC)
  have hD : HasFDerivAt f (innerSL ℝ p) 0 := by
    apply (((normalCost_hasFDerivAt_zero hp).const_mul (-s⁻¹)).const_add (v0+C 0/s)).congr_fderiv
    ext h
    simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,inner_neg_left,real_inner_smul_left]
    field_simp
  have he (h : TangentSpace 𝓘(ℝ,Model n) x) :
      scalarCostSupport φ v0 x p s (riemannianExp x h)=φ (f h) := by
    dsimp [scalarCostSupport,f,C,normalCost]
    rw [riemannianExp_zero]
    congr 1
    ring
  have heq : (fun h => scalarCostSupport φ v0 x p s (riemannianExp x h))=fun h => φ (f h) := funext he
  rw [heq]
  have hφf : ContDiffAt ℝ 2 φ (f 0) := hf0.symm ▸ hφ
  refine ⟨hφf.comp 0 hf,?_,?_⟩
  · have H := (hφf.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt 0 hD
    rw [hf0,hl] at H
    apply H.congr_fderiv
    ext h
    simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,real_inner_smul_left]
  · intro ξ
    rw [second_fderiv_scalar_comp hf hφf ξ,hf0,hl,hD.fderiv]
    have H : fderiv ℝ (fderiv ℝ f) 0 ξ ξ=(-s⁻¹)*hessianValue x (s • p) ξ := by
      have hd : fderiv ℝ f=fun h => (-s⁻¹) • fderiv ℝ C h := by
        funext h
        dsimp only [f]
        rw [fderiv_const_add]
        exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := C) (-s⁻¹)) h
      rw [hd]
      change fderiv ℝ ((-s⁻¹) • fderiv ℝ C) 0 ξ ξ = _
      rw [fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ C) (-s⁻¹)]
      rw [hessianValue_eq_normalHessian hp]
      rfl
    rw [H]
    simp only [innerSL_apply_apply]
    ring

end WeakMTWTransport

end

end OAI
