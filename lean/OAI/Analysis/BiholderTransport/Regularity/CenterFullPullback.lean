import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.SecondFderivAdd
import OAI.Analysis.BiholderTransport.Coordinates.NormalLowerTaylorBound
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section CenterFullPullback
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma scalar_support_full_pullback_identity {a b : M}
    {p : TangentSpace 𝓘(ℝ,Model n) a} {q : TangentSpace 𝓘(ℝ,Model n) b}
    {l s : ℝ} {φ : ℝ → ℝ} {v : ℝ}
    (hs : s≠0) (hp : s • p∈injectivityDomain a)
    (hlp : l • p∈injectivityDomain a) (hq : q∈injectivityDomain b)
    (hab : riemannianExp a (l • p)=b)
    (hφ : ContDiffAt ℝ 2 φ v) (hφd : deriv φ v=l)
    {R : TangentSpace 𝓘(ℝ,Model n) b → TangentSpace 𝓘(ℝ,Model n) a}
    (hR : ContDiffAt ℝ ∞ R q) (hR0 : R q=0)
    (hRe : ∀ᶠ w in 𝓝 q,riemannianExp a (R w)=riemannianExp b w)
    (d : TangentSpace 𝓘(ℝ,Model n) b) :
    ‖d‖^2+fderiv ℝ (fderiv ℝ (fun w=>scalarCostSupport φ v a p s
      (riemannianExp b w))) q d d=
      fderiv ℝ (fderiv ℝ (fun h=>scalarCostSupport φ v a p s
        (riemannianExp a h))) 0 (fderiv ℝ R q d) (fderiv ℝ R q d)+
      hessianValue a (l • p) (fderiv ℝ R q d) := by
  let S := fun h:TangentSpace 𝓘(ℝ,Model n) a=>scalarCostSupport φ v a p s (riemannianExp a h)
  let C := normalCost a (l • p)
  have hc : ContDiffAt ℝ 2 C 0 :=
    (normalCost_contDiffAt hlp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨hsC,hsD,_⟩ := scalarCostSupport_normal_jet hs hp hφ hφd
  have hstat : fderiv ℝ (fun h=>S h+C h) 0=0 := by
    rw [fderiv_fun_add (hsC.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)),
      hsD.fderiv,(normalCost_hasFDerivAt_zero hlp).fderiv]
    simp only [map_neg,add_neg_cancel]
  have hR2 := hR.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcomp := second_fderiv_comp_stationary (f := fun h=>S h+C h)
    (hR0.symm ▸ hsC.add hc) hR2 (by rwa [hR0]) d d
  rw [hR0,second_fderiv_add_eq hsC hc] at hcomp
  rw [hessianValue_eq_normalHessian hlp]
  have he : (fun w=>S (R w)+C (R w))=ᶠ[𝓝 q]
      (fun w=>scalarCostSupport φ v a p s (riemannianExp b w)+‖w‖^2/2) := by
    filter_upwards [hRe,(isOpen_injectivityDomain b).mem_nhds hq] with w hw hwi
    dsimp only [S,C,normalCost]
    rw [hw,hab]
    congr 1
    change dist (riemannianExp b w) b^2/2=‖w‖^2/2
    rw [dist_comm,injectivityDomain_subset_minimizingVectors b hwi]
  have hsE : ContDiffAt ℝ 2 (fun w=>scalarCostSupport φ v a p s (riemannianExp b w)) q :=
    ((hR0.symm ▸ hsC).comp q hR2).congr_of_eventuallyEq
      (hRe.mono (fun w hw=>congrArg (scalarCostSupport φ v a p s) hw.symm))
  rw [he.fderiv.fderiv_eq,second_fderiv_add_eq hsE
    ((half_norm_sq_contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt),
    add_apply,add_apply,half_norm_sq_second_fderiv] at hcomp
  simpa only [innerSL_apply_apply,real_inner_self_eq_norm_sq,add_comm,S,C,normalHessian,add_apply] using hcomp

omit [Nonempty M] in
lemma exists_uniform_center_full_pullback :
    ∃ c>0,∀ᶠ l : ℝ in 𝓝 1, 0<l → l<1 → ∀ a b : M,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) a,
      ∀ q : TangentSpace 𝓘(ℝ,Model n) b,
      p∈minimizingVectors a → q∈injectivityDomain b →
      riemannianExp a (l • p)=b → riemannianExp b q=a →
      ∀ (φ : ℝ → ℝ) (v : ℝ), ContDiffAt ℝ 2 φ v → deriv φ v=l →
      ∀ d : TangentSpace 𝓘(ℝ,Model n) b,
        c*(1-l)*‖d‖^2+(iteratedDeriv 2 φ v/l^2)*(inner ℝ q d)^2≤
          ‖d‖^2+fderiv ℝ (fderiv ℝ (fun w=>scalarCostSupport φ v a p ((1+l)/2)
            (riemannianExp b w))) q d d := by
  obtain ⟨c,hc,H⟩ := exists_uniform_center_support_pullback (n := n) (M := M)
  refine ⟨c,hc,?_⟩
  filter_upwards [H] with l hl
  intro hl0 hl1 a b p q hp hq hab hba φ v hφ hφd d
  obtain ⟨R,hR,hR0,hRe,HR⟩ := hl hl1 a b p q hp hq hab hba φ v hφ hφd
  have hs : 0<(1+l)/2 := by linarith
  have hs1 : (1+l)/2<1 := by linarith
  rw [scalar_support_full_pullback_identity hs.ne'
    (contracted_minimizer_mem_injectivityDomain hp hs hs1)
    (contracted_minimizer_mem_injectivityDomain hp hl0 hl1) hq hab hφ hφd hR hR0 hRe]
  exact HR d

end CenterFullPullback
end WeakMTWTransport

end
end

end OAI
