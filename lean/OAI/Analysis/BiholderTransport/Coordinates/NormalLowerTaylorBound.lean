import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.UniformReverseGain
import OAI.Analysis.BiholderTransport.Contact.CenterSupport

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

lemma reverse_normal_pairing {a b : M}
    {p : TangentSpace 𝓘(ℝ,Model n) a} {q : TangentSpace 𝓘(ℝ,Model n) b}
    (hp : p∈injectivityDomain a) (hq : q∈injectivityDomain b)
    (hpq : riemannianExp a p=b)
    {R : TangentSpace 𝓘(ℝ,Model n) b → TangentSpace 𝓘(ℝ,Model n) a}
    (hR : DifferentiableAt ℝ R q) (hR0 : R q=0)
    (hRe : ∀ᶠ w in 𝓝 q,riemannianExp a (R w)=riemannianExp b w)
    (w : TangentSpace 𝓘(ℝ,Model n) b) :
    inner ℝ p (fderiv ℝ R q w)=-inner ℝ q w := by
  have heq : (fun v => normalCost a p (R v)) =ᶠ[𝓝 q] (fun v => ‖v‖^2/2) := by
    filter_upwards [hRe,(isOpen_injectivityDomain b).mem_nhds hq] with v hv hvreg
    dsimp only [normalCost]
    rw [hv,hpq]
    change dist (riemannianExp b v) b^2/2=‖v‖^2/2
    rw [dist_comm,injectivityDomain_subset_minimizingVectors b hvreg]
  have hg : HasFDerivAt (normalCost a p) (innerSL ℝ (-p)) (R q) := by
    rw [hR0]; exact normalCost_hasFDerivAt_zero hp
  have hh : HasFDerivAt (fun v : TangentSpace 𝓘(ℝ,Model n) b => ‖v‖^2/2)
      (innerSL ℝ q) q := by
    convert! ((hasStrictFDerivAt_norm_sq q).hasFDerivAt.const_mul (1/2:ℝ)) using 1
    · ext v; ring
    · ext v
      simp only [smul_apply,smul_eq_mul]
      ring
  have H : (innerSL ℝ (-p)).comp (fderiv ℝ R q)=innerSL ℝ q :=
    ((hg.comp q hR.hasFDerivAt).congr_of_eventuallyEq heq.symm).unique hh
  have HV := congrArg (fun A => A w) H
  simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,inner_neg_left] at HV
  linarith only [HV]

lemma exists_uniform_center_support_pullback :
    ∃ c>0,∀ᶠ l : ℝ in 𝓝 1, l<1 → ∀ a b : M,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) a,
      ∀ q : TangentSpace 𝓘(ℝ,Model n) b,
      p∈minimizingVectors a → q∈injectivityDomain b →
      riemannianExp a (l • p)=b → riemannianExp b q=a →
      ∀ (φ : ℝ → ℝ) (v : ℝ), ContDiffAt ℝ 2 φ v → deriv φ v=l →
      ∃ R : TangentSpace 𝓘(ℝ,Model n) b → TangentSpace 𝓘(ℝ,Model n) a,
        ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
        (∀ᶠ w in 𝓝 q,riemannianExp a (R w)=riemannianExp b w) ∧
        ∀ w : TangentSpace 𝓘(ℝ,Model n) b,
          c*(1-l)*‖w‖^2+(iteratedDeriv 2 φ v/l^2)*(inner ℝ q w)^2 ≤
            fderiv ℝ (fderiv ℝ (fun h =>
              scalarCostSupport φ v a p ((1+l)/2) (riemannianExp a h))) 0
              (fderiv ℝ R q w) (fderiv ℝ R q w)+
            hessianValue a (l • p) (fderiv ℝ R q w) := by
  obtain ⟨c,hc,H⟩ := exists_uniform_reverse_divided_gain (n := n) (M := M)
  have hpair : Tendsto (fun l : ℝ => (l,(1+l)/2)) (𝓝 1) (𝓝 (1,1)) := by
    have hc : ContinuousAt (fun l : ℝ => (l,(1+l)/2)) (1:ℝ) :=
      continuousAt_id.prodMk ((continuousAt_const.add continuousAt_id).div_const 2)
    simpa using hc.tendsto
  refine ⟨c/4,by positivity,?_⟩
  filter_upwards [hpair.eventually H,eventually_gt_nhds (by norm_num : (1/2:ℝ)<1)] with l hl hhalf
  intro hl1 a b p q hp hq hpb hqa φ v hφ hφd
  have hl0 : 0<l := by linarith only [hhalf]
  have hs0 : 0<(1+l)/2 := by positivity
  have hs1 : (1+l)/2<1 := by linarith only [hl1]
  have hls : l≤(1+l)/2 := by linarith only [hl1]
  have hpl := contracted_minimizer_mem_injectivityDomain hp hl0 hl1
  have hps := contracted_minimizer_mem_injectivityDomain hp hs0 hs1
  obtain ⟨R,hR,hR0,hRe,HR⟩ := hl hls hs1 a b p q hp hq hpb hqa
  refine ⟨R,hR,hR0,hRe,?_⟩
  intro w
  obtain ⟨_,_,HJ⟩ := scalarCostSupport_normal_jet hs0.ne' hps hφ hφd
  rw [HJ]
  have HP := reverse_normal_pairing hpl hq hpb
    (hR.differentiableAt (by simp)) hR0 hRe w
  rw [real_inner_smul_left] at HP
  have HIP : (inner ℝ p (fderiv ℝ R q w))^2=(inner ℝ q w)^2/l^2 := by
    have he : inner ℝ p (fderiv ℝ R q w)=-(inner ℝ q w)/l := by
      apply (eq_div_iff hl0.ne').mpr
      nlinarith only [HP]
    rw [he,div_pow,neg_sq]
  rw [HIP]
  have HD := mul_le_mul_of_nonneg_left (HR w) hl0.le
  have HA : l*(hessianValue a (l • p) (fderiv ℝ R q w)/l-
      hessianValue a (((1+l)/2) • p) (fderiv ℝ R q w)/((1+l)/2))=
      hessianValue a (l • p) (fderiv ℝ R q w)-
        (l/((1+l)/2))*hessianValue a (((1+l)/2) • p) (fderiv ℝ R q w) := by
    field_simp
  rw [HA] at HD
  have HG : (c/4)*(1-l)*‖w‖^2≤l*(c*((1+l)/2-l)*‖w‖^2) := by
    nlinarith only [mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hl1.le)) (sq_nonneg ‖w‖),
      mul_nonneg (sub_nonneg.mpr (le_of_lt hhalf))
        (mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hl1.le)) (sq_nonneg ‖w‖))]
  calc
    _ ≤ l*(c*((1+l)/2-l)*‖w‖^2)+(iteratedDeriv 2 φ v/l^2)*(inner ℝ q w)^2 := by linarith only [HG]
    _ ≤ (hessianValue a (l • p) (fderiv ℝ R q w)-
        (l/((1+l)/2))*hessianValue a (((1+l)/2) • p) (fderiv ℝ R q w))+
        (iteratedDeriv 2 φ v/l^2)*(inner ℝ q w)^2 := by linarith only [HD]
    _ = _ := by ring

end WeakMTWTransport

end

end OAI
