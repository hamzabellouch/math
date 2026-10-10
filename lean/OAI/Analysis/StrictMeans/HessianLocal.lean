import OAI.Analysis.StrictMeans.QuadraticHomotopy

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma complex_real_decomposition (z : ℂ) : z.re • (1:ℂ)+z.im • Complex.I=z := by
  apply Complex.ext <;> simp

lemma realCLM_apply (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z=z.re*L 1+z.im*L Complex.I := by
  conv_lhs => rw [← complex_real_decomposition z]
  simp only [map_add,map_smul,smul_eq_mul]

lemma realCLM_eq_zero {L : ℂ →L[ℝ] ℝ} (hx : L 1=0) (hy : L Complex.I=0) : L=0 := by
  ext z
  simp [realCLM_apply L z,hx,hy]

def planeCLM (a b : ℝ) : ℂ →L[ℝ] ℝ := a•Complex.reCLM+b•Complex.imCLM

@[simp] lemma planeCLM_apply (a b : ℝ) (z : ℂ) : planeCLM a b z=a*z.re+b*z.im := by
  simp [planeCLM]

def hessianCLM (a b c : ℝ) : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  Complex.reCLM.smulRight (planeCLM a b)+Complex.imCLM.smulRight (planeCLM b c)

lemma hessianCLM_apply (a b c : ℝ) (z w : ℂ) :
    hessianCLM a b c z w=(a*z.re+b*z.im)*w.re+(b*z.re+c*z.im)*w.im := by
  simp [hessianCLM]
  ring

lemma hessianCLM_injective {a b c : ℝ} (hD : a*c-b^2≠0) : Injective (hessianCLM a b c) := by
  apply (hessianCLM a b c).toLinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  change hessianCLM a b c z=0 at hz
  have hx := congrArg (fun L : ℂ →L[ℝ] ℝ =>L 1) hz
  have hy := congrArg (fun L : ℂ →L[ℝ] ℝ =>L Complex.I) hz
  simp only [hessianCLM_apply,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,
    mul_one,mul_zero,zero_add,add_zero,zero_apply] at hx hy
  have hxr : z.re=0 := (mul_eq_zero.mp (show (a*c-b^2)*z.re=0 by linear_combination c*hx-b*hy)).resolve_left hD
  have hyr : z.im=0 := (mul_eq_zero.mp (show (a*c-b^2)*z.im=0 by linear_combination a*hy-b*hx)).resolve_left hD
  exact Complex.ext (by simpa using hxr) (by simpa using hyr)

lemma injectiveCLM_lower_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : E →L[ℝ] F} (hL : Injective L) : ∃ m : ℝ, 0 < m ∧ ∀ z, m*‖z‖≤‖L z‖ := by
  obtain ⟨K,hK,hBound⟩ := L.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hL)
  have hKr : (0:ℝ)<K := hK
  refine ⟨(K:ℝ)⁻¹,inv_pos.mpr hKr,fun z=>?_⟩
  have h := ZeroHomClass.bound_of_antilipschitz L hBound z
  rw [inv_mul_le_iff₀ hKr]
  exact h

lemma hessianCLM_of_second {u : ℂ → ℝ} {p : ℂ} (hu : ContDiffAt ℝ 2 u p) :
    fderiv ℝ (fderiv ℝ u) p =
      hessianCLM (fderiv ℝ (fderiv ℝ u) p 1 1)
        (fderiv ℝ (fderiv ℝ u) p 1 Complex.I)
        (fderiv ℝ (fderiv ℝ u) p Complex.I Complex.I) := by
  let L := fderiv ℝ (fderiv ℝ u) p
  have hsym := (hu.isSymmSndFDerivAt (by norm_num)).eq 1 Complex.I
  change L 1 Complex.I=L Complex.I 1 at hsym
  ext z w
  rw [hessianCLM_apply,realCLM_apply (L z) w]
  have he : L z=z.re•L 1+z.im•L Complex.I := by
    conv_lhs => rw [← complex_real_decomposition z]
    simp only [map_add,map_smul]
  rw [he]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rw [← hsym]
  ring

lemma quadratic_contDiff (a b c : ℝ) : ContDiff ℝ ⊤ (quadratic a b c) := by
  have hr := Complex.reCLM.contDiff (n := (⊤ : WithTop ℕ∞))
  have hi := Complex.imCLM.contDiff (n := (⊤ : WithTop ℕ∞))
  exact (((contDiff_const.mul (hr.pow 2)).add (((contDiff_const.mul hr).mul hi))).add
    (contDiff_const.mul (hi.pow 2))).div_const 2

lemma quadratic_fderiv (a b c : ℝ) (z : ℂ) :
    fderiv ℝ (quadratic a b c) z=hessianCLM a b c z := by
  have hr := quadraticFamily_dx (A:=fun _=>a) (B:=fun _=>b) (C:=fun _=>c) (p:=0)
    (q:=(0,z)) ((quadraticFamily_contDiff contDiff_const contDiff_const contDiff_const 0).differentiable (by norm_num : (1 : WithTop ℕ∞)≠0) (0,z))
  have hi := quadraticFamily_dy (A:=fun _=>a) (B:=fun _=>b) (C:=fun _=>c) (p:=0)
    (q:=(0,z)) ((quadraticFamily_contDiff contDiff_const contDiff_const contDiff_const 0).differentiable (by norm_num : (1 : WithTop ℕ∞)≠0) (0,z))
  have he : quadraticFamily (fun _=>a) (fun _=>b) (fun _=>c) 0 = quadratic a b c ∘ Prod.snd := by
    funext q; simp [quadraticFamily]
  have hf : HasFDerivAt (quadratic a b c ∘ Prod.snd)
      ((fderiv ℝ (quadratic a b c) z).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)) ((0:ℝ),z) :=
    ((quadratic_contDiff a b c).differentiable (by simp) z).hasFDerivAt.comp ((0:ℝ),z)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0:ℝ),z)))
  rw [he,hf.fderiv] at hr hi
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',sub_zero] at hr hi
  ext w
  rw [realCLM_apply _ w,hr,hi,hessianCLM_apply]
  ring

def affinePotential (u v : ℂ → ℝ) (q : ℝ × ℂ) : ℝ := (1-q.1)*u q.2+q.1*v q.2

lemma affinePotential_contDiffAt {u v : ℂ → ℝ} {q : ℝ × ℂ}
    (hu : ContDiffAt ℝ 1 u q.2) (hv : ContDiffAt ℝ 1 v q.2) :
    ContDiffAt ℝ 1 (affinePotential u v) q := by
  exact (((contDiffAt_const.sub contDiffAt_fst).mul (hu.comp q contDiffAt_snd)).add
    (contDiffAt_fst.mul (hv.comp q contDiffAt_snd)))

lemma affinePotential_spatial {u v : ℂ → ℝ} {q : ℝ × ℂ}
    (hu : DifferentiableAt ℝ u q.2) (hv : DifferentiableAt ℝ v q.2) (d : ℂ) :
    fderiv ℝ (affinePotential u v) q (0,d)=
      (1-q.1)*fderiv ℝ u q.2 d+q.1*fderiv ℝ v q.2 d := by
  have hU := hu.hasFDerivAt.comp q hasFDerivAt_snd
  have hV := hv.hasFDerivAt.comp q hasFDerivAt_snd
  have hT := hasFDerivAt_fst (𝕜 := ℝ) (p := q)
  have hd := ((hasFDerivAt_const (1:ℝ) q).sub hT).mul hU |>.add (hT.mul hV)
  change fderiv ℝ (((fun _ : ℝ × ℂ => (1:ℝ))-Prod.fst) * (u ∘ Prod.snd) +
    (Prod.fst * (v ∘ Prod.snd))) q (0,d) = _
  rw [hd.fderiv]
  simp

lemma local_quadratic_homotopy_regular {u : ℂ → ℝ} {p : ℂ}
    (hu : ContDiffAt ℝ 2 u p) (hp : fderiv ℝ u p=0)
    (hD : (fderiv ℝ (fderiv ℝ u) p 1 1)*
      (fderiv ℝ (fderiv ℝ u) p Complex.I Complex.I)-
      (fderiv ℝ (fderiv ℝ u) p 1 Complex.I)^2≠0) :
    let a := fderiv ℝ (fderiv ℝ u) p 1 1
    let b := fderiv ℝ (fderiv ℝ u) p 1 Complex.I
    let c := fderiv ℝ (fderiv ℝ u) p Complex.I Complex.I
    ∀ᶠ z in 𝓝 p, z≠p → ∀ t∈Icc (0:ℝ) 1,
      ∃ L : (ℝ × ℂ) →L[ℝ] ℝ,
        HasStrictFDerivAt (affinePotential u (fun w=>quadratic a b c (w-p))) L (t,z) ∧
          (L (0,1)≠0 ∨ L (0,Complex.I)≠0) := by
  dsimp only
  let a := fderiv ℝ (fderiv ℝ u) p 1 1
  let b := fderiv ℝ (fderiv ℝ u) p 1 Complex.I
  let c := fderiv ℝ (fderiv ℝ u) p Complex.I Complex.I
  obtain ⟨m,hm,hH⟩ := injectiveCLM_lower_bound (hessianCLM_injective hD)
  have hg : HasFDerivAt (fderiv ℝ u) (hessianCLM a b c) p := by
    rw [← hessianCLM_of_second hu]
    exact (hu.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero |>.hasFDerivAt
  have hreg := derivative_homotopy_regular hg hp hm hH
  have hQ : ContDiff ℝ 1 (fun w=>quadratic a b c (w-p)) :=
    (quadratic_contDiff a b c).of_le (by simp) |>.comp (contDiff_id.sub contDiff_const)
  have hQd (z : ℂ) : fderiv ℝ (fun w=>quadratic a b c (w-p)) z=hessianCLM a b c (z-p) := by
    have he := ((quadratic_contDiff a b c).differentiable (by simp) (z-p)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub_const p)
    change fderiv ℝ (quadratic a b c ∘ fun x => id x-p) z = _
    rw [he.fderiv,quadratic_fderiv]
    ext d; simp
  filter_upwards [hreg,(hu.of_le (by norm_num : (1 : WithTop ℕ∞)≤2)).eventually (by norm_num)] with z hz hzu
  intro hzp t ht
  have hd := affinePotential_contDiffAt hzu hQ.contDiffAt (q := (t,z))
  refine ⟨_,hd.hasStrictFDerivAt one_ne_zero,?_⟩
  rw [affinePotential_spatial (hzu.differentiableAt one_ne_zero) (hQ.differentiable one_ne_zero z),
    affinePotential_spatial (hzu.differentiableAt one_ne_zero) (hQ.differentiable one_ne_zero z),hQd]
  by_contra hn
  obtain ⟨hx,hy⟩ := not_or.mp hn
  simp only [not_not] at hx hy
  apply hz hzp t ht
  exact realCLM_eq_zero hx hy

end
end StrictInverseFirstPower.Grid

end

end OAI
