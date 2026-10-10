import OAI.Analysis.LiebThirring.Main

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set
open scoped ComplexConjugate Topology

abbrev L2C := Lp ℂ 2 (volume : Measure ℝ)
abbrev ProductL2 := WithLp 2 (L2C × L2C)
abbrev TestFunction := {φ : ℝ → ℂ // ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ}

def testLp (φ : ℝ → ℂ) (hc : Continuous φ) (hs : HasCompactSupport φ) : L2C :=
  (hc.memLp_of_hasCompactSupport hs (p := 2)).toLp φ

lemma inner_star_testLp (φ : ℝ → ℂ) (hc : Continuous φ) (hs : HasCompactSupport φ)
    (f : L2C) : inner ℂ (testLp (star φ) hc.star (hs.comp_left (star_zero ℂ))) f = ∫ x, f x*φ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hc.star.memLp_of_hasCompactSupport (hs.comp_left (star_zero ℂ)) (p := 2)).coeFn_toLp] with x hx
  simp only [RCLike.inner_apply]
  change f x*star ((testLp (star φ) hc.star (hs.comp_left (star_zero ℂ))) x) = f x*φ x
  rw [show (testLp (star φ) hc.star (hs.comp_left (star_zero ℂ))) x = star (φ x) from hx,star_star]

def constraint (φ : TestFunction) : ProductL2 →L[ℂ] ℂ :=
  (innerSL ℂ (testLp (star (deriv φ.1))
    (φ.2.1.continuous_deriv (by simp)).star (φ.2.2.deriv.comp_left (star_zero ℂ)))).comp (WithLp.fstL 2 ℂ L2C L2C) +
  (innerSL ℂ (testLp (star φ.1) φ.2.1.continuous.star (φ.2.2.comp_left (star_zero ℂ)))).comp (WithLp.sndL 2 ℂ L2C L2C)

lemma constraint_eq (φ : TestFunction) (u : ProductL2) : constraint φ u =
    (∫ x, (WithLp.ofLp u).1 x * deriv φ.1 x) + (∫ x, (WithLp.ofLp u).2 x * φ.1 x) := by
  simp only [constraint,add_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,WithLp.fstL_apply,WithLp.sndL_apply]
  exact congrArg₂ (· + ·)
    (inner_star_testLp (deriv φ.1) (φ.2.1.continuous_deriv (by simp)) φ.2.2.deriv _)
    (inner_star_testLp φ.1 φ.2.1.continuous φ.2.2 _)

def h1Graph : Submodule ℂ ProductL2 := ⨅ φ : TestFunction, (constraint φ).ker

lemma mem_h1Graph_iff (u : ProductL2) : u ∈ h1Graph ↔ ∀ φ : TestFunction,
    (∫ x, (WithLp.ofLp u).1 x * deriv φ.1 x) = -(∫ x, (WithLp.ofLp u).2 x * φ.1 x) := by
  simp only [h1Graph,Submodule.mem_iInf,LinearMap.mem_ker,ContinuousLinearMap.coe_coe,constraint_eq,
    add_eq_zero_iff_eq_neg]

lemma h1Graph_closed : IsClosed (h1Graph : Set ProductL2) := by
  rw [h1Graph,Submodule.coe_iInf]
  exact isClosed_iInter (fun φ ↦ (constraint φ).isClosed_ker)

abbrev H1C := ↥h1Graph
instance : CompleteSpace H1C := h1Graph_closed.completeSpace_coe

def valL : H1C →L[ℂ] L2C := (WithLp.fstL 2 ℂ L2C L2C).comp h1Graph.subtypeL
def gradL : H1C →L[ℂ] L2C := (WithLp.sndL 2 ℂ L2C L2C).comp h1Graph.subtypeL

def toH1 (u : H1C) : H1 where
  val := valL u
  grad := gradL u
  val_memLp := Lp.memLp _
  grad_memLp := Lp.memLp _
  weak_derivative φ hc hs := (mem_h1Graph_iff u.1).mp u.2 ⟨φ,hc,hs⟩

def ofH1 (u : H1) : H1C := ⟨WithLp.toLp 2 (u.val_memLp.toLp u.val,u.grad_memLp.toLp u.grad),by
  rw [mem_h1Graph_iff]
  intro φ
  convert u.weak_derivative φ.1 φ.2.1 φ.2.2 using 1
  · exact integral_congr_ae (u.val_memLp.coeFn_toLp.mono (fun x hx ↦ by simp [hx]))
  · congr 1
    exact integral_congr_ae (u.grad_memLp.coeFn_toLp.mono (fun x hx ↦ by simp [hx]))⟩

@[simp] lemma valL_ofH1 (u : H1) : valL (ofH1 u) = u.val_memLp.toLp u.val := rfl
@[simp] lemma gradL_ofH1 (u : H1) : gradL (ofH1 u) = u.grad_memLp.toLp u.grad := rfl

lemma valL_injective : Function.Injective valL := by
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro u hu
  have hv : valL u = 0 := hu
  have hg : (fun x ↦ gradL u x) =ᵐ[volume] (0 : ℝ → ℂ) := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero ((Lp.memLp (gradL u)).locallyIntegrable (by norm_num))
    intro φ hc hs
    have h := (toH1 u).weak_derivative (fun x ↦ (φ x : ℂ))
      (Complex.ofRealCLM.contDiff.comp hc) (hs.comp_left Complex.ofReal_zero)
    have hi : (∫ x, (toH1 u).val x*deriv (fun x ↦ (φ x : ℂ)) x) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
      change valL u x*_ = 0
      rw [hv,hx]
      simp
    rw [hi,eq_neg_iff_add_eq_zero,zero_add] at h
    simpa [toH1,Complex.real_smul,mul_comm] using h
  have hgz : gradL u = 0 := Lp.ext (hg.trans (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)).symm)
  apply (Submodule.mem_bot ℂ).mpr
  apply Subtype.ext
  apply (WithLp.equiv 2 (L2C × L2C)).injective
  apply Prod.ext
  · exact hv
  · exact hgz


lemma valL_dense : Dense (Set.range valL) := by
  have hd := Lp.dense_hasCompactSupport_contDiff (E := ℝ) (F := ℂ)
    (μ := volume) (p := 2) (by norm_num)
  apply hd.mono
  rintro f ⟨g,hfg,hgc,hgd⟩
  let u : H1 := SobolevProof.smoothH1 g (deriv g) hgd
    (fun x ↦ (hgd.differentiable (by simp) x).hasDerivAt)
    (hgd.continuous_deriv (by simp))
    (hgd.continuous.memLp_of_hasCompactSupport hgc)
    ((hgd.continuous_deriv (by simp)).memLp_of_hasCompactSupport hgc.deriv)
  refine ⟨ofH1 u,?_⟩
  apply Lp.ext
  exact u.val_memLp.coeFn_toLp.trans hfg.symm

@[simp] lemma toLp_toH1 (u : H1C) : (toH1 u).val_memLp.toLp (toH1 u).val = valL u :=
  Lp.toLp_coeFn _ _
@[simp] lemma grad_toLp_toH1 (u : H1C) : (toH1 u).grad_memLp.toLp (toH1 u).grad = gradL u :=
  Lp.toLp_coeFn _ _

lemma l2Pairing_eq_inner (u v : H1) :
    l2Pairing u v = inner ℂ (u.val_memLp.toLp u.val) (v.val_memLp.toLp v.val) := by
  rw [l2Pairing,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [u.val_memLp.coeFn_toLp,v.val_memLp.coeFn_toLp] with x hx hy
  rw [hx,hy,RCLike.inner_apply,mul_comm]
  rfl

lemma gradPairing_eq_inner (u v : H1) :
    (∫ x, star (u.grad x)*v.grad x) = inner ℂ (u.grad_memLp.toLp u.grad) (v.grad_memLp.toLp v.grad) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [u.grad_memLp.coeFn_toLp,v.grad_memLp.coeFn_toLp] with x hx hy
  rw [hx,hy,RCLike.inner_apply,mul_comm]
  rfl

end SharpLiebThirring.OperatorProof

end

end OAI
