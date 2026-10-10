import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section WeakDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]

def IsWeakDerivative (v : E) (f g : E → ℂ) : Prop :=
  ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, f x * Complex.ofReal (lineDeriv ℝ φ x v)) = -(∫ x, g x * (φ x : ℂ))

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma IsWeakDerivative.congr_ae {v : E} {f f' g g' : E → ℂ}
    (h : IsWeakDerivative v f g) (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    IsWeakDerivative v f' g' := by
  intro φ hφ hcφ
  rw [← integral_congr_ae (hf.mono fun x hx => congrArg (· * _) hx),
    ← integral_congr_ae (hg.mono fun x hx => congrArg (· * _) hx)]
  exact h φ hφ hcφ

variable [IsLocallyFiniteMeasure (volume : Measure E)]

lemma IsWeakDerivative.unique {v : E} {f g g' : E → ℂ}
    (h : IsWeakDerivative v f g) (h' : IsWeakDerivative v f g')
    (hg : MemLp g 2) (hg' : MemLp g' 2) : g =ᵐ[volume] g' := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (hg.locallyIntegrable (by norm_num)) (hg'.locallyIntegrable (by norm_num))
  intro φ hφ hcφ
  have hh := neg_injective ((h φ hφ hcφ).symm.trans (h' φ hφ hcφ))
  simpa only [Complex.real_smul, mul_comm] using hh

def l2Test (φ : E → ℝ) (hφ : MemLp (fun x => (φ x : ℂ)) 2) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] ℂ :=
  innerSL ℂ (hφ.toLp (fun x => (φ x : ℂ)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)] in
lemma l2Test_apply (φ : E → ℝ) (hφ : MemLp (fun x => (φ x : ℂ)) 2)
    (f : Lp ℂ 2 (volume : Measure E)) :
    l2Test φ hφ f = ∫ x, f x * (φ x : ℂ) := by
  change ⟪hφ.toLp (fun x => (φ x : ℂ)), f⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, Complex.conj_ofReal]

lemma test_memLp {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    MemLp (fun x => (φ x : ℂ)) 2 :=
  (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
    (hcφ.comp_left (by simp))

lemma test_deriv_memLp {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (v : E) :
    MemLp (fun x => Complex.ofReal (lineDeriv ℝ φ x v)) 2 := by
  have hEq : (fun x => lineDeriv ℝ φ x v) = fun x => fderiv ℝ φ x v := by
    funext x
    exact (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv
  change MemLp (Complex.ofReal ∘ (fun x => lineDeriv ℝ φ x v)) 2
  rw [hEq]
  exact (Complex.continuous_ofReal.comp
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    ).memLp_of_hasCompactSupport
      (((hcφ.fderiv ℝ).comp_left (g := fun A : E →L[ℝ] ℝ => A v) (by simp)
        ).comp_left (by simp))

variable {ι : Type*} [Fintype ι]

abbrev WeakGraphAmbient (E : Type*) [NormedAddCommGroup E] [MeasureSpace E] (ι : Type*) :=
  PiLp 2 (fun _ : Option ι => Lp ℂ 2 (volume : Measure E))

def weakGraphTest (v : ι → E) (i : ι) (φ : E → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    WeakGraphAmbient E ι →L[ℂ] ℂ :=
  (l2Test (fun x => lineDeriv ℝ φ x (v i)) (test_deriv_memLp hφ hcφ (v i))).comp
      (PiLp.proj 2 (fun _ : Option ι => Lp ℂ 2 (volume : Measure E)) none) +
    (l2Test φ (test_memLp hφ hcφ)).comp
      (PiLp.proj 2 (fun _ : Option ι => Lp ℂ 2 (volume : Measure E)) (some i))

def weakGraph (v : ι → E) : Submodule ℂ (WeakGraphAmbient E ι) :=
  ⨅ (i : ι) (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ),
    (weakGraphTest v i φ hφ hcφ).ker

omit [Fintype ι] in
lemma mem_weakGraph (v : ι → E) (F : WeakGraphAmbient E ι) :
    F ∈ weakGraph v ↔ ∀ i, IsWeakDerivative (v i) (F none) (F (some i)) := by
  simp [weakGraph, weakGraphTest, l2Test_apply, IsWeakDerivative, eq_neg_iff_add_eq_zero]

omit [Fintype ι] in
lemma weakGraph_isClosed (v : ι → E) : IsClosed (weakGraph v : Set (WeakGraphAmbient E ι)) := by
  simp only [weakGraph, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun φ => isClosed_iInter fun hφ =>
    isClosed_iInter fun hcφ => (weakGraphTest v i φ hφ hcφ).isClosed_ker

instance weakGraph_completeSpace (v : ι → E) : CompleteSpace (weakGraph v) :=
  (weakGraph_isClosed v).completeSpace_coe

def weakGraphValue (v : ι → E) : weakGraph v →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (PiLp.proj 2 (fun _ : Option ι => Lp ℂ 2 (volume : Measure E)) none).comp
    (weakGraph v).subtypeL

omit [Fintype ι] in
lemma weakGraphValue_injective (v : ι → E) : Function.Injective (weakGraphValue v) := by
  intro F G hFG
  apply Subtype.ext
  apply PiLp.ext
  intro j
  cases j with
  | none => exact hFG
  | some i =>
    have hF := (mem_weakGraph v F).mp F.property i
    have hG := (mem_weakGraph v G).mp G.property i
    have hv : (F.val none : E → ℂ) =ᵐ[volume] (G.val none : E → ℂ) := by
      change F.val none = G.val none at hFG
      rw [hFG]
    have hF' := hF.congr_ae hv (EventuallyEq.refl _ _)
    exact Lp.ext (hF'.unique hG (Lp.memLp _) (Lp.memLp _))

end WeakDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smooth_derivative_continuous {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (v : E) :
    Continuous (fun x => fderiv ℝ f x v) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

lemma compact_derivative {f : E → ℂ} (hf : HasCompactSupport f) (v : E) :
    HasCompactSupport (fun x => fderiv ℝ f x v) :=
  (hf.fderiv ℝ).comp_left (g := fun A : E →L[ℝ] ℂ => A v) (by rfl)

lemma smooth_complex_ofReal_derivative {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v : E) :
    fderiv ℝ (fun y => (φ y : ℂ)) x v = Complex.ofReal (lineDeriv ℝ φ x v) := by
  rw [(hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
  have h := Complex.ofRealCLM.hasFDerivAt.comp x ((hφ.differentiable (by simp) x).hasFDerivAt)
  exact congrArg (fun A : E →L[ℝ] ℂ => A v) h.fderiv

omit [NormedSpace ℝ E] in
lemma compact_norm_sq {f : E → ℂ} (hcf : HasCompactSupport f) :
    HasCompactSupport (fun x => ‖f x‖ ^ (2 : ℕ)) := by
  apply hcf.comp_left (g := fun z : ℂ => ‖z‖ ^ (2 : ℕ))
  simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

lemma smooth_weak_gradient {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (v : E) :
    (∫ x, f x * Complex.ofReal (lineDeriv ℝ φ x v)) =
      -(∫ x, fderiv ℝ f x v * (φ x : ℂ)) := by
  let g : E → ℂ := fun x => (φ x : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hφ
  have hcg : HasCompactSupport g := hcφ.comp_left (g := Complex.ofReal) (by rfl)
  have hdf := smooth_derivative_continuous hf v
  have hdg := smooth_derivative_continuous hg v
  have hdfg : Integrable (fun x => fderiv ℝ f x v * g x) :=
    (hdf.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left
  have hfdg : Integrable (fun x => f x * fderiv ℝ g x v) :=
    (hf.continuous.mul hdg).integrable_of_hasCompactSupport hcf.mul_right
  have hfg : Integrable (fun x => f x * g x) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcf.mul_right
  simpa only [g, smooth_complex_ofReal_derivative hφ] using
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hdfg hfdg hfg
      (fun x _ => hf.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x)

variable {ι : Type*} [Fintype ι]

def smoothGraph (v : ι → E) {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : weakGraph v := by
  have hm : MemLp f 2 := hf.continuous.memLp_of_hasCompactSupport hc
  have hd (i : ι) : MemLp (fun x => fderiv ℝ f x (v i)) 2 :=
    (smooth_derivative_continuous hf _).memLp_of_hasCompactSupport (compact_derivative hc _)
  let F : WeakGraphAmbient E ι := WithLp.toLp 2 fun j =>
    match j with
    | none => hm.toLp f
    | some i => (hd i).toLp _
  refine ⟨F, (mem_weakGraph v F).mpr ?_⟩
  intro i
  have hw : IsWeakDerivative (v i) f (fun x => fderiv ℝ f x (v i)) :=
    fun φ hφ hcφ => smooth_weak_gradient hf hc hφ hcφ (v i)
  exact hw.congr_ae hm.coeFn_toLp.symm (hd i).coeFn_toLp.symm

omit [Fintype ι] in
lemma weakGraphValue_smoothGraph (v : ι → E) {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    weakGraphValue v (smoothGraph v hf hc) =
      (hf.continuous.memLp_of_hasCompactSupport (p := 2) hc).toLp f := rfl

omit [Fintype ι] in
lemma orthogonal_weakGraphValue_zero (v : ι → E)
    (f : Lp ℂ 2 (volume : Measure E)) (hf : f ∈ (weakGraphValue v).rangeᗮ) : f = 0 := by
  have hzero : (f : E → ℂ) =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((Lp.memLp f).locallyIntegrable (by norm_num))
    intro φ hφ hcφ
    let φc : E → ℂ := fun x => (φ x : ℂ)
    have hφc : ContDiff ℝ ∞ φc := Complex.ofRealCLM.contDiff.comp hφ
    have hcφc : HasCompactSupport φc := hcφ.comp_left (g := Complex.ofReal) (by rfl)
    have hw : ⟪weakGraphValue v (smoothGraph v hφc hcφc), f⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal _ _).mp hf _ ⟨smoothGraph v hφc hcφc, rfl⟩
    rw [weakGraphValue_smoothGraph] at hw
    have heq := l2Test_apply φ (test_memLp hφ hcφ) f
    change ⟪(test_memLp hφ hcφ).toLp φc, f⟫_ℂ = _ at heq
    rw [heq] at hw
    simpa only [Complex.real_smul, mul_comm] using hw
  exact Lp.ext (hzero.trans (Lp.coeFn_zero ℂ 2 volume).symm)

omit [Fintype ι] in

theorem weakGraphValue_denseRange (v : ι → E) : DenseRange (weakGraphValue v) := by
  have horth : (weakGraphValue v).rangeᗮ = ⊥ :=
    ((weakGraphValue v).rangeᗮ.eq_bot_iff).mpr (orthogonal_weakGraphValue_zero v)
  change Dense ((weakGraphValue v).range : Set (Lp ℂ 2 (volume : Measure E)))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← Submodule.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]

end CoulombAtom

end

end OAI
