import OAI.Geometry.Perimeter.Regularity.EllipticLinearStep
import OAI.Geometry.Perimeter.Regularity.EllipticSecant

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def WeakFluxEquation (V : Euc n → Euc n) (U : Set (Euc n)) : Prop :=
  ∀ φ : SmoothLocalTest U, (∫ x, inner ℝ (V x) (gradient φ.val x))=0

def translateLocalTest {U W : Set (Euc n)} (z : Euc n)
    (hz : ∀ x∈W, x+z∈U) (φ : SmoothLocalTest W) : SmoothLocalTest U := by
  let ψ : Euc n → ℝ := fun y ↦ φ.val (y-z)
  refine ⟨ψ,φ.property.1.comp (contDiff_id.sub contDiff_const),
    φ.property.2.1.comp_homeomorph (Homeomorph.subRight z),?_⟩
  intro y hy
  have hh := φ.property.2.2 (tsupport_comp_subset_preimage φ.val
    (continuous_id.sub continuous_const) hy)
  simpa only [sub_add_cancel] using hz (y-z) hh

 theorem gradient_translate {f : Euc n → ℝ} (hf : Differentiable ℝ f)
    (z x : Euc n) : gradient (fun y ↦ f (y+z)) x=gradient f (x+z) := by
  apply ext_inner_right ℝ
  intro y
  simp only [inner_gradient_left]
  have hh := ((hf (x+z)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const z)).fderiv
  simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L y) hh

 theorem WeakFluxEquation.translate {V : Euc n → Euc n} {U W : Set (Euc n)}
    (h : WeakFluxEquation V U) (z : Euc n) (hz : ∀ x∈W, x+z∈U) :
    WeakFluxEquation (fun x ↦ V (x+z)) W := by
  intro φ
  have hh := h (translateLocalTest z hz φ)
  have hg (x : Euc n) : gradient (translateLocalTest z hz φ).val (x+z)=gradient φ.val x := by
    have he : (translateLocalTest z hz φ).val=(fun y ↦ φ.val (y+(-z))) := by
      funext y; rfl
    rw [he,gradient_translate (φ.property.1.differentiable (by simp))]
    simp only [add_neg_cancel_right]
  rw [←integral_add_right_eq_self (fun x ↦ inner ℝ (V x)
    (gradient (translateLocalTest z hz φ).val x)) z] at hh
  simpa only [hg] using hh

 theorem WeakFluxEquation.sub {V W : Euc n → Euc n} {U : Set (Euc n)}
    (hV : Continuous V) (hW : Continuous W) (h : WeakFluxEquation V U)
    (h' : WeakFluxEquation W U) : WeakFluxEquation (fun x ↦ V x-W x) U := by
  intro φ
  simp_rw [inner_sub_left]
  rw [integral_sub (inner_gradient_pairing_integrable hV φ)
    (inner_gradient_pairing_integrable hW φ),h φ,h' φ,sub_self]

 theorem WeakFluxEquation.const_smul {V : Euc n → Euc n} {U : Set (Euc n)}
    (h : WeakFluxEquation V U) (c : ℝ) : WeakFluxEquation (fun x ↦ c•V x) U := by
  intro φ
  simp only [inner_smul_left,conj_trivial,integral_const_mul,h φ,mul_zero]

 def differenceQuotient (f : Euc n → ℝ) (e : Euc n) (h : ℝ) (x : Euc n) :=
  h⁻¹*(f (x+h•e)-f x)

 theorem differenceQuotient_contDiff {f : Euc n → ℝ} {k : ℕ∞}
    (hf : ContDiff ℝ k f) (e : Euc n) (h : ℝ) : ContDiff ℝ k (differenceQuotient f e h) :=
  contDiff_const.mul ((hf.comp (contDiff_id.add contDiff_const)).sub hf)

 theorem differenceQuotient_gradient {f : Euc n → ℝ} (hf : Differentiable ℝ f)
    (e : Euc n) (h : ℝ) (x : Euc n) :
    gradient (differenceQuotient f e h) x=h⁻¹•(gradient f (x+h•e)-gradient f x) := by
  apply ext_inner_right ℝ
  intro y
  simp only [inner_gradient_left,inner_smul_left,inner_sub_left,conj_trivial]
  have hd := ((((hf (x+h•e)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (h•e))).sub
    (hf x).hasFDerivAt).const_mul h⁻¹).fderiv
  change fderiv ℝ (fun y ↦ h⁻¹*(f (y+h•e)-f y)) x y = _
  simpa only [differenceQuotient,smul_apply,sub_apply,
    ContinuousLinearMap.comp_id,smul_eq_mul,Function.comp_def,id_eq,Pi.sub_apply] using congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L y) hd

 theorem differenceQuotient_tendsto {f : Euc n → ℝ} (hf : Differentiable ℝ f)
    (e x : Euc n) : Tendsto (fun h : ℝ ↦ differenceQuotient f e h x) (𝓝[≠] 0)
      (𝓝 (fderiv ℝ f x e)) := by
  have ht : HasDerivAt (fun h : ℝ ↦ x+h•e) e 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const e |>.const_add x)
  have hd : HasDerivAt (fun h : ℝ ↦ f (x+h•e)) (fderiv ℝ f x e) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ)•e) := by simpa using (hf x).hasFDerivAt
    have hh := hf'.comp_hasDerivAt (0:ℝ) ht
    simpa only [zero_smul,add_zero,Function.comp_def] using hh
  have he : (fun h : ℝ ↦ differenceQuotient f e h x) = _root_.slope (fun h : ℝ ↦ f (x+h•e)) 0 := by
    funext h
    simp only [_root_.slope,differenceQuotient,vsub_eq_sub,sub_zero,zero_smul,add_zero,smul_eq_mul]
  rw [he]
  exact hd.tendsto_slope

 theorem weak_nonlinear_difference {G : Euc n → Euc n} (hG : ContDiff ℝ 1 G)
    {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f) {U W : Set (Euc n)}
    (h : WeakFluxEquation (fun x ↦ G (gradient f x)) U) (hWU : W⊆U)
    (e : Euc n) (s : ℝ) (hs : ∀ x∈W, x+s•e∈U) :
    WeakLinearEquation (fun x ↦ derivativeSecant G (gradient f x) (gradient f (x+s•e)))
      (differenceQuotient f e s) (fun _ ↦ 0) W := by
  have hbase : WeakFluxEquation (fun x ↦ G (gradient f x)) W := by
    intro φ
    exact h ⟨φ.val,φ.property.1,φ.property.2.1,φ.property.2.2.trans hWU⟩
  have hcont := hG.continuous.comp (gradient_continuous_C1 hf)
  have hd := ((h.translate (s•e) hs).sub
    (hcont.comp (continuous_id.add continuous_const)) hcont hbase).const_smul s⁻¹
  intro φ
  have he (x : Euc n) : derivativeSecant G (gradient f x) (gradient f (x+s•e))
      (gradient (differenceQuotient f e s) x)=s⁻¹•(G (gradient f (x+s•e))-G (gradient f x)) := by
    rw [differenceQuotient_gradient (hf.differentiable (by simp)),map_smul,derivativeSecant_apply hG]
  simp only [he,inner_zero_left,integral_zero]
  exact hd φ

end RPISingularHarnack

end

end OAI
