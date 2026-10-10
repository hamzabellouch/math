import OAI.Geometry.SurfaceImmersion.Correction.SmoothParameterIntegral

namespace OAI

/-! Exact smooth division by a real coordinate vanishing at one point. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def smoothZeroFactor (f : ℝ → V) (p t : ℝ) : V :=
  ∫ s in (0:ℝ)..1, deriv f (p+s*(t-p))

lemma smoothZeroFactor_smooth {f : ℝ → V} (hf : ContDiff ℝ ∞ f) (p : ℝ) :
    ContDiff ℝ ∞ (smoothZeroFactor f p) := by
  have hD : ContDiff ℝ ∞ (deriv f) := hf.deriv'
  have hF : ContDiff ℝ ∞ (fun z : ℝ × ℝ => deriv f (p+z.2*(z.1-p))) :=
    hD.comp (contDiff_const.add (contDiff_snd.mul (contDiff_fst.sub contDiff_const)))
  exact SmoothParameterIntegral.contDiff_integral hF 0 1

lemma smoothZeroFactor_identity {f : ℝ → V} (hf : ContDiff ℝ ∞ f) (p t : ℝ) :
    (t-p) • smoothZeroFactor f p t = f t-f p := by
  have hD : Continuous (deriv f) := (hf.deriv' (n := ∞)).continuous
  have hcont : Continuous (fun s : ℝ => (t-p) • deriv f (p+s*(t-p))) := by fun_prop
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => f (p+s*(t-p)))
      ((t-p) • deriv f (p+s*(t-p))) s := by
    simpa [Function.comp_def] using ((hf.differentiable (by simp) _).hasDerivAt).scomp s
      (((hasDerivAt_id s).mul_const (t-p)).const_add p)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hcont.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_smul] at hi
  simpa only [smoothZeroFactor,zero_mul,add_zero,one_mul,add_sub_cancel] using hi

lemma smoothZeroFactor_self (f : ℝ → V) (p : ℝ) :
    smoothZeroFactor f p p = deriv f p := by
  simp [smoothZeroFactor]

/-- Division by two distinct simple-zero coordinates is globally smooth. -/
theorem two_zero_smooth_factor {f : ℝ → V} (hf : ContDiff ℝ ∞ f)
    {p q : ℝ} (hpq : p ≠ q) (hp : f p = 0) (hq : f q = 0) :
    ∃ d : ℝ → V, ContDiff ℝ ∞ d ∧
      (∀ t, f t = ((t-p)*(t-q)) • d t) ∧
      deriv f p = (p-q) • d p ∧ deriv f q = (q-p) • d q := by
  let h := smoothZeroFactor f p
  have hh : ContDiff ℝ ∞ h := smoothZeroFactor_smooth hf p
  have he (t : ℝ) : f t = (t-p) • h t := by
    simpa only [hp,sub_zero] using (smoothZeroFactor_identity hf p t).symm
  have hhq : h q = 0 := by
    have hz := he q
    rw [hq] at hz
    exact (smul_eq_zero.mp hz.symm).resolve_left (sub_ne_zero.mpr hpq.symm)
  let d := smoothZeroFactor h q
  have hd : ContDiff ℝ ∞ d := smoothZeroFactor_smooth hh q
  have hed (t : ℝ) : h t = (t-q) • d t := by
    simpa only [hhq,sub_zero] using (smoothZeroFactor_identity hh q t).symm
  have hef (t : ℝ) : f t = ((t-p)*(t-q)) • d t := by
    rw [he t,hed t,smul_smul]
  have hep : deriv f p = (p-q) • d p := by
    rw [←hed p]
    exact (smoothZeroFactor_self f p).symm
  have heq : deriv f q = (q-p) • d q := by
    have hder := (((hasDerivAt_id q).sub_const p).smul
      (hh.differentiable (by simp) q).hasDerivAt)
    have hefun : f = fun t => (t-p) • h t := funext he
    change HasDerivAt (fun t => (t-p) • h t)
      ((q-p) • deriv h q+1 • h q) q at hder
    rw [←hefun] at hder
    rw [hder.deriv,hhq,smul_zero,add_zero]
    exact congrArg ((q-p) • ·) (smoothZeroFactor_self h q).symm
  exact ⟨d,hd,hef,hep,heq⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
