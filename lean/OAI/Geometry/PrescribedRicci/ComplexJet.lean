import Mathlib
import OAI.Geometry.PrescribedRicci.FamilyJetNorm

namespace OAI

/-! Complex Jet. -/

section

 

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Classical BigOperators
namespace TameInterpolation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

def cdir (v : E) (f : E → ℂ) (x : E) : ℂ := fderiv ℝ f x v

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma cdir_smooth (v : E) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (cdir v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma cdir_compact (v : E) {f : E → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (cdir v f) :=
  (hf.fderiv ℝ).comp_left (g:=fun L : E →L[ℝ] ℂ => L v) (by simp)

def cjet (e : ι → E) (f : E → ℂ) : {j : ℕ} → (Fin j → ι) → E → ℂ
  | 0,_ => f
  | _j+1,w => cdir (e (w 0)) (cjet e f (w ∘ Fin.succ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [Nonempty ι] in
lemma cjet_smooth (e : ι → E) {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    {j : ℕ} (w : Fin j → ι) : ContDiff ℝ ∞ (cjet e f w) := by
  induction j with
  | zero => exact hf
  | succ j ih => exact cdir_smooth _ (ih _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [Nonempty ι] in
lemma cjet_compact (e : ι → E) {f : E → ℂ} (hf : HasCompactSupport f)
    {j : ℕ} (w : Fin j → ι) : HasCompactSupport (cjet e f w) := by
  induction j with
  | zero => exact hf
  | succ j ih => exact cdir_compact _ (ih _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [Nonempty ι] in
lemma cjet_real_map (e : ι → E) {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (L : ℂ →L[ℝ] ℝ) {j : ℕ} (w : Fin j → ι) :
    jet e (fun x => L (f x)) w = fun x => L (cjet e f w x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [jet,cjet,ih]
    funext x
    dsimp only [dir,cdir]
    exact congrArg (fun T : E →L[ℝ] ℝ => T (e (w 0)))
      (L.hasFDerivAt.comp x ((cjet_smooth e hf _).differentiable (by simp) x).hasFDerivAt).fderiv

def realComponents (f : κ → E → ℂ) : κ × Bool → E → ℝ :=
  fun a x => if a.2 then (f a.1 x).im else (f a.1 x).re

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype κ] [Nonempty κ] in
lemma realComponents_smooth (f : κ → E → ℂ) (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (a : κ × Bool) : ContDiff ℝ ∞ (realComponents f a) := by
  rcases a with ⟨a,b⟩; cases b
  · exact Complex.reCLM.contDiff.comp (hf a)
  · exact Complex.imCLM.contDiff.comp (hf a)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [Fintype κ] [Nonempty κ] in
lemma realComponents_compact (f : κ → E → ℂ) (hf : ∀ a, HasCompactSupport (f a))
    (a : κ × Bool) : HasCompactSupport (realComponents f a) := by
  rcases a with ⟨a,b⟩; cases b
  · exact (hf a).comp_left (g:=Complex.re) rfl
  · exact (hf a).comp_left (g:=Complex.im) rfl

lemma lpNorm_complex_le (f : E → ℂ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hr : MemLp (fun x => (f x).re) p volume) (hi : MemLp (fun x => (f x).im) p volume) :
    lpNorm f p volume ≤ lpNorm (fun x => (f x).re) p volume + lpNorm (fun x => (f x).im) p volume := by
  have hh := lpNorm_mono_real (hr.norm.add hi.norm) (f:=f)
    (fun x => by simpa only [Real.norm_eq_abs,Pi.add_apply] using Complex.norm_le_abs_re_add_abs_im (f x))
  apply hh.trans
  simpa only [lpNorm_norm hr.aestronglyMeasurable,lpNorm_norm hi.aestronglyMeasurable] using lpNorm_add_le hr.norm (g:=fun x => ‖(f x).im‖) hp

lemma cjet_lpNorm_le (e : ι → E) (f : κ → E → ℂ)
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hc : ∀ a, HasCompactSupport (f a))
    (a : κ) {j : ℕ} (w : Fin j → ι) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    lpNorm (cjet e (f a) w) p volume ≤ 2*familyJetNorm e (realComponents f) j p := by
  have hr : ContDiff ℝ ∞ (fun x => (cjet e (f a) w x).re) := Complex.reCLM.contDiff.comp (cjet_smooth e (hf a) w)
  have hi : ContDiff ℝ ∞ (fun x => (cjet e (f a) w x).im) := Complex.imCLM.contDiff.comp (cjet_smooth e (hf a) w)
  have hcr := (cjet_compact e (hc a) w).comp_left (g:=Complex.re) rfl
  have hci := (cjet_compact e (hc a) w).comp_left (g:=Complex.im) rfl
  have hl := lpNorm_complex_le _ hp (hr.continuous.memLp_of_hasCompactSupport hcr) (hi.continuous.memLp_of_hasCompactSupport hci)
  have h1 := (lpNorm_jet_le e (realComponents f (a,false)) w p).trans (jetNorm_le_family e (realComponents f) (a,false) j p)
  have h2 := (lpNorm_jet_le e (realComponents f (a,true)) w p).trans (jetNorm_le_family e (realComponents f) (a,true) j p)
  change lpNorm (jet e (fun x => Complex.reCLM (f a x)) w) p volume ≤ _ at h1
  change lpNorm (jet e (fun x => Complex.imCLM (f a x)) w) p volume ≤ _ at h2
  rw [cjet_real_map e (hf a) Complex.reCLM] at h1
  rw [cjet_real_map e (hf a) Complex.imCLM] at h2
  change lpNorm (fun x => (cjet e (f a) w x).re) p volume ≤ _ at h1
  change lpNorm (fun x => (cjet e (f a) w x).im) p volume ≤ _ at h2
  linarith only [hl,h1,h2]

end TameInterpolation

end
end

end OAI
