import OAI.Geometry.SurfaceImmersion.Geometry.JetVariations

namespace OAI

/-! Real and imaginary parts commute with all actual ordered jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma directional_clm {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : A → E} (hf : ContDiff ℝ ∞ f) (w : List A) :
    iteratedDirectional w (L ∘ f) = L ∘ iteratedDirectional w f := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    rw [iteratedDirectional, ih]
    funext p
    have hs := contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hf.contDiffOn w)
    exact congrArg (fun T : A →L[ℝ] F => T v)
      ((L.hasFDerivAt.comp p (hs.differentiable (by simp) p).hasFDerivAt).fderiv)

def complexJet (H : Base → Fin 4 → ℂ) (w : List (Fin 2)) (a : Fin 4) : Base → ℂ :=
  iteratedDirectional (w.map coordinateVector) (fun p => H p a)

def realField (H : Base → Fin 4 → ℂ) : Base → Space := fun p a => (H p a).re
def imagField (H : Base → Fin 4 → ℂ) : Base → Space := fun p a => (H p a).im

lemma realField_smooth {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (realField H) := by
  apply contDiff_pi.mpr
  intro a
  exact Complex.reCLM.contDiff.comp (contDiff_pi.mp hH a)

lemma imagField_smooth {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (imagField H) := by
  apply contDiff_pi.mpr
  intro a
  exact Complex.imCLM.contDiff.comp (contDiff_pi.mp hH a)

lemma complexJet_re {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    (complexJet H w a p).re = jet (realField H) w a p := by
  exact (congrFun (directional_clm Complex.reCLM (contDiff_pi.mp hH a)
    (w.map coordinateVector)) p).symm

lemma complexJet_im {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    (complexJet H w a p).im = jet (imagField H) w a p := by
  exact (congrFun (directional_clm Complex.imCLM (contDiff_pi.mp hH a)
    (w.map coordinateVector)) p).symm

lemma complexJet_decompose {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    complexJet H w a p = (jet (realField H) w a p : ℂ) +
      Complex.I * (jet (imagField H) w a p : ℂ) := by
  rw [← complexJet_re hH, ← complexJet_im hH]
  exact Complex.ext (by simp) (by simp)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
