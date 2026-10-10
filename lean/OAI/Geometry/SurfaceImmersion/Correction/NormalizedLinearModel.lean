import OAI.Geometry.SurfaceImmersion.Geometry.AxisDefectJet

namespace OAI

/-! The actual first-order transverse model in normalized coordinates. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def normalizedAxisPolynomial (p q : ℝ) (x : Base) : Base :=
  ![(x 1-p)*(x 1-q),0]
def normalTransverse (G : Base → Base) (t : ℝ) : Base :=
  fderiv ℝ G (crosscapAxis t) (![1,0] : Base)
def normalizedLinearModel (G : Base → Base) (p q : ℝ) (x : Base) : Base :=
  normalizedAxisPolynomial p q x+x 0 • normalTransverse G (x 1)

lemma normalizedAxisPolynomial_smooth (p q : ℝ) :
    ContDiff ℝ ∞ (normalizedAxisPolynomial p q) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [normalizedAxisPolynomial] <;> fun_prop

lemma normalTransverse_smooth {G : Base → Base} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (normalTransverse G) :=
  ((hG.fderiv_right (m := ∞) (by simp)).comp crosscapAxis.contDiff).clm_apply contDiff_const

lemma normalizedLinearModel_smooth {G : Base → Base} (hG : ContDiff ℝ ∞ G) (p q : ℝ) :
    ContDiff ℝ ∞ (normalizedLinearModel G p q) :=
  (normalizedAxisPolynomial_smooth p q).add ((contDiff_apply ℝ ℝ 0).smul
    ((normalTransverse_smooth hG).comp (contDiff_apply ℝ ℝ 1)))

lemma normalizedLinearModel_axis (G : Base → Base) (p q t : ℝ) :
    normalizedLinearModel G p q (crosscapAxis t) = ![(t-p)*(t-q),0] := by
  simp [normalizedLinearModel,normalizedAxisPolynomial,crosscapAxis_apply]

lemma normalizedAxisPolynomial_hasFDerivAt (p q : ℝ) (x : Base) :
    HasFDerivAt (normalizedAxisPolynomial p q)
      ((ContinuousLinearMap.proj 1 : Base →L[ℝ] ℝ).smulRight (![(x 1-p)+(x 1-q),0] : Base)) x := by
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x).sub_const p).mul
    ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x).sub_const q)).smul_const
      (![1,0] : Base)
  convert h using 1
  · funext y
    ext i
    fin_cases i <;> simp [normalizedAxisPolynomial]
  · ext v i
    fin_cases i <;> simp
    ring

lemma normalizedLinearModel_fderiv_axis {G : Base → Base} (hG : ContDiff ℝ ∞ G)
    (p q t : ℝ) :
    fderiv ℝ (normalizedLinearModel G p q) (crosscapAxis t) =
      (ContinuousLinearMap.proj 1).smulRight (![(t-p)+(t-q),0] : Base)+
      (ContinuousLinearMap.proj 0).smulRight (normalTransverse G t) := by
  have hA := normalizedAxisPolynomial_hasFDerivAt p q (crosscapAxis t)
  have ha := ((normalTransverse_smooth hG).differentiable (by simp) t).hasFDerivAt.comp
    (crosscapAxis t) (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (crosscapAxis t))
  have hh := hA.add ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (crosscapAxis t)).smul ha)
  have he := hh.fderiv
  change fderiv ℝ (normalizedLinearModel G p q) (crosscapAxis t) = _ at he
  simpa [crosscapAxis_apply] using he

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
