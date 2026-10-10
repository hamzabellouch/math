import OAI.Geometry.SurfaceImmersion.Whitney.EndpointSignModel

namespace OAI

/-! Diagonal transverse models retain the two prescribed axial zeros. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def diagonalDefectModel (b : ℝ → ℝ) (p q : ℝ) (x : Base) : Base :=
  normalizedAxisPolynomial p q x+(x 0*b (x 1)) • (![0,1] : Base)

lemma diagonalDefectModel_smooth {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (p q : ℝ) :
    ContDiff ℝ ∞ (diagonalDefectModel b p q) := by
  unfold diagonalDefectModel
  exact (normalizedAxisPolynomial_smooth p q).add
    (((contDiff_apply ℝ ℝ 0).mul (hb.comp (contDiff_apply ℝ ℝ 1))).smul contDiff_const)

lemma diagonalDefectModel_apply (b : ℝ → ℝ) (p q : ℝ) (x : Base) :
    diagonalDefectModel b p q x = ![(x 1-p)*(x 1-q),x 0*b (x 1)] := by
  ext i
  fin_cases i <;> simp [diagonalDefectModel,normalizedAxisPolynomial]

lemma diagonalDefectModel_axis (b : ℝ → ℝ) (p q t : ℝ) :
    diagonalDefectModel b p q (crosscapAxis t) = ![(t-p)*(t-q),0] := by
  simp [diagonalDefectModel_apply,crosscapAxis_apply]

lemma diagonalDefectModel_fderiv_axis {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (p q t : ℝ) :
    fderiv ℝ (diagonalDefectModel b p q) (crosscapAxis t) =
      triangularPlaneJet 0 (b t) ((t-p)+(t-q)) := by
  have hb' := (hb.differentiable (by simp) t).hasFDerivAt.comp
    (crosscapAxis t) (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (crosscapAxis t))
  have hh := (normalizedAxisPolynomial_hasFDerivAt p q (crosscapAxis t)).add
    (((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (crosscapAxis t)).mul hb').smul_const
      (![0,1] : Base))
  change HasFDerivAt (diagonalDefectModel b p q) _ _ at hh
  rw [hh.fderiv]
  ext v i
  fin_cases i <;> simp [triangularPlaneJet,crosscapAxis_apply]
  ring

lemma diagonalDefectModel_zero_iff {b : ℝ → ℝ} {p q : ℝ}
    (hp : b p ≠ 0) (hq : b q ≠ 0) (x : Base) :
    diagonalDefectModel b p q x = 0 ↔ x = crosscapAxis p ∨ x = crosscapAxis q := by
  rw [diagonalDefectModel_apply]
  constructor
  · intro he
    have h0 : (x 1-p)*(x 1-q) = 0 := congrFun he 0
    have h1 : x 0*b (x 1) = 0 := congrFun he 1
    rcases mul_eq_zero.mp h0 with h | h
    · have hx : x 1 = p := sub_eq_zero.mp h
      rw [hx] at h1
      have hz := (mul_eq_zero.mp h1).resolve_right hp
      left
      ext i
      fin_cases i <;> simp [crosscapAxis_apply,hz,hx]
    · have hx : x 1 = q := sub_eq_zero.mp h
      rw [hx] at h1
      have hz := (mul_eq_zero.mp h1).resolve_right hq
      right
      ext i
      fin_cases i <;> simp [crosscapAxis_apply,hz,hx]
  · rintro (rfl | rfl) <;> ext i <;> fin_cases i <;> simp [crosscapAxis_apply]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
