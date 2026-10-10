import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import OAI.Geometry.NodalSets.Waves.WaveJetAssembly

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section
abbrev Coord := Fin 4 → ℝ

def reval (p : CPoly) : Coord → ℂ := fun x ↦ eval (fun i ↦ (x i : ℂ)) p

def coordCLM (i : Fin 4) : Coord →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

lemma reval_contDiff (p : CPoly) : ContDiff ℝ ∞ (reval p) := by
  change ContDiff ℝ ∞ (fun x ↦ reval p x)
  induction p using MvPolynomial.induction_on with
  | C a => simpa [reval] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Coord ↦ a))
  | add p q hp hq => simpa [reval] using hp.add hq
  | mul_X p i hp =>
    simpa [reval, coordCLM] using hp.mul (coordCLM i).contDiff

theorem fderiv_reval (p : CPoly) (x v : Coord) :
    fderiv ℝ (reval p) x v = ∑ i, reval (pderiv i p) x * (v i : ℂ) := by
  have hd (p : CPoly) : DifferentiableAt ℝ (reval p) x :=
    (reval_contDiff p).differentiable (by simp) x
  induction p using MvPolynomial.induction_on with
  | C a =>
    have he : reval (C a) = fun _ ↦ a := by ext; simp [reval]
    rw [he]
    simp [reval]
  | add p q hp hq =>
    have he : reval (p + q) = fun x ↦ reval p x + reval q x := by ext; simp [reval]
    rw [he]
    change (fderiv ℝ (reval p + reval q) x) v = _
    rw [fderiv_add (hd p) (hd q)]
    simp only [add_apply, hp, hq, map_add, reval, add_mul,
      Finset.sum_add_distrib]
  | mul_X p j hp =>
    have he : reval (p * X j) = fun x ↦ reval p x * coordCLM j x := by
      ext; simp [reval, coordCLM]
    rw [he]
    change (fderiv ℝ (reval p * ⇑(coordCLM j)) x) v = _
    rw [fderiv_mul (hd p) (coordCLM j).differentiableAt]
    simp [hp, reval, coordCLM, pderiv_X, Finset.sum_add_distrib,
      Finset.mul_sum, mul_add, mul_comm, mul_left_comm, Pi.single_apply, apply_ite]

def coordPartial (i : Fin 4) (f : Coord → ℂ) (x : Coord) : ℂ :=
  fderiv ℝ f x (Pi.single i 1)

lemma coordPartial_reval (i : Fin 4) (p : CPoly) : coordPartial i (reval p) = reval (pderiv i p) := by
  funext x
  simp [coordPartial, fderiv_reval, Pi.single_apply, apply_ite]

def smoothSecondOrder (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (f : Coord → ℂ) (x : Coord) : ℂ :=
  (∑ i, ∑ j, g i j x * coordPartial i (coordPartial j f) x) + ∑ i, b i x * coordPartial i f x

def smoothEikonal (g : Fin 4 → Fin 4 → Coord → ℂ) (f : Coord → ℂ) (x : Coord) : ℂ :=
  (∑ i, ∑ j, g i j x * coordPartial i f x * coordPartial j f x) + 4

theorem reval_secondOrder (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly) (p : CPoly) :
    reval (polynomialSecondOrder g b p) =
      smoothSecondOrder (fun i j ↦ reval (g i j)) (fun i ↦ reval (b i)) (reval p) := by
  funext x
  simp [polynomialSecondOrder, smoothSecondOrder, coordPartial_reval, reval]

theorem reval_eikonal (g : Fin 4 → Fin 4 → CPoly) (p : CPoly) :
    reval (polynomialEikonal g p) = smoothEikonal (fun i j ↦ reval (g i j)) (reval p) := by
  funext x
  simp [polynomialEikonal, smoothEikonal, coordPartial_reval, reval, mul_assoc]

end
end Yau.Jets

end OAI
