import Mathlib
import OAI.Geometry.PrescribedRicci.LocalKahlerEnergy

namespace OAI

/-! Matrix Wirtinger. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

def holDerivative (f : Coordinates d → Mat) (z : Coordinates d) (a : Fin d) : Mat :=
  (2:ℂ)⁻¹ • (fderiv ℝ f z (coordinateVector a) -
    Complex.I • fderiv ℝ f z (Complex.I • coordinateVector a))

lemma holDeriv_entry {f : Coordinates d → Mat} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (a i j : Fin d) :
    holDeriv (fun y => f y i j) z a = holDerivative f z a i j := by
  unfold holDeriv holDerivative
  rw [fderiv_entry hf,fderiv_entry hf]
  rfl

lemma contDiffAt_barDerivative {f : Coordinates d → Mat} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (a : Fin d) :
    ContDiffAt ℝ ∞ (fun y => barDerivative f y a) z := by
  unfold barDerivative
  exact ContDiffAt.smul (contDiffAt_const (c := (2:ℂ)⁻¹))
    ((contDiffAt_deriv_direction hf (coordinateVector a)).add
      (ContDiffAt.smul (contDiffAt_const (c := Complex.I))
        (contDiffAt_deriv_direction hf (Complex.I • coordinateVector a))))

lemma contDiffAt_holDerivative {f : Coordinates d → Mat} {z : Coordinates d}
    (hf : ContDiffAt ℝ ∞ f z) (a : Fin d) :
    ContDiffAt ℝ ∞ (fun y => holDerivative f y a) z := by
  unfold holDerivative
  exact ContDiffAt.smul (contDiffAt_const (c := (2:ℂ)⁻¹))
    ((contDiffAt_deriv_direction hf (coordinateVector a)).sub
      (ContDiffAt.smul (contDiffAt_const (c := Complex.I))
        (contDiffAt_deriv_direction hf (Complex.I • coordinateVector a))))

lemma barDerivative_mul {f g : Coordinates d → Mat} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (a : Fin d) :
    barDerivative (fun y => f y*g y) z a = barDerivative f z a*g z + f z*barDerivative g z a := by
  unfold barDerivative
  rw [MongeAmpere.real_fderiv_matrix_mul hf hg,MongeAmpere.real_fderiv_matrix_mul hf hg]
  simp only [smul_add,Matrix.smul_mul,Matrix.mul_smul,mul_add,add_mul]
  abel

lemma holDerivative_mul {f g : Coordinates d → Mat} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (a : Fin d) :
    holDerivative (fun y => f y*g y) z a = holDerivative f z a*g z + f z*holDerivative g z a := by
  unfold holDerivative
  rw [MongeAmpere.real_fderiv_matrix_mul hf hg,MongeAmpere.real_fderiv_matrix_mul hf hg]
  simp only [smul_add,smul_sub,Matrix.smul_mul,Matrix.mul_smul,mul_sub,sub_mul]
  abel

lemma barDerivative_inv {f : Coordinates d → Mat} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hi : IsUnit (f z).det) (a : Fin d) :
    barDerivative (fun y => (f y)⁻¹) z a = - ((f z)⁻¹*barDerivative f z a*(f z)⁻¹) := by
  have hh := barDerivative_comp hf (MongeAmpere.differentiableAt_inv (f z) (isUnit_iff_ne_zero.mp hi)) a
  exact hh.trans (MongeAmpere.fderiv_inv_apply _ _ hi)

lemma holDerivative_comp {f : Coordinates d → Mat} {F : Mat → Mat} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hF : DifferentiableAt ℂ F (f z)) (a : Fin d) :
    holDerivative (F ∘ f) z a = fderiv ℂ F (f z) (holDerivative f z a) := by
  have hd := ((hF.hasFDerivAt.restrictScalars ℝ).comp z hf.hasFDerivAt).fderiv
  unfold holDerivative
  have h1 := congrArg (fun L : Coordinates d →L[ℝ] Mat => L (coordinateVector a)) hd
  have h2 := congrArg (fun L : Coordinates d →L[ℝ] Mat => L (Complex.I • coordinateVector a)) hd
  calc
    _ = (2:ℂ)⁻¹ • (fderiv ℂ F (f z) (fderiv ℝ f z (coordinateVector a)) -
        Complex.I • fderiv ℂ F (f z) (fderiv ℝ f z (Complex.I • coordinateVector a))) :=
      congrArg₂ (fun U V : Mat => (2:ℂ)⁻¹ • (U-Complex.I • V)) h1 h2
    _ = _ := by simp only [map_smul,map_sub]

lemma holDerivative_inv {f : Coordinates d → Mat} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hi : IsUnit (f z).det) (a : Fin d) :
    holDerivative (fun y => (f y)⁻¹) z a = - ((f z)⁻¹*holDerivative f z a*(f z)⁻¹) := by
  have hh := holDerivative_comp hf (MongeAmpere.differentiableAt_inv (f z) (isUnit_iff_ne_zero.mp hi)) a
  exact hh.trans (MongeAmpere.fderiv_inv_apply _ _ hi)

def matrixTraceCLM : Mat →L[ℝ] ℂ := (Matrix.traceLinearMap (Fin d) ℝ ℂ).toContinuousLinearMap

lemma fderiv_trace {f : Coordinates d → Mat} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (v : Coordinates d) :
    fderiv ℝ (fun y => (f y).trace) z v = (fderiv ℝ f z v).trace := by
  exact congrArg (fun L : Coordinates d →L[ℝ] ℂ => L v)
    (((matrixTraceCLM (d:=d)).hasFDerivAt.comp z hf.hasFDerivAt).fderiv)

lemma barDeriv_trace {f : Coordinates d → Mat} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (a : Fin d) :
    barDeriv (fun y => (f y).trace) z a = (barDerivative f z a).trace := by
  unfold barDeriv barDerivative
  rw [fderiv_trace hf,fderiv_trace hf]
  simp only [trace_smul,trace_add,smul_eq_mul]

lemma holDeriv_trace {f : Coordinates d → Mat} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (a : Fin d) :
    holDeriv (fun y => (f y).trace) z a = (holDerivative f z a).trace := by
  unfold holDeriv holDerivative
  rw [fderiv_trace hf,fderiv_trace hf]
  simp only [trace_smul,trace_sub,smul_eq_mul]

variable {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma holDerivative_adjoint (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    (holDerivative (g.matrix q) z a)ᴴ = barDerivative (g.matrix q) z a := by
  unfold holDerivative barDerivative
  rw [conjTranspose_smul,conjTranspose_sub,conjTranspose_smul,
    (g.derivative_hermitian q hz _).eq,(g.derivative_hermitian q hz _).eq]
  simp only [map_inv₀,map_ofNat,Complex.star_def,Complex.conj_I,neg_smul,sub_neg_eq_add]

lemma holDerivative_symm (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a i j : Fin d) :
    holDerivative (g.matrix q) z a i j = holDerivative (g.matrix q) z j i a := by
  have hh := congrArg (fun M : Mat => star (M j i)) (g.holDerivative_adjoint q hz a)
  have hh' := congrArg (fun M : Mat => star (M a i)) (g.holDerivative_adjoint q hz j)
  simp only [conjTranspose_apply,star_star] at hh hh'
  rw [hh,hh',g.barDerivative_symm q hz a j i]

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI
