import Mathlib
import OAI.Geometry.PrescribedRicci.CalabiTensorAlgebra
import OAI.Geometry.PrescribedRicci.ChernPairDifferential
import OAI.Geometry.PrescribedRicci.KahlerGradientEnergy
import OAI.Geometry.PrescribedRicci.MatrixWirtinger

namespace OAI

/-! Array Wirtinger. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder Kronecker
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {n : Type*}

lemma holArray_eq_holDerivative {f : Coordinates d → Matrix (Fin d) (Fin d) ℂ}
    {z : Coordinates d} (hf : DifferentiableAt ℝ f z) (a : Fin d) :
    holArray f z a = holDerivative f z a := by
  ext i j
  exact holDeriv_entry hf a i j

lemma barArray_eq_barDerivative {f : Coordinates d → Matrix (Fin d) (Fin d) ℂ}
    {z : Coordinates d} (hf : DifferentiableAt ℝ f z) (a : Fin d) :
    barArray f z a = barDerivative f z a := by
  ext i j
  exact barDeriv_entry hf a i j

lemma holArray_const (K : Matrix n n ℂ) (z : Coordinates d) (a : Fin d) :
    holArray (fun _ => K) z a = 0 := by
  ext i j
  simp [holArray,holDeriv]

lemma barArray_const (K : Matrix n n ℂ) (z : Coordinates d) (a : Fin d) :
    barArray (fun _ => K) z a = 0 := by
  ext i j
  simp [barArray,barDeriv]

lemma holArray_transpose (K : Coordinates d → Matrix n n ℂ) (z : Coordinates d) (a : Fin d) :
    holArray (fun y => (K y).transpose) z a = (holArray K z a).transpose := rfl

lemma barArray_transpose (K : Coordinates d → Matrix n n ℂ) (z : Coordinates d) (a : Fin d) :
    barArray (fun y => (K y).transpose) z a = (barArray K z a).transpose := rfl

lemma barArray_eq_adjoint_hol {K : Coordinates d → Matrix n n ℂ} {z : Coordinates d}
    (hK : ∀ᶠ y in nhds z, (K y).IsHermitian) (a : Fin d) :
    barArray K z a = (holArray K z a)ᴴ := by
  ext i j
  change barDeriv (fun y => K y i j) z a = star (holDeriv (fun y => K y j i) z a)
  have he : (fun y => K y i j) =ᶠ[nhds z] (fun y => star (K y j i)) := by
    filter_upwards [hK] with y hy
    exact (Matrix.IsHermitian.ext_iff.mp hy i j).symm
  rw [barDeriv_congr he,barDeriv_star]

lemma holArray_tensor3 {L U V : Coordinates d → Matrix n n ℂ} {z : Coordinates d}
    (hL : ∀ i j, DifferentiableAt ℝ (fun y => L y i j) z)
    (hU : ∀ i j, DifferentiableAt ℝ (fun y => U y i j) z)
    (hV : ∀ i j, DifferentiableAt ℝ (fun y => V y i j) z) (a : Fin d) :
    holArray (fun y => tensor3 (L y) (U y) (V y)) z a =
      tensor3 (holArray L z a) (U z) (V z)+
      tensor3 (L z) (holArray U z a) (V z)+tensor3 (L z) (U z) (holArray V z a) := by
  ext i j
  change holDeriv (fun y => L y i.1 j.1*(U y i.2.1 j.2.1*V y i.2.2 j.2.2)) z a = _
  rw [holDeriv_mul (hL _ _) ((hU _ _).fun_mul (hV _ _)),
    holDeriv_mul (hU _ _) (hV _ _)]
  simp only [Matrix.add_apply,tensor3_apply,holArray]
  ring

lemma barArray_tensor3 {L U V : Coordinates d → Matrix n n ℂ} {z : Coordinates d}
    (hL : ∀ i j, DifferentiableAt ℝ (fun y => L y i j) z)
    (hU : ∀ i j, DifferentiableAt ℝ (fun y => U y i j) z)
    (hV : ∀ i j, DifferentiableAt ℝ (fun y => V y i j) z) (a : Fin d) :
    barArray (fun y => tensor3 (L y) (U y) (V y)) z a =
      tensor3 (barArray L z a) (U z) (V z)+
      tensor3 (L z) (barArray U z a) (V z)+tensor3 (L z) (U z) (barArray V z a) := by
  ext i j
  change barDeriv (fun y => L y i.1 j.1*(U y i.2.1 j.2.1*V y i.2.2 j.2.2)) z a = _
  rw [barDeriv_mul (hL _ _) ((hU _ _).fun_mul (hV _ _)),
    barDeriv_mul (hU _ _) (hV _ _)]
  simp only [Matrix.add_apply,tensor3_apply,barArray]
  ring

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI
