import Mathlib
import OAI.Geometry.PrescribedRicci.HermitianPair
import OAI.Geometry.PrescribedRicci.LocalKahlerEnergy
import OAI.Geometry.PrescribedRicci.WirtingerScalar

namespace OAI

/-! Chern Pair Differential. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {n : Type*} [Fintype n]

def holVector (f : Coordinates d → n → ℂ) (z : Coordinates d) (a : Fin d) : n → ℂ :=
  fun i => holDeriv (fun y => f y i) z a

def barVector (f : Coordinates d → n → ℂ) (z : Coordinates d) (a : Fin d) : n → ℂ :=
  fun i => barDeriv (fun y => f y i) z a

def holArray (K : Coordinates d → Matrix n n ℂ) (z : Coordinates d) (a : Fin d) : Matrix n n ℂ :=
  fun i j => holDeriv (fun y => K y i j) z a

def barArray (K : Coordinates d → Matrix n n ℂ) (z : Coordinates d) (a : Fin d) : Matrix n n ℂ :=
  fun i j => barDeriv (fun y => K y i j) z a

lemma hermPair_smooth {K : Coordinates d → Matrix n n ℂ} {f g : Coordinates d → n → ℂ}
    {z : Coordinates d} (hK : ∀ i j, ContDiffAt ℝ ∞ (fun y => K y i j) z)
    (hf : ∀ i, ContDiffAt ℝ ∞ (fun y => f y i) z)
    (hg : ∀ i, ContDiffAt ℝ ∞ (fun y => g y i) z) :
    ContDiffAt ℝ ∞ (fun y => hermPair (K y) (f y) (g y)) z := by
  simp only [hermPair_expand]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt).comp z (hf i)).mul (hK i j)).mul (hg j)

lemma hermPair_hol {K : Coordinates d → Matrix n n ℂ} {f g : Coordinates d → n → ℂ}
    {z : Coordinates d} (hK : ∀ i j, DifferentiableAt ℝ (fun y => K y i j) z)
    (hf : ∀ i, DifferentiableAt ℝ (fun y => f y i) z)
    (hg : ∀ i, DifferentiableAt ℝ (fun y => g y i) z) (a : Fin d) :
    holDeriv (fun y => hermPair (K y) (f y) (g y)) z a =
      hermPair (K z) (barVector f z a) (g z)+hermPair (holArray K z a) (f z) (g z)+
        hermPair (K z) (f z) (holVector g z a) := by
  have hterm (i j : n) : DifferentiableAt ℝ (fun y => star (f y i)*K y i j*g y j) z :=
    (((hf i).star).fun_mul (hK i j)).fun_mul (hg j)
  have hrow (i : n) : DifferentiableAt ℝ (fun y => ∑ j, star (f y i)*K y i j*g y j) z :=
    DifferentiableAt.fun_sum (u:=Finset.univ) (fun j _ => hterm i j)
  simp only [hermPair_expand]
  rw [holDeriv_sum hrow]
  simp_rw [holDeriv_sum (fun j => hterm _ j)]
  have he (i j : n) : holDeriv (fun y => star (f y i)*K y i j*g y j) z a =
      (holDeriv (fun y => star (f y i)) z a*K z i j+star (f z i)*holDeriv (fun y => K y i j) z a)*g z j+
        (star (f z i)*K z i j)*holDeriv (fun y => g y j) z a := by
    rw [holDeriv_mul (((hf i).star).fun_mul (hK i j)) (hg j),
      holDeriv_mul (hf i).star (hK i j)]
  simp_rw [he,holDeriv_star]
  simp only [holArray,holVector,barVector,add_mul,Finset.sum_add_distrib]

lemma hermPair_bar {K : Coordinates d → Matrix n n ℂ} {f g : Coordinates d → n → ℂ}
    {z : Coordinates d} (hK : ∀ i j, DifferentiableAt ℝ (fun y => K y i j) z)
    (hf : ∀ i, DifferentiableAt ℝ (fun y => f y i) z)
    (hg : ∀ i, DifferentiableAt ℝ (fun y => g y i) z) (a : Fin d) :
    barDeriv (fun y => hermPair (K y) (f y) (g y)) z a =
      hermPair (K z) (holVector f z a) (g z)+hermPair (barArray K z a) (f z) (g z)+
        hermPair (K z) (f z) (barVector g z a) := by
  have hterm (i j : n) : DifferentiableAt ℝ (fun y => star (f y i)*K y i j*g y j) z :=
    (((hf i).star).fun_mul (hK i j)).fun_mul (hg j)
  have hrow (i : n) : DifferentiableAt ℝ (fun y => ∑ j, star (f y i)*K y i j*g y j) z :=
    DifferentiableAt.fun_sum (u:=Finset.univ) (fun j _ => hterm i j)
  simp only [hermPair_expand]
  rw [barDeriv_sum hrow]
  simp_rw [barDeriv_sum (fun j => hterm _ j)]
  have he (i j : n) : barDeriv (fun y => star (f y i)*K y i j*g y j) z a =
      (barDeriv (fun y => star (f y i)) z a*K z i j+star (f z i)*barDeriv (fun y => K y i j) z a)*g z j+
        (star (f z i)*K z i j)*barDeriv (fun y => g y j) z a := by
    rw [barDeriv_mul (((hf i).star).fun_mul (hK i j)) (hg j),
      barDeriv_mul (hf i).star (hK i j)]
  simp_rw [he,barDeriv_star]
  simp only [barArray,holVector,barVector,add_mul,Finset.sum_add_distrib]

def covHol (C : Coordinates d → Fin d → Matrix n n ℂ) (f : Coordinates d → n → ℂ)
    (z : Coordinates d) (a : Fin d) : n → ℂ := holVector f z a+C z a*ᵥ f z

lemma covHol_smooth {C : Coordinates d → Fin d → Matrix n n ℂ} {f : Coordinates d → n → ℂ}
    {z : Coordinates d} (hC : ∀ a i j, ContDiffAt ℝ ∞ (fun y => C y a i j) z)
    (hf : ∀ i, ContDiffAt ℝ ∞ (fun y => f y i) z) (a : Fin d) (i : n) :
    ContDiffAt ℝ ∞ (fun y => covHol C f y a i) z := by
  change ContDiffAt ℝ ∞ (fun y => holDeriv (fun w => f w i) y a+∑ j, C y a i j*f y j) z
  exact (contDiffAt_holDeriv (hf i) a).add
    (ContDiffAt.sum (fun j _ => (hC a i j).mul (hf j)))

lemma hermPair_hol_compatible {K : Coordinates d → Matrix n n ℂ}
    {C : Coordinates d → Fin d → Matrix n n ℂ} {f g : Coordinates d → n → ℂ}
    {z : Coordinates d} (hK : ∀ i j, DifferentiableAt ℝ (fun y => K y i j) z)
    (hf : ∀ i, DifferentiableAt ℝ (fun y => f y i) z)
    (hg : ∀ i, DifferentiableAt ℝ (fun y => g y i) z) (a : Fin d)
    (hcomp : holArray K z a = K z*C z a) :
    holDeriv (fun y => hermPair (K y) (f y) (g y)) z a =
      hermPair (K z) (barVector f z a) (g z)+hermPair (K z) (f z) (covHol C g z a) := by
  rw [hermPair_hol hK hf hg,hcomp,covHol,hermPair_add_right,← hermPair_mulVec_right]
  abel

lemma hermPair_bar_compatible {K : Coordinates d → Matrix n n ℂ}
    {C : Coordinates d → Fin d → Matrix n n ℂ} {f g : Coordinates d → n → ℂ}
    {z : Coordinates d} (hK : ∀ i j, DifferentiableAt ℝ (fun y => K y i j) z)
    (hf : ∀ i, DifferentiableAt ℝ (fun y => f y i) z)
    (hg : ∀ i, DifferentiableAt ℝ (fun y => g y i) z) (a : Fin d)
    (hcomp : barArray K z a = (C z a)ᴴ*K z) :
    barDeriv (fun y => hermPair (K y) (f y) (g y)) z a =
      hermPair (K z) (covHol C f z a) (g z)+hermPair (K z) (f z) (barVector g z a) := by
  rw [hermPair_bar hK hf hg,hcomp,covHol,hermPair_add_left,← hermPair_mulVec_left]

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI
