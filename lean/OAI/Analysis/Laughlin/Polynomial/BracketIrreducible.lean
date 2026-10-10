import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.Analysis.Laughlin.EnergyNonnegative

namespace OAI

namespace Laughlin
open MvPolynomial

theorem bracket_irreducible {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Irreducible (bracket i j) := by
  let f : MvPolynomial (SpinorVariables N) ℂ := X (j,true)
  let g : MvPolynomial (SpinorVariables N) ℂ := -(X (j,false)*X (i,true))
  have hf : f ≠ 0 := X_ne_zero _
  have hif : (i,false) ∉ f.vars := by simp [f]
  have hig : (i,false) ∉ g.vars := by
    simp only [g, vars_neg]
    intro h
    have hu := vars_mul (X (j,false) : MvPolynomial (SpinorVariables N) ℂ) (X (i,true)) h
    simp [hij] at hu
  have hnd : ¬ f ∣ g := by
    intro hd
    let ev : MvPolynomial (SpinorVariables N) ℂ →+* ℂ :=
      eval₂Hom (RingHom.id ℂ) (fun z => if z = (j,true) then 0 else 1)
    have h := map_dvd ev hd
    norm_num [ev,f,g,eval₂Hom,hij,Ne.symm hij] at h
  have hr : IsRelPrime f g :=
    (X_prime (R := ℂ) (i := (j,true))).irreducible.isRelPrime_iff_not_dvd.mpr hnd
  have h := irreducible_mul_X_add f g (i,false) hf hif hig hr
  convert h using 1
  unfold bracket f g
  ring

theorem bracket_prime {N : ℕ} (i j : Fin N) (hij : i ≠ j) : Prime (bracket i j) :=
  irreducible_iff_prime.mp (bracket_irreducible i j hij)

end Laughlin

end OAI
