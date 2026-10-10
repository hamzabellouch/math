import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Finiteness.Prod
import OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex

namespace OAI

namespace PiExponentSiegelAux.W30

universe u
variable {R : Type u} [CommRing R]

def emptyKoszulObject : ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R R
  | _ + 1 => ModuleCat.of R (Fin 0 → R)

def emptyKoszulComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of emptyKoszulObject (fun _ => 0) (fun _ => by simp)

def iterateScalarCones (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    List R → ChainComplex (ModuleCat.{u} R) ℕ
  | [] => C
  | r :: rs => iterateScalarCones (scalarConeComplex C r) rs

def regularSequenceComplex (rs : List R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  iterateScalarCones emptyKoszulComplex rs

lemma scalarCone_free (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (hfree : ∀ n, Module.Free R (C.X n)) (n : ℕ) :
    Module.Free R ((scalarConeComplex C r).X n) := by
  cases n with
  | zero => exact hfree 0
  | succ n =>
    let := hfree (n + 1)
    let := hfree n
    change Module.Free R (C.X (n + 1) × C.X n)
    infer_instance

lemma scalarCone_finite (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (hfinite : ∀ n, Module.Finite R (C.X n)) (n : ℕ) :
    Module.Finite R ((scalarConeComplex C r).X n) := by
  cases n with
  | zero => exact hfinite 0
  | succ n =>
    let := hfinite (n + 1)
    let := hfinite n
    change Module.Finite R (C.X (n + 1) × C.X n)
    infer_instance

lemma iterateScalarCones_free (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfree : ∀ n, Module.Free R (C.X n)) (n : ℕ) :
    Module.Free R ((iterateScalarCones C rs).X n) := by
  induction rs generalizing C with
  | nil => exact hfree n
  | cons r rs ih => exact ih (scalarConeComplex C r) (scalarCone_free C r hfree)

lemma iterateScalarCones_finite (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfinite : ∀ n, Module.Finite R (C.X n)) (n : ℕ) :
    Module.Finite R ((iterateScalarCones C rs).X n) := by
  induction rs generalizing C with
  | nil => exact hfinite n
  | cons r rs ih => exact ih (scalarConeComplex C r) (scalarCone_finite C r hfinite)

theorem regularSequenceComplex_free (rs : List R) (n : ℕ) :
    Module.Free R ((regularSequenceComplex rs).X n) := by
  apply iterateScalarCones_free
  intro k
  cases k with
  | zero =>
    change Module.Free R R
    exact Module.Free.self R
  | succ k =>
    change Module.Free R (Fin 0 → R)
    infer_instance

theorem regularSequenceComplex_finite (rs : List R) (n : ℕ) :
    Module.Finite R ((regularSequenceComplex rs).X n) := by
  apply iterateScalarCones_finite
  intro k
  cases k with
  | zero =>
    change Module.Finite R R
    exact Module.Finite.self R
  | succ k =>
    change Module.Finite R (Fin 0 → R)
    infer_instance

end PiExponentSiegelAux.W30

end OAI
