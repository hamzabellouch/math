import Mathlib.Tactic
import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree

namespace OAI

namespace PiExponentSiegelAux.W30
universe u
variable {R : Type u} [CommRing R]

lemma scalarCone_bounded (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (d : ℕ)
    (hbound : ∀ n, d < n → Subsingleton (C.X n)) (n : ℕ) (hn : d + 1 < n) :
    Subsingleton ((scalarConeComplex C r).X n) := by
  cases n with
  | zero => omega
  | succ n =>
    let := hbound n (by omega)
    let := hbound (n + 1) (by omega)
    change Subsingleton (C.X (n + 1) × C.X n)
    infer_instance

lemma iterateScalarCones_bounded (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (d : ℕ) (hbound : ∀ n, d < n → Subsingleton (C.X n))
    (n : ℕ) (hn : d + rs.length < n) :
    Subsingleton ((iterateScalarCones C rs).X n) := by
  induction rs generalizing C d with
  | nil => exact hbound n (by simpa using hn)
  | cons r rs ih =>
    apply ih (scalarConeComplex C r) (d + 1) (scalarCone_bounded C r d hbound)
    simp only [List.length_cons] at hn
    omega

theorem regularSequenceComplex_bounded (rs : List R) (n : ℕ) (hn : rs.length < n) :
    Subsingleton ((regularSequenceComplex rs).X n) := by
  apply iterateScalarCones_bounded rs emptyKoszulComplex 0 ?_ n (by simpa using hn)
  intro k hk
  cases k with
  | zero => omega
  | succ k =>
    change Subsingleton (Fin 0 → R)
    infer_instance

theorem iterateScalarCones_zero (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    (iterateScalarCones C rs).X 0 = C.X 0 := by
  induction rs generalizing C with
  | nil => rfl
  | cons r rs ih => exact (ih (scalarConeComplex C r)).trans rfl

@[simp] theorem regularSequenceComplex_zero (rs : List R) :
    (regularSequenceComplex rs).X 0 = ModuleCat.of R R :=
  iterateScalarCones_zero rs emptyKoszulComplex

end PiExponentSiegelAux.W30

end OAI
