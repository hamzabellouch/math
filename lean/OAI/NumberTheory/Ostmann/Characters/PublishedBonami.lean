import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # Published finite-cube hypercontractive input

A. Bonami, *Étude des coefficients de Fourier des fonctions de Lᵖ(G)*,
Annales de l'Institut Fourier 20 (1970), no. 2, 335–402,
Chapter III, Theorems 2–3, printed pp. 374–376.
DOI: 10.5802/aif.357; https://www.numdam.org/item/10.5802/aif.357.pdf .

`PublishedBonamiBound` is only the real finite Boolean-cube consequence with
p=2 and q=2l: applying the noise operator with multiplier
(2l-1)^(-card Q/2) gives this weighted even-moment inequality. This is an
explicit hypothesis, not a global axiom. No assertion about primes, Jacobi
symbols, translating residues or the target sumset is included in it.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def rademacherMonomial {P : Finset ℕ} (Q : Finset P) (ε : P → Bool) : ℝ :=
  ∏ p ∈ Q, if ε p then 1 else -1

def PublishedBonamiBound : Prop :=
  ∀ (P : Finset ℕ) (l : ℕ), 0 < l → ∀ a : Finset P → ℝ,
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool, |∑ Q : Finset P, a Q * rademacherMonomial Q ε| ^ (2 * l) ≤
      (∑ Q : Finset P, ((2 * l - 1 : ℕ) : ℝ) ^ Q.card * (a Q) ^ 2) ^ l

end Ostmann

end OAI
