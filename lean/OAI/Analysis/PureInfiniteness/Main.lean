import OAI.Analysis.CStarAlgebra.PureInfiniteness.Main
import OAI.Analysis.PureInfiniteness.Absorption

namespace OAI

/-!
# Weak pure infiniteness and Cuntz-algebra absorption

Individual proper infiniteness implies strong pure infiniteness for arbitrary,
possibly nonunital complex C*-algebras. Exactness removes a fixed finite
amplification. The rectangular epsilon formulation of Cuntz comparison agrees
with its sequential formulation.
-/

noncomputable section

open scoped ComplexOrder

namespace WeakPureInfiniteness.Campaign

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- Fixed-amplification proper infiniteness, including the zero element. -/
def FixedAmplification (A : Type u) [NonUnitalCStarAlgebra A] (n : ℕ) : Prop :=
  ∀ a : A, 0 ≤ a → ProperlyInfinite (diagonalCopies n a)

/-- Omitting zero does not change the fixed-amplification hypothesis. -/
theorem weaklyPurelyInfinite_iff :
    WeaklyPurelyInfinite A ↔ ∃ n : ℕ, 1 ≤ n ∧ FixedAmplification A n := by
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, fun _ ha => weak_amplification_all h ha⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, fun a ha _ => h a ha⟩

/-- Epsilon and sequential rectangular Cuntz comparison agree. -/
theorem finiteCuntzLE_iff {m n : ℕ}
    (a : CStarMatrix (Fin m) (Fin m) A)
    (b : CStarMatrix (Fin n) (Fin n) A) :
    MainGap.FiniteCuntzLE a b ↔ CuntzSubequiv a b := by
  rw [MainGap.finiteCuntzLE_iff_closure, cuntzSubequiv_iff_mem_closure]

private theorem scalarCorner_eq (a : A) :
    MainGap.scalarCorner a = diagonalCopies 1 a := by
  ext i j
  change a = if i = j then a else 0
  rw [ite_eq_left (Subsingleton.elim i j)]

/-- Translate the two-copy comparison without adding an exactness hypothesis. -/
theorem properlyInfinite_to_mainGap {a : A}
    (h : ProperlyInfinite (diagonalCopies 1 a)) : MainGap.ProperlyInfinite a := by
  have hc := h.submatrix_left
    (finSumFinEquiv.symm : Fin (1 + 1) → Fin 1 ⊕ Fin 1)
  rw [diagonalCopies_double] at hc
  change MainGap.FiniteCuntzLE (MainGap.doubleCorner a) (MainGap.scalarCorner a)
  rw [scalarCorner_eq]
  exact (finiteCuntzLE_iff _ _).mpr hc

/-- Theorem 1.1: arbitrary positive diagonals and an arbitrary mixed entry. -/
theorem individual_to_strong
    (hP : FixedAmplification A 1) :
    MainGap.UnrestrictedDiagonalization A ∧ StronglyPurelyInfinite A := by
  have hp : MainGap.PropertyP A := fun a ha => properlyInfinite_to_mainGap (hP a ha)
  refine ⟨MainGap.individual_to_strong hp, ?_⟩
  intro a b ha hb ε hε
  simpa only [MainGap.Diagonalization, mul_assoc] using
    MainGap.individual_to_strong_spi hp a b ha hb ε hε

/-- Theorem 1.2: exactness removes the fixed finite amplification. -/
theorem exact_fixedAmplification (hExact : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hF : FixedAmplification A n) :
    FixedAmplification A 1 ∧ MainGap.UnrestrictedDiagonalization A ∧
      StronglyPurelyInfinite A := by
  have hW : WeaklyPurelyInfinite A := ⟨n, hn, fun a ha _ => hF a ha⟩
  have hP : FixedAmplification A 1 := fun _ ha =>
    exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any hExact hW ha
  exact ⟨hP, individual_to_strong hP⟩

/-- The nuclear specialization, with no separability or unit assumption. -/
theorem nuclear_fixedAmplification (hNuclear : Nuclear A) {n : ℕ} (hn : 1 ≤ n)
    (hF : FixedAmplification A n) :
    FixedAmplification A 1 ∧ MainGap.UnrestrictedDiagonalization A ∧
      StronglyPurelyInfinite A :=
  exact_fixedAmplification (nuclear_exact hNuclear) hn hF

/-- Corollary 1.3, conditional only on the cited published absorption input. -/
theorem nuclear_absorption_conditional [TopologicalSpace.SeparableSpace A]
    (hKirchberg : KirchbergOInfinityAbsorption A)
    (hNuclear : Nuclear A) {n : ℕ} (hn : 1 ≤ n)
    (hF : FixedAmplification A n) :
    AbsorbsOInfinity A := by
  have hS : StronglyPurelyInfinite A :=
    (nuclear_fixedAmplification (A := A) hNuclear hn hF).2.2
  exact hKirchberg hNuclear hS

end WeakPureInfiniteness.Campaign

end

end OAI
