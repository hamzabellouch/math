import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateConjugation

namespace OAI

/-! # Compact normalized exponential-coordinate groups

The defining equations retain both the exact group law and its adjoint
conjugation formula. All of these equations hold in the actual rescalings
and survive passage to a limit.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Module

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

def normalizedExponentialParameters {c : ℕ} (a : DynkinCoefficients c 2)
    (w : J → FreeMagma I) (b : J → V) (C : ℝ) :
    Set ((V →L[ℝ] V →L[ℝ] V) × (I → V)) :=
  normalizedGroupParameters a w b C ∩
    {p | ExponentialConjugationLaw (dynkinProduct a p.1) p.1}

theorem isCompact_normalizedExponentialParameters {c : ℕ}
    (a : DynkinCoefficients c 2) (w : J → FreeMagma I) (b : J → V) (C : ℝ) :
    IsCompact (normalizedExponentialParameters a w b C) :=
  (isCompact_normalizedGroupParameters a w b C).inter_right
    ((isClosed_exponentialConjugationLaw a).preimage continuous_fst)

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [DecidableEq I] {G A : Type*} [Group G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Actual rescalings satisfy all the closed equations used in the limiting
endpoint-map argument. No limiting-group assertion is an external input. -/
theorem exists_rescaledExponentialData_bound (X : I → L) {k : ℕ}
    (hk : LieModule.lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r →
      rescaledLieData X (boundedBracketWords k) β s r ∈
        normalizedExponentialParameters a (fun j => (β.val j : FreeMagma I))
          (fun j => Pi.single j 1) C := by
  obtain ⟨C, hC, hb⟩ := exists_rescaledGroupData_bound X hk hletters b₀
    Exp hinj hzero hneg hadd a hm
  refine ⟨C, hC, ?_⟩
  intro s β hβ r hr
  refine ⟨hb s β hβ r hr, ?_⟩
  exact basis_exponentialConjugationLaw _ Exp hinj hneg a hm j ρ hρ hmatch

end PolycyclicRecognition

end

end OAI
