import OAI.Analysis.PureInfiniteness.CommutativeRelativeCopies
import OAI.Analysis.PureInfiniteness.CompressedCoefficientAlgebra
import OAI.Analysis.PureInfiniteness.CollapseFiniteCompression
import OAI.Analysis.PureInfiniteness.FiniteFamilyAbelianization

namespace OAI

/-! The finite part of KR02 Proposition 7.14: an approximation by finitely
many inner coefficients collapses to one whenever the targets commute. -/

noncomputable section
open scoped BigOperators IsMulCommutative

namespace WeakPureInfiniteness

variable {A I : Type*} [NonUnitalCStarAlgebra A] [Fintype I] [DecidableEq I]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem finite_oneStep_reduction (hP : MainGap.PropertyP A)
    (a b : I → N) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i j, Commute (a i) (a j))
    (m : ℕ) (d : Fin m → N) :
    ∃ f : N, ∀ i, ‖star f * b i * f - a i‖ ≤
      ‖(∑ j, star (d j) * b i * d j) - a i‖ := by
  classical
  let X := I × Fin m × Fin m
  let x (s : X) := star (d s.2.1) * b s.1 * d s.2.2
  let P := X × Fin 4
  let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  let p (s : P) := fourPositiveParts (x s.1) s.2
  obtain ⟨z, hz, hfix, _, hpair⟩ := ultrapower_finite_family_abelianization U hP a ha hc
    (Fintype.card P) (fun j => p (e.symm j))
    (fun j => fourPositiveParts_nonneg _ _)
  let C := coefficientAlgebra (compressedParts x z)
  have hcomm : ∀ s t, Commute (compressedParts x z s) (compressedParts x z t) := by
    intro s t
    simpa only [Equiv.symm_apply_apply, p, compressedParts] using hpair (e s) (e t)
  let : IsMulCommutative C := compressedParts_algebra_commutative x z hcomm
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  let c (s : X) : C := ⟨star z * x s * z, compression_mem_coefficientAlgebra x z s⟩
  obtain ⟨r, _, hrc, hrr⟩ := relative_copies_on_commutative_family (M := Fin m) U hP
    (NonUnitalStarSubalgebraClass.subtype (coefficientAlgebra (compressedParts x z))) c
  refine ⟨∑ j, d j * z * r j, ?_⟩
  intro i
  exact collapse_compression_error_le d r z (a i) (b i) hz (hfix i)
    (fun j k => hrc (i, j, k) k) (fun j k => hrr (i, j, k) j k)

end WeakPureInfiniteness

end

end OAI
