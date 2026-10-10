import OAI.Analysis.KadisonKastler.AmplificationUnitaryBound
import OAI.Analysis.KadisonKastler.ControlledCommutator
import OAI.Analysis.KadisonKastler.UnitaryExtension
import OAI.Analysis.KadisonKastler.PairedRepresentations

namespace OAI

/-! # Dimension-free amplification on a separable finite factor

The controlled free lift is constructed from the published ultrapower and
independence inputs. All word, row, recovery, and norm estimates are proved.
-/

namespace KadisonKastler

open Filter

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
variable {n : ℕ} [NeZero n]

local instance finiteAmplificationSourceOrder : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance finiteAmplificationSourceStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance finiteAmplificationOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance finiteAmplificationOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

variable (hpub : PublishedTracialUltrapower.{u})
variable (hmat : PublishedFiniteMatrixUltraproduct)
variable (hind : PublishedPopaFiniteBaseIndependence.{u})
variable (hM : Generator.IsII1Factor M.toStarSubalgebra)
variable (hCyclic : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
variable (hFock : PublishedDiagonalFockRepresentation.{u})
variable (h : H →L[ℂ] H) (hh : h.IsSymmetric) {δ : ℝ} (hδ : 0 ≤ δ)
variable (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖) (hn : 2 ≤ n)

include hpub hmat hind hM hCyclic hFock hh hδ hb hn in
/-- The actual randomization gives the `282δ` bound on every matrix unitary. -/
theorem finiteFactor_unitary_commutator_le
    (U : unitary (Algebra (matrixVonNeumann (ι := Fin n) M))) :
    let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
    ‖T * U.val.val - U.val.val * T‖ ≤ 282 * δ := by
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨P, s, hfree, hs⟩ := exists_freeHaar_commutator_lift
    (n := n) hpub hmat hind hM ω hω h hδ hb
  exact unitary_commutator_le_of_free_lift hM (concreteFactorTrace hM) P.traceQuotient
    (concreteFactorTrace_finiteVector hM) (concreteFactorTrace_finiteVector P.factor)
    hCyclic hFock s hfree h hh hδ hb hs hn U

include hpub hmat hind hM hCyclic hFock hh hδ hb hn in
/-- Four-unitary decomposition gives the manuscript's round `600δ` bound
on every element of a matrix amplification of size at least two. -/
theorem finiteFactor_matrix_commutator_le
    (a : Algebra (matrixVonNeumann (ι := Fin n) M)) :
    let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
    ‖T * a.val - a.val * T‖ ≤ 600 * δ * ‖a‖ := by
  let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
  let F : Algebra (matrixVonNeumann (ι := Fin n) M) →ₗ[ℂ]
      (Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) H) :=
    (innerDerivation T).comp (matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype.toLinearMap
  exact linear_norm_le_six_hundred F hδ
    (fun U => finiteFactor_unitary_commutator_le hpub hmat hind hM hCyclic hFock h hh hδ hb hn U) a

end

end KadisonKastler

end OAI
