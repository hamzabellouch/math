import OAI.Analysis.KadisonKastler.InitialCyclicCommutantNeighbor
import OAI.Analysis.KadisonKastler.CyclicCommonMatrixStages
import OAI.Analysis.KadisonKastler.MatrixCommonPositionData
import OAI.Analysis.KadisonKastler.RelativeIrreducibilityTransport

namespace OAI

/-! # Constructed common tracial position for an increasing matrix subfactor

This proves the instance of CCSSWW, Lemma 4.10, used by the finite-factor
application. The common algebra is the actual increasing full-matrix closure.
-/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  {M N R : VonNeumannAlgebra H}

theorem exists_commonTracialPosition_of_matrixStages
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hM : IsII1Factor M.toStarSubalgebra) (hN : IsII1Factor N.toStarSubalgebra)
    (A : ℕ → FiniteMatrixStage R)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (hgen : FiniteMatrixStage.generatedVonNeumann A = R)
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 174 / 1000000000000000)
    (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ) :
    Nonempty (CommonTracialPositionData M N R hRM hRN γ (faithfulCyclicSpace M)) := by
  obtain ⟨P, e, hP, he, hcomp, hnear, hdist⟩ :=
    exists_initial_cyclic_commutant_neighbor (H := H) M N R hRM hRN hM hN
      (γ := γ) hγ (by linarith) hMN hNM
  let C := cyclicCommonAlgebra M R hRM
  have hCL : C ≤ faithfulCyclicAlgebra M := cyclicCommon_le M R hRM
  let f : Algebra R →⋆ₐ[ℂ] Algebra P := e.toStarAlgHom.comp (coordinateInclusion hRN)
  have hf : ∀ r, (f r).val = faithfulCyclicHom M (coordinateInclusion hRM r) := he
  have hCP : C ≤ P := cyclicCommon_le_neighbor M R hRM P f hf
  have he' : ∀ r, e (coordinateInclusion hRN r) =
      coordinateInclusion hCP (cyclicCommonEquiv M R hRM r) :=
    cyclicCommon_neighbor_restrict M R hRM P f hf
  obtain ⟨p⟩ := exists_faithfulCyclic_standardTracialPosition M hM
  have hi : ∀ T ∈ faithfulCyclicAlgebra M, (∀ r ∈ C, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M) :=
    relative_ambient_scalar_of_common_equivs hRM hCL
      (faithfulCyclicEquiv M) (cyclicCommonEquiv M R hRM)
      (cyclicCommon_restrict M R hRM) hirr
  exact exists_commonPositionData_of_matrix_cyclic_neighbor hRM hRN hCL hCP
    (faithfulCyclicEquiv M) e (cyclicCommonEquiv M R hRM)
    (cyclicCommon_restrict M R hRM) he' p hP (fun n => (A n).size)
    (normalImageMatrixUnits (cyclicCommonHom M R hRM) A)
    (cyclicCommonMatrixUnits_mono M R hRM A hA)
    (cyclicCommonMatrixUnits_generated M R hRM A hA hgen)
    hi hγ hsmall hMN hNM (fun a b _ hb => hcomp a b hb) hnear hdist

end

end KadisonKastler

end OAI
