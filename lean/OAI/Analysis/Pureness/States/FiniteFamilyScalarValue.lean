import OAI.Analysis.Pureness.States.FiniteFamilyScalarUltraproduct

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace OrderedSemigroup Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))
variable (hF : F.level 1 1=1)
variable (U : Ultrafilter ℕ)

theorem scalarTracialMatrixAWEmbedding_value (z : ScalarTracialMatrixUltraproduct U) :
    ultralimitAWQuasitrace (F.normalizedPositiveLevel hmono) U
      (F.normalizedPositiveLevel_unit hmono hF)
      (F.normalizedPositiveLevel_metricSize_add hmono)
      (F.normalizedPositiveLevel_sqrt_add hmono)
      (scalarTracialMatrixAWEmbedding F hmono hF U z) =
        (scalarMatrixUltraTracialState U).functional z := by
  obtain ⟨u,rfl⟩ := (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap_surjective z
  change ultralimitAWQuasitrace (F.normalizedPositiveLevel hmono) U
    (F.normalizedPositiveLevel_unit hmono hF)
    (F.normalizedPositiveLevel_metricSize_add hmono)
    (F.normalizedPositiveLevel_sqrt_add hmono)
    (scalarCoefficientAWMap F hmono hF U u) = _
  dsimp only [scalarCoefficientAWMap,StarAlgHom.comp_apply]
  rw [ultralimitAWQuasitrace_original]
  have h := quasitraceUltraComplex_tendsto (F.normalizedPositiveLevel hmono) U
    (F.normalizedPositiveLevel_unit hmono hF) (scalarCoefficientProductHom (A := A) u)
  have he (n : ℕ) : (F.normalizedPositiveLevel hmono n).complexValue
      ((scalarCoefficientProductHom (A := A) u) n) = (scalarMatrixTracialState n).functional (u n) :=
    (F.normalizedPositiveLevel_scalarCoefficient hmono hF n (u n)).trans
      ((scalarMatrixPositiveTrace_complex n (u n)).symm.trans (scalarMatrixPositiveTrace_eq_state n (u n)))
  simp only [he] at h
  exact tendsto_nhds_unique h (scalarMatrixUltraValue_tendsto U u)

theorem commuting_scalar_factor :
    Function.Injective (scalarTracialMatrixAWEmbedding F hmono hF U) ∧
    (∀ x z, Commute (F.matrixDiagonalAWMap hmono hF U x)
      (scalarTracialMatrixAWEmbedding F hmono hF U z)) ∧
    (∀ z, ultralimitAWQuasitrace (F.normalizedPositiveLevel hmono) U
      (F.normalizedPositiveLevel_unit hmono hF)
      (F.normalizedPositiveLevel_metricSize_add hmono)
      (F.normalizedPositiveLevel_sqrt_add hmono)
      (scalarTracialMatrixAWEmbedding F hmono hF U z) =
        (scalarMatrixUltraTracialState U).functional z) :=
  ⟨scalarTracialMatrixAWEmbedding_injective F hmono hF U,
    scalarTracialMatrixAWEmbedding_commute F hmono hF U,
    scalarTracialMatrixAWEmbedding_value F hmono hF U⟩
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI
