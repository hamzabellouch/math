import OAI.Analysis.Pureness.States.ScalarTracialUltraproductTrace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
variable (U : Ultrafilter ℕ)

theorem scalarTracialMatrixAWEmbedding_value (z : ScalarTracialMatrixUltraproduct U) :
    ultralimitAWQuasitrace (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
      (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
      (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
      (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)
      (scalarTracialMatrixAWEmbedding hsimple y hy f U z) =
        (scalarMatrixUltraTracialState U).functional z := by
  obtain ⟨u,rfl⟩ := (filteredQuasitraceClosedIdeal scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit).quotientMap_surjective z
  change ultralimitAWQuasitrace (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)
    (scalarCoefficientAWMap hsimple y hy f U u) = _
  dsimp only [scalarCoefficientAWMap,StarAlgHom.comp_apply]
  rw [ultralimitAWQuasitrace_original]
  have h := quasitraceUltraComplex_tendsto (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f) (scalarCoefficientProductHom (A := A) u)
  have he (n : ℕ) : (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n).complexValue
      ((scalarCoefficientProductHom (A := A) u) n) = (scalarMatrixTracialState n).functional (u n) :=
    (normalizedMatrixState_scalarCoefficient hsimple y hy f n (u n)).trans
      ((scalarMatrixPositiveTrace_complex n (u n)).symm.trans (scalarMatrixPositiveTrace_eq_state n (u n)))
  simp only [he] at h
  exact tendsto_nhds_unique h (scalarMatrixUltraValue_tendsto U u)

theorem matrixState_commuting_scalar_factor :
    Function.Injective (scalarTracialMatrixAWEmbedding hsimple y hy f U) ∧
    (∀ x z, Commute (matrixStateDiagonalAWEmbedding hsimple y hy f U x)
      (scalarTracialMatrixAWEmbedding hsimple y hy f U z)) ∧
    (∀ z, ultralimitAWQuasitrace (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
      (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
      (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
      (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)
      (scalarTracialMatrixAWEmbedding hsimple y hy f U z) =
        (scalarMatrixUltraTracialState U).functional z) :=
  ⟨scalarTracialMatrixAWEmbedding_injective hsimple y hy f U,
    scalarTracialMatrixAWEmbedding_commute hsimple y hy f U,
    scalarTracialMatrixAWEmbedding_value hsimple y hy f U⟩
end CuntzPureness

end

end OAI
