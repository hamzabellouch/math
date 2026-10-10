import OAI.Analysis.KadisonSimilarity.FreeProduct.MatrixSourceFreeness
import OAI.Analysis.KadisonSimilarity.Tracial.FiniteFactorPresentation

namespace OAI

/-! The constructed irreducible matrix source supplies the free position
required by every separably acting finite factor. -/

noncomputable section
namespace KadisonSimilarity
open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : VonNeumannAlgebra H} [TopologicalSpace.SeparableSpace H]

namespace FiniteFactorPresentation
variable (F : FiniteFactorPresentation P)

theorem freePosition (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    F.FreePosition ω hω := by
  let : Nontrivial F.N.toStarSubalgebra :=
    nontrivial_of_ne (F.equivalence 0) (F.equivalence 1) (fun h => by
      have he : (0 : P.toStarSubalgebra) = 1 := F.equivalence.injective h
      have ht := congrArg F.traceData.trace he
      rw [map_zero, F.traceData.one] at ht
      exact zero_ne_one ht)
  let : ∀ n, Nonempty (Fin (F.source.stages n).size) :=
    fun n => ⟨⟨0, (F.source.stages n).positive⟩⟩
  let : TopologicalSpace.SeparableSpace F.traceData.trace.GNS :=
    gns_separable_of_predual (concretePredualEquiv P) F.traceData.trace F.traceData.normal_predual
  apply finiteFactorFreeCornerInputs_of_normal_tower
    (generatedMatrixTrace F.source.stages F.representation) F.traceData.trace
    (generatedMatrixTrace_one F.source.stages F.representation) F.traceData.one
    (generatedMatrixTrace_tracial F.source.stages F.representation) F.traceData.tracial
    (generatedMatrixTrace_faithful F.source.stages F.representation) F.traceData.faithful
    (generatedMatrixTrace_normal F.source.stages F.representation) F.normal
    F.inclusion ?_ F.trace_inclusion ?_
    (concreteNestedTracialMatrices F.source.stages F.source.monotone F.representation)
    (matrix_stage_sizes_tendsto F.source.stages F.source.monotone F.source.source_factor.diffuse)
    ω hω
  · exact F.equivalence.symm.injective.comp
      (StarSubalgebra.inclusion_injective (FiniteMatrixStage.generated_le F.source.stages))
  · intro c hc
    have hcomm (a : FiniteMatrixStage.generated F.source.stages) :
        a.val * (F.equivalence c).val = (F.equivalence c).val * a.val := by
      have h := congrArg F.equivalence (hc a)
      change F.equivalence (F.inclusion a * c) = F.equivalence (c * F.inclusion a) at h
      rw [map_mul, map_mul] at h
      have ha : F.equivalence (F.inclusion a) = StarSubalgebra.inclusion
          (FiniteMatrixStage.generated_le F.source.stages) a :=
        F.equivalence.apply_symm_apply _
      rw [ha] at h
      exact congrArg Subtype.val h
    obtain ⟨z, hz⟩ := F.source.irreducible (F.equivalence c) hcomm
    refine ⟨z, F.equivalence.injective ?_⟩
    change F.equivalence c = F.equivalence (z • 1)
    rw [map_smul, map_one]
    exact hz

end FiniteFactorPresentation

/-- The three structural factor alternatives have local free-position data. -/
theorem publishedFactorCases [Nontrivial H]
    (hfactor : ∀ a : P.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ P.toStarSubalgebra c) :
    PublishedFactorCasesInput P := by
  apply publishedFactorCases_of_free_position P hfactor
  intro F
  obtain ⟨ω, hω⟩ := Ultrafilter.exists_le (Filter.cofinite : Filter ℕ)
  exact ⟨ω, hω, F.freePosition ω hω⟩

end KadisonSimilarity

end

end OAI
