import Mathlib
import OAI.Analysis.Commutator.AbelianSpectralIndicators
import OAI.Analysis.Commutator.StableGNSModule
import OAI.Analysis.Commutator.StableSpectralUnitary
import OAI.Analysis.Commutator.InfiniteSeparable

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable InfiniteAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

theorem exists_stable_center_spectral_model [TopologicalSpace.SeparableSpace H] :
    ∃ μ : Measure (Spectrum M), IsFiniteMeasure μ ∧
      ∃ U : Space ℕ H ≃ₗᵢ[ℂ] Lp (Space ℕ ℂ) 2 μ,
        (∀ (a : CentralCorner.center M) (v : Space ℕ H),
          U (map (a : H →L[ℂ] H) v)=
            scalarVectorMultiplier μ (gelfandStarTransform _ a) (U v)) ∧
        (∀ (s : Set (Spectrum M)) (hs : MeasurableSet s),
          ∃ a : CentralCorner.center M,
            scalarMultiplier μ (gelfandStarTransform _ a)=indicatorOperator μ s hs) ∧
        TopologicalSpace.SeparableSpace (Lp (Space ℕ ℂ) 2 μ) := by
  obtain ⟨τ,hn,hf,W,hW⟩ := NormalRepresentation.exists_stable_gns_model (CentralCorner.center M)
  obtain ⟨μ,hμ,V,hV⟩ := CyclicSpectral.exists_gelfand_model τ.gnsStarAlgHom
    (TracialGNS.vacuum τ) (by
      have he : (fun a => τ.gnsStarAlgHom a (TracialGNS.vacuum τ))=
          (fun a => TracialGNS.algebraVector τ a) :=
        funext (fun a => TracialGNS.left_vacuum τ a)
      rw [he]
      exact TracialGNS.algebraVector_dense τ)
  let U := stableUnitary μ W V
  refine ⟨μ,hμ,U,?_,?_,?_⟩
  · intro a v
    exact stableUnitary_intertwines μ W V a.val (τ.gnsStarAlgHom a)
      (gelfandStarTransform _ a) (hW a) (hV a) v
  · intro s hs
    exact indicator_in_scalar_spectral_range M τ μ V hn hV s hs
  · let : TopologicalSpace.SeparableSpace (Space ℕ H) := separable_space
    exact U.symm.isometry.isEmbedding.separableSpace

end Kadison.CentralSpectral

end

end
end

end OAI
