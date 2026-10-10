import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalProductRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactLiftContinuity

namespace OAI

/-! # Descending continuous representations from the Cartan factors

The existing factor model includes surjectivity and compact lifts. Thus
the algebraic descent also preserves continuity, without choosing a
global continuous factorization.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G] [LocallyCompactSpace G]
  [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G}

omit [SimplyConnectedSpace G] in
theorem CartanFactorModel.descend_representation (F : CartanFactorModel H Exp)
    (ρN : F.N.carrier →* A) (ρD : F.D.carrier →* A)
    (hcN : Continuous ρN) (hcD : Continuous ρD)
    (hconj : ∀ d n, ρN (F.action d n) = ρD d * ρN n * (ρD d)⁻¹)
    (hagree : ∀ n d, F.inclusionN n = F.inclusionD d → ρN n = ρD d) :
    ∃ ρ : G →* A, Continuous ρ ∧
      ∀ n d, ρ (F.inclusionN n * F.inclusionD d) = ρN n * ρD d := by
  let : ContinuousMul G := ⟨(contMDiff_mul (𝓘(ℝ, E)) ⊤).continuous⟩
  obtain ⟨ρ, hρ⟩ := exists_representation_of_factor_maps F.action F.inclusionN F.inclusionD
    (fun d => by ext n; exact F.conjugation d n)
    (fun g => by obtain ⟨⟨n, d⟩, h⟩ := F.surjective g; exact ⟨n, d, h⟩)
    ρN ρD hconj hagree
  refine ⟨ρ, ?_, hρ⟩
  exact continuous_of_compact_lifts
    (fun p : F.N.carrier × F.D.carrier => F.inclusionN p.1 * F.inclusionD p.2)
    (fun p : F.N.carrier × F.D.carrier => ρN p.1 * ρD p.2) ρ
    ((F.closedN.continuous.comp continuous_fst).mul (F.closedD.continuous.comp continuous_snd))
    ((hcN.comp continuous_fst).mul (hcD.comp continuous_snd))
    (fun p => hρ p.1 p.2) F.compactLifts

end PolycyclicRecognition

end

end OAI
