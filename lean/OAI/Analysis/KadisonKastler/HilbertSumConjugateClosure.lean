import OAI.Analysis.KadisonKastler.HilbertSumFieldClosure
import OAI.Analysis.KadisonKastler.HilbertSumCoordinateAction
import OAI.Analysis.KadisonSimilarity.Representation.RepresentationCenterTransport

namespace OAI

/-! # Fiber closure after a unitary change of coordinates -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {C H : Type*} [CStarAlgebra C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))
  [∀ n, IsFiniteMeasure (μ n)] [∀ n, TopologicalSpace.SeparableSpace (K n)]
  [TopologicalSpace.SeparableSpace (lp (fun n => Lp (K n) 2 (μ n)) 2)]

local notation "L" => fun n => Lp (K n) 2 (μ n)

theorem ae_hilbertSum_field_mem_of_conjugate_closure
    (U : H ≃ₗᵢ[ℂ] lp L 2) (σ : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (P : ∀ n, X n → VonNeumannAlgebra (K n))
    (R : C → ∀ n, X n → K n →L[ℂ] K n)
    (hR : ∀ a (v : H) n, U (σ a v) n =ᵐ[μ n] fun x => R a n x (U v n x))
    (hmem : ∀ a n, ∀ᵐ x ∂μ n, R a n x ∈ P n x)
    (T : lp L 2 →L[ℂ] lp L 2)
    (hT : T ∈ representationVonNeumannAlgebra (U.conjStarAlgEquiv.toStarAlgHom.comp σ))
    (Q : ∀ n, X n → K n →L[ℂ] K n)
    (hQ : ∀ (f : lp L 2) n, T f n =ᵐ[μ n] fun x => Q n x (f n x)) (n : ℕ) :
    ∀ᵐ x ∂μ n, Q n x ∈ P n x :=
  ae_hilbertSum_field_mem_of_representation_closure μ
    (U.conjStarAlgEquiv.toStarAlgHom.comp σ) P R
    (conjugated_hilbertSum_action μ U σ R hR) hmem T hT Q hQ n

theorem ae_hilbertSum_representation_field_mem
    (U : H ≃ₗᵢ[ℂ] lp L 2) (σ : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : ∀ n, X n → C →⋆ₐ[ℂ] (K n →L[ℂ] K n))
    (hρ : ∀ a (v : H) n, U (σ a v) n =ᵐ[μ n] fun x => ρ n x a (U v n x))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ)
    (Q : ∀ n, X n → K n →L[ℂ] K n)
    (hQ : ∀ (f : lp L 2) n, U.conjStarAlgEquiv T f n =ᵐ[μ n]
      fun x => Q n x (f n x)) (n : ℕ) :
    ∀ᵐ x ∂μ n, Q n x ∈ representationVonNeumannAlgebra (ρ n x) :=
  ae_hilbertSum_field_mem_of_conjugate_closure μ U σ
    (fun n x => representationVonNeumannAlgebra (ρ n x)) (fun a n x => ρ n x a) hρ
    (fun a n => Filter.Eventually.of_forall fun x => mem_representationVonNeumannAlgebra (ρ n x) a)
    (U.conjStarAlgEquiv T)
    (representation_bicommutant_map_mem U.conjStarAlgEquiv σ
      (U.conjStarAlgEquiv.toStarAlgHom.comp σ) (fun _ => rfl) T hT) Q hQ n

end

end KadisonKastler

end OAI
