import OAI.Analysis.KadisonKastler.HilbertSumFieldAction
import OAI.Analysis.KadisonSimilarity.Representation.KaplanskyStrongSequence

namespace OAI

/-! # Fiber membership from strong approximation on the Hilbert sum -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity Filter
open scoped Topology

noncomputable section

variable {X K : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
  [∀ n, CompleteSpace (K n)] (μ : ∀ n, Measure (X n))

local notation "L" => fun n => Lp (K n) 2 (μ n)

theorem hilbertSumCompression_strong_tendsto
    (T : ℕ → lp L 2 →L[ℂ] lp L 2) (S : lp L 2 →L[ℂ] lp L 2)
    (h : ∀ f, Tendsto (fun j => T j f) atTop (𝓝 (S f))) (n : ℕ) (f : L n) :
    Tendsto (fun j => hilbertSumCompression n (T j) f) atTop
      (𝓝 (hilbertSumCompression n S f)) := by
  simpa only [hilbertSumCompression_apply, lp.evalCLM, LinearMap.mkContinuous_apply,
    lp.evalₗ_apply, Function.comp_def] using
    (lp.evalCLM ℂ L 2 n).continuous.tendsto _ |>.comp (h (lp.single 2 n f))

variable [∀ n, IsFiniteMeasure (μ n)] [∀ n, TopologicalSpace.SeparableSpace (K n)]
  [TopologicalSpace.SeparableSpace (lp (fun n => Lp (K n) 2 (μ n)) 2)]
  {B : Type*} [CStarAlgebra B]

theorem ae_hilbertSum_field_mem_of_representation_closure
    (σ : B →⋆ₐ[ℂ] (lp L 2 →L[ℂ] lp L 2))
    (P : ∀ n, X n → VonNeumannAlgebra (K n))
    (R : B → ∀ n, X n → K n →L[ℂ] K n)
    (hR : ∀ a (f : lp L 2) n, σ a f n =ᵐ[μ n] fun x => R a n x (f n x))
    (hmem : ∀ a n, ∀ᵐ x ∂μ n, R a n x ∈ P n x)
    (T : lp L 2 →L[ℂ] lp L 2) (hT : T ∈ representationVonNeumannAlgebra σ)
    (Q : ∀ n, X n → K n →L[ℂ] K n)
    (hQ : ∀ (f : lp L 2) n, T f n =ᵐ[μ n] fun x => Q n x (f n x)) (n : ℕ) :
    ∀ᵐ x ∂μ n, Q n x ∈ P n x := by
  obtain ⟨a, hb, hs⟩ := kaplansky_strong_sequence σ T hT
  apply ae_field_mem_of_norm_bounded_strong_approximation (μ n) (P n)
    (fun j => hilbertSumCompression n (σ (a j))) (hilbertSumCompression n T)
    (fun j => R (a j) n) (Q n)
    (fun j => hilbertSumCompression_field_action μ (σ (a j)) (R (a j)) (hR (a j)) n)
    (hilbertSumCompression_field_action μ T Q hQ n)
    (hilbertSumCompression_strong_tendsto μ _ _ hs n) ‖T‖ (norm_nonneg T) ?_
    (fun j => hmem (a j) n)
  intro j
  exact (hilbertSumCompression_norm_le n (σ (a j))).trans
    ((NonUnitalStarAlgHom.norm_apply_le σ (a j)).trans (hb j))

end

end KadisonKastler

end OAI
