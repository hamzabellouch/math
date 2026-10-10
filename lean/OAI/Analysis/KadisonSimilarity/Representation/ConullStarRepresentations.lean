import OAI.Analysis.KadisonSimilarity.Representation.AERepresentationAgreement

namespace OAI

/-! # Genuine fiber representations on a measurable conull base

Restricting to a measurable conull set allows the almost-everywhere
representation theorem to be used as an actual family of representations.
The original section for each fixed algebra element remains unchanged
almost everywhere after this restriction.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter

variable {A : Type*} [CStarAlgebra A]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ x, NormedAddCommGroup (K x)]
  [∀ x, InnerProductSpace ℂ (K x)] [∀ x, CompleteSpace (K x)]

/-- Choose genuine representations on a measurable conull set, retaining
the prescribed representatives almost everywhere for each fixed element. -/
theorem exists_conull_starRepresentations
    (S : Subring A) (f : ∀ _a : A, ∀ x, K x →L[ℂ] K x)
    (hexists : ∀ᵐ x ∂μ, ∃ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
      ∀ b : S, σ b = f b x)
    (hagrees : ∀ a : A, ∀ᵐ x ∂μ, ∀ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
      (∀ b : S, σ b = f b x) → σ a = f a x) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ σ : ∀ x : s, A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
        ∀ a : A, ∀ᵐ x ∂Measure.comap ((↑) : s → Ω) μ, σ x a = f a x := by
  classical
  obtain ⟨s, hs, hsm, hsexists⟩ := hexists.exists_measurable_mem
  choose σ hσ using fun x : s => hsexists x x.property
  refine ⟨s, hsm, ?_, σ, ?_⟩
  · exact (mem_ae_iff.mp hs)
  · intro a
    have h := (ae_restrict_iff_subtype hsm).mp (ae_restrict_of_ae (hagrees a))
    exact h.mono fun x hx => hx (σ x) (hσ x)

end KadisonSimilarity

end

end OAI
