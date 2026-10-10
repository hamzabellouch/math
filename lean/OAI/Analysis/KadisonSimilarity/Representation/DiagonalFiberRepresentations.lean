import OAI.Analysis.KadisonSimilarity.Representation.DiagonalFieldAdjoint
import OAI.Analysis.KadisonSimilarity.Representation.ConullStarRepresentations

namespace OAI

/-! # Genuine representations of the diagonal commutant

For a norm-separable C-star algebra acting on a constant-fiber L² space,
commutation with measurable localizations gives genuine representations on
a conull base. All raw AE algebraic relations are derived from the actual
L² action. The original operator norm is recovered from the fiber norms.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal CStarAlgebra

variable {A Ω H : Type*} [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Actual diagonal-commuting representations decompose into genuine fiber
representations, with pointwise action on every L² vector and the exact
scalar norm-bound equivalence. -/
theorem exists_conull_diagonal_star_representations
    (σ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (hσ : ∀ (b : A) (r : Set Ω) (hr : MeasurableSet r),
      σ b * l2Localization μ r hr = l2Localization μ r hr * σ b) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ ρ : ∀ _a : s, A →⋆ₐ[ℂ] (H →L[ℂ] H),
        (∀ (b : A) (f : Lp H 2 μ),
          ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ,
            σ b f a = ρ a b (f a)) ∧
        ∀ (b : A) (C : ℝ), 0 ≤ C →
          (‖σ b‖ ≤ C ↔ ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖ρ a b‖ ≤ C) := by
  let F : A → Ω → H →L[ℂ] H := fun b => diagonalField μ (σ b) (hσ b)
  have hact (b : A) (f : Lp H 2 μ) : ∀ᵐ a ∂μ, σ b f a = F b a (f a) :=
    diagonalField_action μ (σ b) (hσ b) f
  have hzero : ∀ᵐ a ∂μ, F 0 a = 0 :=
    pointwise_field_zero μ _ (by simpa only [map_zero] using hact 0)
  have hone : ∀ᵐ a ∂μ, F 1 a = 1 :=
    pointwise_field_one μ _ (by simpa only [map_one] using hact 1)
  have hadd (b c : A) : ∀ᵐ a ∂μ, F (b + c) a = F b a + F c a :=
    pointwise_field_add μ (σ b) (σ c) _ _ _ (hact b) (hact c)
      (by simpa only [map_add] using hact (b + c))
  have hmul (b c : A) : ∀ᵐ a ∂μ, F (b * c) a = F b a * F c a :=
    pointwise_field_mul μ (σ b) (σ c) _ _ _ (hact b) (hact c)
      (by simpa only [map_mul] using hact (b * c))
  have hnorm (b : A) : ∀ᵐ a ∂μ, ‖F b a‖ ≤ ‖b‖ :=
    .of_forall fun a => (diagonalField_norm μ (σ b) (hσ b) a).trans
      (NonUnitalStarAlgHom.norm_apply_le σ b)
  have hstar (b : A) : ∀ᵐ a ∂μ, F (star b) a = star (F b a) :=
    pointwise_field_star μ (σ b) (hσ b) _ _ (hact b)
      (by simpa only [map_star] using hact (star b))
  have hI : ∀ᵐ a ∂μ, F (algebraMap ℂ A Complex.I) a =
      algebraMap ℂ (H →L[ℂ] H) Complex.I := by
    have hσI : σ (algebraMap ℂ A Complex.I) = Complex.I • 1 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one]
    have hi := pointwise_field_smul μ Complex.I 1 (F 1)
      (F (algebraMap ℂ A Complex.I))
      (by simpa only [map_one] using hact 1)
      (by simpa only [hσI] using
        hact (algebraMap ℂ A Complex.I))
    filter_upwards [hi, hone] with a ha ho
    simpa only [ho, Algebra.algebraMap_eq_smul_one] using ha
  obtain ⟨S, _, _, hexists, hagrees⟩ :=
    exists_dense_subring_ae_fiber_representations μ (fun _ => H)
      F hzero hone hadd hmul hnorm hstar hI
  obtain ⟨s, hsm, hsnull, ρ, hρ⟩ :=
    exists_conull_starRepresentations μ (fun _ => H) S F hexists hagrees
  have haction (b : A) (f : Lp H 2 μ) :
      ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, σ b f a = ρ a b (f a) := by
    have h := (ae_restrict_iff_subtype hsm).mp (ae_restrict_of_ae (hact b f))
    filter_upwards [h, hρ b] with a ha hb
    rw [hb]
    exact ha
  refine ⟨s, hsm, hsnull, ρ, haction, ?_⟩
  intro b C hC
  constructor
  · intro hb
    have hn : ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖F b a‖ ≤ ‖σ b‖ := by
      apply (ae_restrict_iff_subtype (μ := μ)
        (p := fun a : Ω => ‖F b a‖ ≤ ‖σ b‖) hsm).mp
      exact ae_restrict_of_ae (.of_forall (diagonalField_norm μ (σ b) (hσ b)))
    filter_upwards [hρ b, hn] with a ha hn
    rw [ha]
    exact hn.trans hb
  · exact norm_le_of_conull_pointwise_action μ (σ b) s hsm hsnull
      (fun a => ρ a b) (haction b) C hC

end KadisonSimilarity

end

end OAI
