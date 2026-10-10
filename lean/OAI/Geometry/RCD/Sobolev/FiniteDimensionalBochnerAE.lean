import OAI.Geometry.RCD.Coordinates.FiniteBilinearAE
import OAI.Geometry.RCD.Sobolev.BochnerShiftedQuadratic
import OAI.Geometry.RCD.Metric.ShiftedRadonBounds

namespace OAI

/-! # A common null set for the finite-dimensional Bochner correction -/

open Set Filter MeasureTheory TopologicalSpace

noncomputable section
namespace RegularPointCoordinates

/-- The scalar finite-dimensional Bochner bound, initially available in
each fixed direction, holds in every direction outside one null set. -/
theorem ae_finite_bochner_shift_nonneg {X : Type*} [MeasurableSpace X] {m : ℕ}
    (μ : Measure X) (B : X → Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ)
    (D : X → Euclidean m →ₗ[ℝ] ℝ) (N : ℝ) (hN : 0<N)
    (hBE : ∀ a, ∀ᵐ x ∂μ, (D x a)^2≤N*B x a a) :
    ∀ᵐ x ∂μ, ∀ a b, 0≤B x a a-2*b*D x a+N*b^2 := by
  obtain ⟨S,hS,hdense⟩ := exists_countable_dense (Euclidean m)
  let : Countable S := hS.to_subtype
  filter_upwards [ae_all_iff.mpr (fun a : S => hBE a)] with x hx
  have hc : IsClosed {a : Euclidean m | (D x a)^2≤N*B x a a} :=
    isClosed_le ((D x).toContinuousLinearMap.continuous.pow 2)
      (continuous_const.mul (bilinear_diagonal_continuous (B x)))
  have hsub : S ⊆ {a : Euclidean m | (D x a)^2≤N*B x a a} := fun a ha => hx ⟨a,ha⟩
  have hall := closure_minimal hsub hc
  rw [hdense.closure_eq] at hall
  exact fun a b => finite_bochner_shift_nonneg N (B x a a) (D x a) b hN (hall (mem_univ a))

/-- The diagonal bilinear density equals the Radon--Nikodym density of
the full positive measure. -/
theorem bochnerRadonDensity_diagonal {X : Type*} [MeasurableSpace X] {m : ℕ}
    (μ : Measure X) [SigmaFinite μ] (M : PositiveBilinearMeasure X (Euclidean m))
    (a : Euclidean m) :
    (fun x => bochnerRadonDensity μ M x a a) =ᵐ[μ]
      fun x => ((M.measure a).rnDeriv μ x).toReal := by
  have h := signed_rnDeriv_toSignedMeasure μ (M.measure a)
  rw [M.measure_toSignedMeasure] at h
  exact (bochnerRadonDensity_rep μ M a a).symm.trans h

/-- The scalar dimensional inequality gives the full shifted measure
lower bound, with no absolute-continuity assumption on its Bochner mass. -/
theorem shiftedBochnerLowerBound_of_finite_dimension {X : Type*} [MeasurableSpace X] {m : ℕ}
    (μ : Measure X) [SigmaFinite μ] (M : PositiveBilinearMeasure X (Euclidean m))
    {Ω : Set X} [IsFiniteMeasure (μ.restrict Ω)]
    (ell : Euclidean m →ₗ[ℝ] ℝ) (N : ℝ) (hN : 0<N)
    (hBE : ∀ a, ∀ᵐ x ∂μ.restrict Ω,
      (ell a)^2≤N*bochnerRadonDensity μ M x a a) :
    ShiftedBochnerLowerBound M (μ.restrict Ω) ell N := by
  have hpos := ae_finite_bochner_shift_nonneg (μ.restrict Ω)
    (bochnerRadonDensity μ M) (fun _ => ell) N hN hBE
  apply shiftedBochnerLowerBound_of_density μ M ell N
  intro a b
  filter_upwards [hpos,ae_restrict_of_ae (bochnerRadonDensity_diagonal μ M a)] with x hx he
  have hh := hx a b
  rw [he] at hh
  linarith only [hh]

end RegularPointCoordinates

end

end OAI
