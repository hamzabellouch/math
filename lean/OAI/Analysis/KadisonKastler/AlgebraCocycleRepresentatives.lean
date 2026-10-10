import OAI.Analysis.KadisonKastler.NonsingularBoundary

namespace OAI

/-! # Algebra-valued representatives of an almost-everywhere cocycle

An ambient unitary lying in a von Neumann algebra is a unitary of that
algebra. Replacing exceptional values by one therefore makes the entire
family algebra-valued without changing any measurable or cocycle data.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Regard an ambient unitary contained in an algebra as a unitary of it. -/
def unitaryInAlgebra (M : VonNeumannAlgebra H) (u : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ M) : unitary (Algebra M) :=
  ⟨⟨u, hu⟩, by
    constructor
    · apply Subtype.ext
      exact Unitary.star_mul_self_of_mem u.property
    · apply Subtype.ext
      exact Unitary.mul_star_self_of_mem u.property⟩

@[simp]
theorem unitaryInAlgebra_coe (M : VonNeumannAlgebra H) (u : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ M) :
    (unitaryInAlgebra M u hu : Algebra M).val = (u : H →L[ℂ] H) := rfl

variable {G D : Type*}

/-- Replace the exceptional values of an ambient unitary family by one. -/
def algebraCocycleRepresentative (M : VonNeumannAlgebra H)
    (W : G → D → unitary (H →L[ℂ] H)) (g : G) (x : D) : unitary (Algebra M) := by
  classical
  exact if hx : (W g x : H →L[ℂ] H) ∈ M then unitaryInAlgebra M (W g x) hx else 1

variable [MeasurableSpace D] {μ : Measure D}

theorem algebraCocycleRepresentative_ae (M : VonNeumannAlgebra H)
    (W : G → D → unitary (H →L[ℂ] H))
    (hmem : ∀ g, ∀ᵐ x ∂μ, (W g x : H →L[ℂ] H) ∈ M) (g : G) :
    ∀ᵐ x ∂μ, (algebraCocycleRepresentative M W g x : Algebra M).val =
      (W g x : H →L[ℂ] H) := by
  filter_upwards [hmem g] with x hx
  simp only [algebraCocycleRepresentative, dite_eq_left hx, unitaryInAlgebra_coe]

/-- Measurable evaluations survive the exceptional-set replacement. -/
theorem algebraCocycleRepresentative_measurable (M : VonNeumannAlgebra H)
    (W : G → D → unitary (H →L[ℂ] H))
    (hmem : ∀ g, ∀ᵐ x ∂μ, (W g x : H →L[ℂ] H) ∈ M)
    (hmeas : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ)
    (g : G) (ξ : H) :
    AEStronglyMeasurable
      (fun x => (algebraCocycleRepresentative M W g x : Algebra M).val ξ) μ :=
  (hmeas g ξ).congr ((algebraCocycleRepresentative_ae M W hmem g).mono
    fun _ hx => congrArg (fun T : H →L[ℂ] H => T ξ) hx.symm)

variable [Group G]

/-- Nonsingularity transports the exceptional null set in the second
factor of the cocycle identity. -/
theorem algebraCocycleRepresentative_cocycle (M : VonNeumannAlgebra H)
    (α : NonsingularAction G D μ) (W : G → D → unitary (H →L[ℂ] H))
    (hmem : ∀ g, ∀ᵐ x ∂μ, (W g x : H →L[ℂ] H) ∈ M)
    (hcoc : ∀ g h, ∀ᵐ x ∂μ,
      (W g x : H →L[ℂ] H) * (W h (α.toPerm g⁻¹ x) : H →L[ℂ] H) =
        (W (g * h) x : H →L[ℂ] H)) (g h : G) :
    ∀ᵐ x ∂μ,
      (algebraCocycleRepresentative M W g x : Algebra M) *
        (algebraCocycleRepresentative M W h (α.toPerm g⁻¹ x) : Algebra M) =
          (algebraCocycleRepresentative M W (g * h) x : Algebra M) := by
  filter_upwards [algebraCocycleRepresentative_ae M W hmem g,
    (α.quasi g⁻¹).ae (algebraCocycleRepresentative_ae M W hmem h),
    algebraCocycleRepresentative_ae M W hmem (g * h), hcoc g h] with x hg hh hgh hc
  apply Subtype.ext
  change (algebraCocycleRepresentative M W g x : Algebra M).val *
      (algebraCocycleRepresentative M W h (α.toPerm g⁻¹ x) : Algebra M).val =
        (algebraCocycleRepresentative M W (g * h) x : Algebra M).val
  rw [hg, hh, hgh]
  exact hc

omit [Group G] in
/-- Any essential closeness estimate is retained with the same constant. -/
theorem algebraCocycleRepresentative_close (M : VonNeumannAlgebra H)
    (W : G → D → unitary (H →L[ℂ] H))
    (hmem : ∀ g, ∀ᵐ x ∂μ, (W g x : H →L[ℂ] H) ∈ M)
    (U : G → H →L[ℂ] H) {δ : ℝ}
    (hclose : ∀ g, ∀ᵐ x ∂μ, ‖(W g x : H →L[ℂ] H) - U g‖ ≤ δ) (g : G) :
    ∀ᵐ x ∂μ, ‖(algebraCocycleRepresentative M W g x : Algebra M).val - U g‖ ≤ δ := by
  filter_upwards [algebraCocycleRepresentative_ae M W hmem g, hclose g] with x hx hc
  rwa [hx]

/-- A typed algebra-valued cocycle, with all the original measurable data. -/
theorem exists_algebra_cocycle_representatives (M : VonNeumannAlgebra H)
    (α : NonsingularAction G D μ) (W : G → D → unitary (H →L[ℂ] H))
    (hmem : ∀ g, ∀ᵐ x ∂μ, (W g x : H →L[ℂ] H) ∈ M)
    (hmeas : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ)
    (hcoc : ∀ g h, ∀ᵐ x ∂μ,
      (W g x : H →L[ℂ] H) * (W h (α.toPerm g⁻¹ x) : H →L[ℂ] H) =
        (W (g * h) x : H →L[ℂ] H)) :
    ∃ WN : G → D → unitary (Algebra M),
      (∀ g, ∀ᵐ x ∂μ, (WN g x : Algebra M).val = (W g x : H →L[ℂ] H)) ∧
      (∀ g ξ, AEStronglyMeasurable (fun x => (WN g x : Algebra M).val ξ) μ) ∧
      (∀ g h, ∀ᵐ x ∂μ, (WN g x : Algebra M) *
        (WN h (α.toPerm g⁻¹ x) : Algebra M) = (WN (g * h) x : Algebra M)) := by
  exact ⟨algebraCocycleRepresentative M W, algebraCocycleRepresentative_ae M W hmem,
    algebraCocycleRepresentative_measurable M W hmem hmeas,
    algebraCocycleRepresentative_cocycle M α W hmem hcoc⟩

end

end KadisonKastler

end OAI
