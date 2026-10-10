import OAI.Analysis.KadisonSimilarity.Tracial.TracialRightSupportDischarge

namespace OAI

/-! # Transport of the discharged tracial inputs

These are coordinate changes through actual star algebra equivalences.
The concrete normal representation is retained as algebraic data; neither
rounding nor existence of a right support is assumed in the concrete model.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

section Equivalence
variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A star homomorphism of C-star algebras preserves positivity. -/
theorem starAlgHom_preserves_nonneg (f : A →⋆ₐ[ℂ] B) {a : A} (ha : 0 ≤ a) : 0 ≤ f a := by
  obtain ⟨b, hb⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := a)).mp ha
  rw [hb, map_mul, map_star]
  exact star_mul_self_nonneg _

/-- Positive functional in the coordinates of the target algebra. -/
def transportedPositiveTrace (τ : A →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] B) : B →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (τ.toLinearMap.comp e.symm.toStarAlgHom.toLinearMap)
    (fun _ hb => τ.map_nonneg (starAlgHom_preserves_nonneg e.symm.toStarAlgHom hb))

@[simp] theorem transportedPositiveTrace_apply (τ : A →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] B) (b : B) :
    transportedPositiveTrace τ e b = τ (e.symm b) := rfl

@[simp] theorem transportedPositiveTrace_map (τ : A →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] B) (a : A) :
    transportedPositiveTrace τ e (e a) = τ a := by simp

theorem transportedPositiveTrace_tracial (τ : A →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] B)
    (htr : ∀ a b, τ (a * b) = τ (b * a)) :
    ∀ b c, transportedPositiveTrace τ e (b * c) = transportedPositiveTrace τ e (c * b) := by
  intro b c
  simp only [transportedPositiveTrace_apply, map_mul]
  exact htr _ _

/-- Trace preservation is exactly the norm preservation needed for rounding. -/
theorem preGNS_norm_map_eq (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    (e : A →⋆ₐ[ℂ] B) (hτ : ∀ a, τB (e a) = τA a) (a : A) :
    ‖τB.toPreGNS (e a)‖ = ‖τA.toPreGNS a‖ := by
  simp only [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [← map_star e, ← map_mul e, hτ]

/-- Rounding is invariant under a trace-preserving star equivalence. -/
theorem spectralProjectionRoundingInput_of_equiv
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] B)
    (hτ : ∀ a, τB (e a) = τA a) (rounding : SpectralProjectionRoundingInput τB) :
    SpectralProjectionRoundingInput τA := by
  intro a ha
  obtain ⟨p, hp, hbound⟩ := rounding (e a) (ha.map e)
  refine ⟨e.symm p, hp.map e.symm, ?_⟩
  calc
    ‖τA.toPreGNS (e.symm p - a)‖ = ‖τB.toPreGNS (e (e.symm p - a))‖ :=
      (preGNS_norm_map_eq τA τB e.toStarAlgHom hτ _).symm
    _ = ‖τB.toPreGNS (p - e a)‖ := by rw [map_sub, e.apply_symm_apply]
    _ ≤ 2 * ‖τB.toPreGNS (e a * e a - e a)‖ := hbound
    _ = 2 * ‖τA.toPreGNS (a * a - a)‖ := by
      rw [← map_mul e, ← map_sub e]
      exact congrArg (fun t : ℝ => 2 * t)
        (preGNS_norm_map_eq τA τB e.toStarAlgHom hτ (a * a - a))

/-- Right supports transfer through the same actual algebraic equivalence. -/
theorem tracialRightSupportInput_of_equiv
    (τA : A → ℝ) (τB : B → ℝ) (e : A ≃⋆ₐ[ℂ] B) (hτ : ∀ a, τB (e a) = τA a)
    (q : A) (S : StarSubalgebra ℂ A)
    (support : TracialRightSupportInput τB (e q) (S.map e.toStarAlgHom)) :
    TracialRightSupportInput τA q S := by
  intro a
  let b : S.map e.toStarAlgHom := ⟨e (a : A), ⟨(a : A), a.property, rfl⟩⟩
  obtain ⟨r, hr, htrace, hright⟩ := support b
  change (e q * e (a : A)) * r = e q * e (a : A) at hright
  refine ⟨e.symm r, hr.map e.symm, ?_, ?_⟩
  · have he : τA (e.symm r) = τB r := by
      simpa only [e.apply_symm_apply] using (hτ (e.symm r)).symm
    rw [he, ← hτ q]
    exact htrace
  · have h := congrArg e.symm hright
    simpa only [map_mul, e.symm_apply_apply] using h

end Equivalence

section Concrete
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

local instance transportModel_closed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed P.carrier
  rw [← P.centralizer_centralizer']
  exact Set.isClosed_centralizer _

/-- A faithful normal realization with precisely this represented range
supplies the star equivalence; no tracial input is needed for this step. -/
def equivalenceOfConcreteRange (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hinj : Function.Injective ρ) (hrange : ρ.range = P.toStarSubalgebra) :
    A ≃⋆ₐ[ℂ] P.toStarSubalgebra :=
  StarAlgEquiv.ofBijective (ρ.codRestrict P.toStarSubalgebra (fun a => by
    rw [← hrange]
    exact ⟨a, rfl⟩))
    ⟨(StarAlgHom.injective_codRestrict _ _ _).mpr hinj, by
      intro b
      have hb : (b : H →L[ℂ] H) ∈ ρ.range := by
        rw [hrange]
        exact b.property
      obtain ⟨a, ha⟩ := hb
      exact ⟨a, Subtype.ext ha⟩⟩

/-- The concrete spectral theorem discharges rounding after an actual
faithful normal realization of the abstract algebra. -/
theorem spectralProjectionRoundingInput_of_concrete_equiv
    (τ : A →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] P.toStarSubalgebra) :
    SpectralProjectionRoundingInput τ :=
  spectralProjectionRoundingInput_of_equiv τ (transportedPositiveTrace τ e) e
    (transportedPositiveTrace_map τ e)
    (spectralProjectionRoundingInput P (transportedPositiveTrace τ e))

/-- The concrete polar construction discharges right supports in the
abstract algebra through that same faithful normal realization. -/
theorem tracialRightSupportInput_of_concrete_equiv
    (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (e : A ≃⋆ₐ[ℂ] P.toStarSubalgebra) (q : A) (hq : IsStarProjection q)
    (S : StarSubalgebra ℂ A) : TracialRightSupportInput (fun a => (τ a).re) q S := by
  apply tracialRightSupportInput_of_equiv (fun a => (τ a).re)
    (fun b => (transportedPositiveTrace τ e b).re) e
    (fun a => congrArg Complex.re (transportedPositiveTrace_map τ e a)) q S
  exact tracialRightSupportInput P (transportedPositiveTrace τ e)
    (transportedPositiveTrace_tracial τ e htr) (e q) (hq.map e.toStarAlgHom) (S.map e.toStarAlgHom)

/-- A faithful representation whose range is the stated von Neumann
algebra supplies all the coordinates needed for spectral rounding. -/
theorem spectralProjectionRoundingInput_of_concrete_range
    (τ : A →ₚ[ℂ] ℂ) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hinj : Function.Injective ρ) (hrange : ρ.range = P.toStarSubalgebra) :
    SpectralProjectionRoundingInput τ :=
  spectralProjectionRoundingInput_of_concrete_equiv P τ
    (equivalenceOfConcreteRange P ρ hinj hrange)

/-- The same actual representation supplies the propagation right
supports for every projection and every subalgebra. -/
theorem tracialRightSupportInput_of_concrete_range
    (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hinj : Function.Injective ρ)
    (hrange : ρ.range = P.toStarSubalgebra)
    (q : A) (hq : IsStarProjection q) (S : StarSubalgebra ℂ A) :
    TracialRightSupportInput (fun a => (τ a).re) q S :=
  tracialRightSupportInput_of_concrete_equiv P τ htr
    (equivalenceOfConcreteRange P ρ hinj hrange) q hq S

end Concrete
end KadisonSimilarity

end

end OAI
