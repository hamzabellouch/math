import OAI.Analysis.KadisonKastler.SpectralVectorMeasure
import OAI.Analysis.KadisonKastler.Algebra
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

namespace OAI

/-! # Spectral commutation for real character multipliers

Character commutation passes to every unitary of their commutant.
Finite vector measures then give scalar-multiplier commutation, and
the linear span of unitaries gives the assertion for every operator.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularCharacterUnitary_neg (a : ℝ) :
    regularCharacterUnitary (H := H) (-a) = star (regularCharacterUnitary a) := by
  simpa only [regularCharacterRepresentation, MonoidHom.coe_mk,
    OneHom.coe_mk, toAdd_inv, toAdd_ofAdd, Unitary.star_eq_inv] using
    map_inv (regularCharacterRepresentation (H := H)) (Multiplicative.ofAdd a)

/-- Commutation on the unitary generators extends by their linear span. -/
theorem commute_map_of_unitaries {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (T : B)
    (h : ∀ u : unitary A, Commute (f u) T) (a : A) : Commute (f a) T := by
  let L : A →ₗ[ℂ] B :=
    ((LinearMap.mulRight ℂ T) - (LinearMap.mulLeft ℂ T)).comp f.toAlgHom.toLinearMap
  have hspan : Submodule.span ℂ (unitary A : Set A) ≤ L.ker := by
    apply Submodule.span_le.mpr
    intro u hu
    exact sub_eq_zero.mpr (h ⟨u, hu⟩).eq
  have ha : a ∈ Submodule.span ℂ (unitary A : Set A) := by
    rw [CStarAlgebra.span_unitary]
    trivial
  exact sub_eq_zero.mp (hspan ha)

/-- The closed C-star algebra commuting with all real character multipliers. -/
def characterCommutant :
    StarSubalgebra ℂ (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  StarSubalgebra.centralizer ℂ (Set.range fun a : ℝ =>
    (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))

instance characterCommutantCStarAlgebra : CStarAlgebra (characterCommutant (H := H)) :=
  StarSubalgebra.cstarAlgebra _ (h_closed := Set.isClosed_centralizer _)

theorem mem_characterCommutant
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ a : ℝ, Commute T (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) :
    T ∈ characterCommutant := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  rintro _ ⟨a, rfl⟩
  refine ⟨(hT a).eq.symm, ?_⟩
  simpa only [regularCharacterUnitary_neg, Unitary.coe_star] using (hT (-a)).eq.symm

theorem characterCommutant_unitary_commutes
    (u : unitary (characterCommutant (H := H))) (a : ℝ) :
    Commute (((characterCommutant (H := H)).subtype u) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  (((StarSubalgebra.mem_centralizer_iff ℂ).mp u.val.property) _ ⟨a, rfl⟩).1.symm

theorem commute_scalarMultiplier_of_characters
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ a : ℝ, Commute T (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    Commute T (regularScalarMultiplier φ hφ C hC) := by
  apply commute_map_of_unitaries (characterCommutant (H := H)).subtype
    (regularScalarMultiplier φ hφ C hC) ?_ ⟨T, mem_characterCommutant T hT⟩
  intro u
  let v := Unitary.map (StarMonoidHom.ofClass (characterCommutant (H := H)).subtype) u
  exact unitary_commute_scalarMultiplier_of_characters v
    (characterCommutant_unitary_commutes u) φ hφ C hC

/-- The concrete real-line specialization of Stone's spectral commutant
theorem cited in the downstream regular-core construction. -/
theorem publishedRealSpectralCommutant : PublishedRealSpectralCommutant.{u} := by
  intro H _ _ _ T hT φ hφ C hC
  exact commute_scalarMultiplier_of_characters T hT φ hφ C hC

end

end KadisonKastler

end OAI
