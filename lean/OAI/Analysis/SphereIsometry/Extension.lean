import OAI.Analysis.SphereIsometry.DefectAttainment
import OAI.Analysis.SphereIsometry.Alignment
import OAI.Analysis.SphereIsometry.ChordContradiction
import OAI.Analysis.SphereIsometry.RadialExtension

namespace OAI

/-!
# The unique real-linear extension of an onto sphere isometry

The intermediate hypotheses of the separate constructions are discharged here:
positive original defect produces an actual attained defect in completed normed
quotients, alignment produces actual opposite chords, and the chord theorem
rules them out. The original radial extension consequently preserves distance.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem no_attained_positive_defect
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (t M : ℝ)
    (ht : 0 < t ∧ t < 1) (hM : 0 < M) (hb : HasDefectBound f M)
    (x y : UnitSphere X) (hatt : signedDefect f t x y = M) : False := by
  obtain ⟨C⟩ := exists_alignedConfiguration f y x t M ht hM hb hatt
  exact alignedConfiguration_impossible hM ht hb C

variable [Nontrivial X] [Nontrivial Y]

theorem maxDefect_eq_zero
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [Nontrivial X] [Nontrivial Y]
    (f : UnitSphere X ≃ᵢ UnitSphere Y) : maxDefect f = 0 := by
  apply le_antisymm ?_ (maxDefect_nonneg f)
  by_contra hn
  have hM : 0 < maxDefect f := lt_of_not_ge hn
  obtain ⟨hb, hi, t, ht, ha⟩ := positive_maxDefect_attained_or_inverse f hM
  rcases ha with ⟨x, y, hxy⟩ | ⟨x, y, hxy⟩
  · exact no_attained_positive_defect _ t (maxDefect f) ⟨ht.1, ht.2⟩ hM hb x y hxy
  · exact no_attained_positive_defect _ t (maxDefect f) ⟨ht.1, ht.2⟩ hM hi x y hxy

theorem hasDefectBound_zero (f : UnitSphere X ≃ᵢ UnitSphere Y) : HasDefectBound f 0 := by
  simpa only [maxDefect_eq_zero] using hasDefectBound_maxDefect f

theorem existsUnique_linearIsometryEquiv
    (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    ∃! T : X ≃ₗᵢ[ℝ] Y, ∀ x : UnitSphere X, T (x : X) = (f x : Y) := by
  exact existsUnique_linearIsometryEquiv_of_zero_defect f (hasDefectBound_zero f)

/-- The actual unconditional extension, with the original radial function. -/
def extension (f : UnitSphere X ≃ᵢ UnitSphere Y) : X ≃ₗᵢ[ℝ] Y :=
  radialLinearIsometryEquiv f (hasDefectBound_zero f)

@[simp] theorem extension_apply (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : X) :
    extension f x = radialExtension f x := rfl

@[simp] theorem extension_zero (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    extension f 0 = 0 := radialExtension_zero f

@[simp] theorem extension_unit (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : UnitSphere X) :
    extension f (x : X) = (f x : Y) := radialExtension_unit f x

theorem extension_radial (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : X) (hx : x ≠ 0) :
    extension f x = ‖x‖ • (f (normalize x hx) : Y) :=
  radialExtension_of_ne_zero f x hx

theorem extension_surjective (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    Function.Surjective (extension f) := (extension f).surjective

theorem extension_unique (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (L : X →ₗ[ℝ] Y) (hL : ∀ x : UnitSphere X, L (x : X) = (f x : Y)) :
    L = (extension f).toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact linear_extension_eq_radial f L hL x

/-- An ordinary onto sphere isometry is a genuine sphere isometry equivalence. -/
def sphereIsometryEquiv (f : UnitSphere X → UnitSphere Y)
    (hf : Isometry f) (hs : Function.Surjective f) : UnitSphere X ≃ᵢ UnitSphere Y where
  toEquiv := Equiv.ofBijective f ⟨hf.injective, hs⟩
  isometry_toFun := hf

/-- Every onto isometry of unit spheres extends uniquely to a real-linear isometry. -/
theorem tingley_sphere_isometry
    (f : UnitSphere X → UnitSphere Y) (hf : Isometry f) (hs : Function.Surjective f) :
    ∃! T : X ≃ₗᵢ[ℝ] Y, ∀ x : UnitSphere X, T (x : X) = (f x : Y) := by
  exact existsUnique_linearIsometryEquiv (sphereIsometryEquiv f hf hs)

/-- Radial formula, surjectivity, and uniqueness among all real-linear extensions. -/
theorem tingley_sphere_isometry_full
    (f : UnitSphere X → UnitSphere Y) (hf : Isometry f) (hs : Function.Surjective f) :
    ∃ T : X ≃ₗᵢ[ℝ] Y,
      (∀ u : UnitSphere X, T (u : X) = (f u : Y)) ∧
      T 0 = 0 ∧
      (∀ x : X, ∀ hx : x ≠ 0, T x = ‖x‖ • (f (normalize x hx) : Y)) ∧
      Function.Surjective T ∧
      (∀ L : X →ₗ[ℝ] Y, (∀ u : UnitSphere X, L (u : X) = (f u : Y)) →
        L = T.toLinearEquiv.toLinearMap) := by
  let e := sphereIsometryEquiv f hf hs
  refine ⟨extension e, extension_unit e, extension_zero e,
    extension_radial e, extension_surjective e, ?_⟩
  intro L hL
  exact extension_unique e L hL

end Tingley

end

end OAI
