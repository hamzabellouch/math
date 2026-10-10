import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.KadisonKastler.Haagerup
import OAI.Analysis.KadisonKastler.MatrixCorrection

namespace OAI

/-!
# The published multiplication-correction input

`PublishedMultiplicationCorrection` is the application of Ricard--Roydor,
*A non-commutative Amir--Cambern theorem for von Neumann algebras and
nuclear C*-algebras*, J. Funct. Anal. 267 (2014), Proposition 3.2
(arXiv:1108.1970v2), to associative, involution-compatible products on a
concrete von Neumann algebra. It is an explicit hypothesis, not an axiom.

The downstream theorem constructs the corrected star-algebra equivalence
and proves the `32e` complete bound. Surjectivity of the original map and
spatial implementation are treated separately.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- The precise published input used for correction. No normality is
required of the perturbed multiplication or of the correcting map. -/
def PublishedMultiplicationCorrection (M : VonNeumannAlgebra H) : Prop :=
  ∀ m : Algebra M →ₗ[ℂ] Algebra M →ₗ[ℂ] Algebra M,
    (∀ x y z, m (m x y) z = m x (m y z)) →
    (∀ x y, star (m x y) = m (star y) (star x)) →
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 / 11 →
      HaagerupBound (m - LinearMap.mul ℂ (Algebra M)) q →
      ∃ L : Algebra M ≃ₗ[ℂ] Algebra M,
        (∀ x y, L (m x y) = L x * L y) ∧
        (∀ x, L (star x) = star (L x)) ∧
        CompletelyBoundedBy (L.toLinearMap - LinearMap.id) (10 * q)

variable {B C : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder B] [StarOrderedRing B] in
theorem linear_correction_of_published (M : VonNeumannAlgebra H)
    (hPublished : PublishedMultiplicationCorrection M)
    (F : Algebra M ≃ₗ[ℂ] B) (hFstar : ∀ x, F (star x) = star (F x))
    {q : ℝ} (hq₀ : 0 ≤ q) (hq : q ≤ 1 / 11)
    (hdefect : TransportedProductBound F q) :
    ∃ L : Algebra M ≃ₗ[ℂ] Algebra M,
      (∀ x y, L (transportedMul F x y) = L x * L y) ∧
      (∀ x, L (star x) = star (L x)) ∧
      CompletelyBoundedBy (L.toLinearMap - LinearMap.id) (10 * q) := by
  exact hPublished (transportedBilinear F) (transportedBilinear_assoc F)
    (transportedBilinear_star F hFstar) q hq₀ hq
    ((haagerupBound_transported_defect_iff F q).mpr hdefect)

/-- The algebraic-isomorphism part of the UCP criterion, conditional only
on the published correction theorem. Complete contractivity and the linear
equivalence are explicit here; later steps supply them from positivity and
the reverse unit-ball gap. -/
theorem corrected_equivalence_of_published (M : VonNeumannAlgebra H)
    (hPublished : PublishedMultiplicationCorrection M)
    (F : Algebra M ≃ₗ[ℂ] B) (ρ : Algebra M →ₐ[ℂ] C) (ι : B →ₐ[ℂ] C)
    (hFstar : ∀ x, F (star x) = star (F x))
    {e : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000)
    (hρ : CompletelyIsometric ρ.toLinearMap)
    (hι : CompletelyIsometric ι.toLinearMap)
    (hF : CompletelyBoundedBy F.toLinearMap 1)
    (hclose : CompletelyBoundedBy (ι.toLinearMap.comp F.toLinearMap - ρ.toLinearMap) e) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] B,
      CompletelyBoundedBy (ι.toLinearMap.comp θ.toAlgEquiv.toLinearMap - ρ.toLinearMap)
        (32 * e) := by
  have he2 : e < 1 := by linarith
  have hden : 0 < 1 - e := sub_pos.mpr he2
  have hq₀ : 0 ≤ 3 * e / (1 - e) := div_nonneg (by positivity) hden.le
  have hq : 3 * e / (1 - e) ≤ 1 / 11 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hFambient : CompletelyBoundedBy (ι.toLinearMap.comp F.toLinearMap) 1 := by
    intro p q X
    rw [matrix_map_comp, hι p q]
    exact hF p q X
  have hdefect : ∀ (p r q : ℕ) (X : CStarMatrix (Fin p) (Fin r) (Algebra M))
      (Y : CStarMatrix (Fin r) (Fin q) (Algebra M)),
      ‖CStarMatrix.mapₗ F.toLinearMap (X * Y) -
          CStarMatrix.mapₗ F.toLinearMap X * CStarMatrix.mapₗ F.toLinearMap Y‖ ≤
        3 * e * ‖X‖ * ‖Y‖ := by
    intro p r q X Y
    calc
      _ = ‖CStarMatrix.mapₗ ι.toLinearMap
          (CStarMatrix.mapₗ F.toLinearMap (X * Y) -
            CStarMatrix.mapₗ F.toLinearMap X * CStarMatrix.mapₗ F.toLinearMap Y)‖ :=
        (hι p q _).symm
      _ = ‖CStarMatrix.mapₗ (ι.toLinearMap.comp F.toLinearMap) (X * Y) -
          CStarMatrix.mapₗ (ι.toLinearMap.comp F.toLinearMap) X *
            CStarMatrix.mapₗ (ι.toLinearMap.comp F.toLinearMap) Y‖ := by
        rw [map_sub, matrix_map_mul, ← matrix_map_comp, ← matrix_map_comp,
          ← matrix_map_comp]
      _ ≤ 3 * e * ‖X‖ * ‖Y‖ :=
        matrix_multiplicative_defect_le ρ _ he hρ hFambient hclose X Y
  have hinv := inverse_completelyBoundedBy_of_close_isometries F
    ρ.toLinearMap ι.toLinearMap he2 hρ hι hclose
  have htransport := transportedProductBound_of_defect F (inv_nonneg.mpr hden.le)
    hinv hdefect
  have htransport' : TransportedProductBound F (3 * e / (1 - e)) := by
    convert htransport using 1; ring
  obtain ⟨L, hLmul, hLstar, hLbound⟩ :=
    linear_correction_of_published M hPublished F hFstar hq₀ hq htransport'
  have hLbound' : CompletelyBoundedBy (L.toLinearMap - LinearMap.id)
      (30 * e / (1 - e)) := by
    convert hLbound using 1; ring
  refine ⟨correctedStarAlgEquiv F L hLmul hFstar hLstar, ?_⟩
  exact correctedMap_completelyBoundedBy_thirty_two_mul F L ρ.toLinearMap ι.toLinearMap
    he he₁ hι hF hclose hLbound'

end

end KadisonKastler

end OAI
