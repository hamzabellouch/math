import OAI.Analysis.KadisonKastler.Jordan
import OAI.Analysis.KadisonKastler.Multiplication
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Quantitative exclusion of the reversed Jordan orientation

The calculation in §5 of *Universal strong Kadison–Kastler stability*
excludes an antihomomorphism that is sufficiently close to the inclusion.
Closeness alone gives a `3e + e²` estimate; contractivity improves it to `3e`.
The applications to Jordan maps keep the embeddings in the common ambient
algebra explicit.
-/

namespace KadisonKastler

variable {A B D : Type*}
  [NormedRing A] [NormedAlgebra ℂ A]
  [NormedRing B] [NormedAlgebra ℂ B]
  [NormedRing D] [NormedAlgebra ℂ D]

/-- The three error terms controlling a commutator under an
antimultiplicative map close to an isometric representation. -/
theorem commutator_norm_le_three_terms
    (ι : A →ₐ[ℂ] D) (F : A →ₗ[ℂ] D) {e : ℝ}
    (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (hclose : ∀ x, ‖F x - ι x‖ ≤ e * ‖x‖)
    (hanti : ∀ x y, F (x * y) = F y * F x) (a b : A) :
    ‖a * b - b * a‖ ≤
      e * ‖a * b‖ + (e * ‖b‖) * ‖F a‖ + ‖b‖ * (e * ‖a‖) := by
  have hexpand : ι (a * b - b * a) =
      (ι (a * b) - F (a * b)) + (F b - ι b) * F a + ι b * (F a - ι a) := by
    simp only [map_sub, map_mul, hanti]
    noncomm_ring
  calc
    ‖a * b - b * a‖ = ‖ι (a * b - b * a)‖ := (hι _).symm
    _ = ‖(ι (a * b) - F (a * b)) + (F b - ι b) * F a +
        ι b * (F a - ι a)‖ := by rw [hexpand]
    _ ≤ ‖ι (a * b) - F (a * b)‖ + ‖(F b - ι b) * F a‖ +
        ‖ι b * (F a - ι a)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ e * ‖a * b‖ + (e * ‖b‖) * ‖F a‖ + ‖b‖ * (e * ‖a‖) := by
      apply add_le_add
      · apply add_le_add
        · simpa only [norm_sub_rev] using hclose (a * b)
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hclose b) (norm_nonneg _))
      · exact (norm_mul_le _ _).trans (by
          rw [hι b]
          exact mul_le_mul_of_nonneg_left (hclose a) (norm_nonneg b))

/-- An antimultiplicative contraction close to an isometric representation
forces every commutator to be small. -/
theorem commutator_norm_le_of_close_antimultiplicative
    (ι : A →ₐ[ℂ] D) (F : A →ₗ[ℂ] D) {e : ℝ} (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖) (hF : ∀ x, ‖F x‖ ≤ ‖x‖)
    (hclose : ∀ x, ‖F x - ι x‖ ≤ e * ‖x‖)
    (hanti : ∀ x y, F (x * y) = F y * F x) (a b : A) :
    ‖a * b - b * a‖ ≤ 3 * e * ‖a‖ * ‖b‖ := by
  calc
    ‖a * b - b * a‖ ≤
        e * ‖a * b‖ + (e * ‖b‖) * ‖F a‖ + ‖b‖ * (e * ‖a‖) :=
      commutator_norm_le_three_terms ι F hι hclose hanti a b
    _ ≤ e * (‖a‖ * ‖b‖) + (e * ‖b‖) * ‖a‖ + ‖b‖ * (e * ‖a‖) := by
      apply add_le_add _ le_rfl
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_mul_le a b) he)
        (mul_le_mul_of_nonneg_left (hF a) (mul_nonneg he (norm_nonneg b)))
    _ = 3 * e * ‖a‖ * ‖b‖ := by ring

/-- Closeness alone controls an antimultiplicative map's commutators;
contractivity is not assumed. -/
theorem commutator_norm_le_of_close_antimultiplicative_without_contractivity
    (ι : A →ₐ[ℂ] D) (F : A →ₗ[ℂ] D) {e : ℝ} (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (hclose : ∀ x, ‖F x - ι x‖ ≤ e * ‖x‖)
    (hanti : ∀ x y, F (x * y) = F y * F x) (a b : A) :
    ‖a * b - b * a‖ ≤ (3 * e + e ^ 2) * ‖a‖ * ‖b‖ := by
  calc
    ‖a * b - b * a‖ ≤
        e * ‖a * b‖ + (e * ‖b‖) * ‖F a‖ + ‖b‖ * (e * ‖a‖) :=
      commutator_norm_le_three_terms ι F hι hclose hanti a b
    _ ≤ e * (‖a‖ * ‖b‖) + (e * ‖b‖) * ((1 + e) * ‖a‖) +
        ‖b‖ * (e * ‖a‖) := by
      apply add_le_add _ le_rfl
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_mul_le a b) he)
        (mul_le_mul_of_nonneg_left (norm_image_le_of_close_to_isometric_hom ι F hι hclose a)
          (mul_nonneg he (norm_nonneg b)))
    _ = (3 * e + e ^ 2) * ‖a‖ * ‖b‖ := by ring

/-- A norm-two commutator of contractions rules out the reversed orientation
when `3 * e < 2`. -/
theorem not_antimultiplicative_of_norm_two_commutator
    (ι : A →ₐ[ℂ] D) (F : A →ₗ[ℂ] D) {e : ℝ} (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖) (hF : ∀ x, ‖F x‖ ≤ ‖x‖)
    (hclose : ∀ x, ‖F x - ι x‖ ≤ e * ‖x‖)
    (a b : A) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ‖a * b - b * a‖ = 2) (hsmall : 3 * e < 2) :
    ¬ ∀ x y, F (x * y) = F y * F x := by
  intro hanti
  have hbound := commutator_norm_le_of_close_antimultiplicative ι F he hι hF hclose hanti a b
  rw [hab, ha, hb, mul_one, mul_one] at hbound
  exact (not_le_of_gt hsmall) hbound

/-- A norm-two commutator excludes a close antihomomorphism without
contractivity, using the slightly smaller tolerance `3e + e² < 2`. -/
theorem not_antimultiplicative_of_norm_two_commutator_without_contractivity
    (ι : A →ₐ[ℂ] D) (F : A →ₗ[ℂ] D) {e : ℝ} (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (hclose : ∀ x, ‖F x - ι x‖ ≤ e * ‖x‖)
    (a b : A) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ‖a * b - b * a‖ = 2) (hsmall : 3 * e + e ^ 2 < 2) :
    ¬ ∀ x y, F (x * y) = F y * F x := by
  intro hanti
  have hbound := commutator_norm_le_of_close_antimultiplicative_without_contractivity
    ι F he hι hclose hanti a b
  rw [hab, ha, hb, mul_one, mul_one] at hbound
  exact (not_le_of_gt hsmall) hbound

/-- A sufficiently close surjective Jordan contraction into a prime algebra
has the multiplicative orientation. Closeness is measured after representing
the source and target in the same ambient normed algebra. -/
theorem PreservesJordan.multiplicative_of_close
    (θ : A →ₗ[ℂ] B) (ι : A →ₐ[ℂ] D) (κ : B →ₐ[ℂ] D) {e : ℝ}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ)
    (hprime : IsPrimeAlgebra B) (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖) (hκ : ∀ x, ‖κ x‖ = ‖x‖)
    (hcontractive : ∀ x, ‖θ x‖ ≤ ‖x‖)
    (hclose : ∀ x, ‖κ (θ x) - ι x‖ ≤ e * ‖x‖)
    (a b : A) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ‖a * b - b * a‖ = 2) (hsmall : 3 * e < 2) :
    ∀ x y, θ (x * y) = θ x * θ y := by
  rcases hθ.multiplicative_or_antimultiplicative hsurj hprime with hmult | hanti
  · exact hmult
  · exfalso
    apply not_antimultiplicative_of_norm_two_commutator ι (κ.toLinearMap.comp θ)
      he hι (fun x => (hκ (θ x)).trans_le (hcontractive x)) hclose a b ha hb hab hsmall
    intro x y
    change κ (θ (x * y)) = κ (θ y) * κ (θ x)
    rw [hanti, map_mul]

/-- The multiplicative orientation follows from closeness alone, with no
contractivity assumption on the Jordan map. -/
theorem PreservesJordan.multiplicative_of_close_without_contractivity
    (θ : A →ₗ[ℂ] B) (ι : A →ₐ[ℂ] D) (κ : B →ₐ[ℂ] D) {e : ℝ}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ)
    (hprime : IsPrimeAlgebra B) (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (hclose : ∀ x, ‖κ (θ x) - ι x‖ ≤ e * ‖x‖)
    (a b : A) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ‖a * b - b * a‖ = 2) (hsmall : 3 * e + e ^ 2 < 2) :
    ∀ x y, θ (x * y) = θ x * θ y := by
  rcases hθ.multiplicative_or_antimultiplicative hsurj hprime with hmult | hanti
  · exact hmult
  · exfalso
    apply not_antimultiplicative_of_norm_two_commutator_without_contractivity
      ι (κ.toLinearMap.comp θ) he hι hclose a b ha hb hab hsmall
    intro x y
    change κ (θ (x * y)) = κ (θ y) * κ (θ x)
    rw [hanti, map_mul]

section CStar

variable [StarRing A] [CStarRing A] [Nontrivial A]

/-- Anticommuting unitaries have a commutator of norm two. In particular this
applies to the selfadjoint anticommuting unitaries in a unital matrix algebra. -/
theorem norm_commutator_of_anticommuting_unitaries (a b : unitary A)
    (hab : (a : A) * (b : A) = -((b : A) * (a : A))) :
    ‖(a : A) * (b : A) - (b : A) * (a : A)‖ = 2 := by
  have hrewrite : (a : A) * (b : A) - (b : A) * (a : A) =
      (2 : ℂ) • ((a : A) * (b : A)) := by
    rw [two_smul, hab]
    abel
  rw [hrewrite, norm_smul, CStarRing.norm_coe_unitary_mul, CStarRing.norm_coe_unitary]
  simp

/-- The form used in the finite-factor argument: a pair of anticommuting
unitaries forces the nearby Jordan map to have multiplicative orientation. -/
theorem PreservesJordan.multiplicative_of_close_of_anticommuting_unitaries
    (θ : A →ₗ[ℂ] B) (ι : A →ₐ[ℂ] D) (κ : B →ₐ[ℂ] D) {e : ℝ}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ)
    (hprime : IsPrimeAlgebra B) (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖) (hκ : ∀ x, ‖κ x‖ = ‖x‖)
    (hcontractive : ∀ x, ‖θ x‖ ≤ ‖x‖)
    (hclose : ∀ x, ‖κ (θ x) - ι x‖ ≤ e * ‖x‖)
    (a b : unitary A) (hab : (a : A) * (b : A) = -((b : A) * (a : A)))
    (hsmall : 3 * e < 2) : ∀ x y, θ (x * y) = θ x * θ y := by
  exact PreservesJordan.multiplicative_of_close θ ι κ hθ hsurj hprime he hι hκ
    hcontractive hclose a b (CStarRing.norm_coe_unitary a) (CStarRing.norm_coe_unitary b)
    (norm_commutator_of_anticommuting_unitaries a b hab) hsmall

/-- The finite-factor orientation step using only closeness and a pair of
anticommuting unitaries, before any contractivity conclusion is available. -/
theorem PreservesJordan.multiplicative_of_close_of_anticommuting_unitaries_without_contractivity
    (θ : A →ₗ[ℂ] B) (ι : A →ₐ[ℂ] D) (κ : B →ₐ[ℂ] D) {e : ℝ}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ)
    (hprime : IsPrimeAlgebra B) (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (hclose : ∀ x, ‖κ (θ x) - ι x‖ ≤ e * ‖x‖)
    (a b : unitary A) (hab : (a : A) * (b : A) = -((b : A) * (a : A)))
    (hsmall : 3 * e + e ^ 2 < 2) : ∀ x y, θ (x * y) = θ x * θ y := by
  exact PreservesJordan.multiplicative_of_close_without_contractivity θ ι κ hθ hsurj hprime
    he hι hclose a b (CStarRing.norm_coe_unitary a) (CStarRing.norm_coe_unitary b)
    (norm_commutator_of_anticommuting_unitaries a b hab) hsmall

end CStar

end KadisonKastler

end OAI
