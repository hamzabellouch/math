import OAI.Analysis.KadisonKastler.PublishedSimpleDerivation
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Tactic.Module

namespace OAI

/-! # Reduction to anti-star derivations

Sakai's spatial construction treats derivations satisfying
`D (star x) = -star (D x)`. Every bounded complex derivation is a complex
linear combination of two such derivations. That decomposition transfers innerness from anti-star derivations
to arbitrary bounded complex derivations.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- A derivation vanishes on an idempotent which commutes with its image.
In particular it vanishes on every central projection. -/
theorem derivation_central_idempotent_eq_zero (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (p : A) (hp : p * p = p) (hc : Commute p (D p)) : D p = 0 := by
  have hleft : p * (D p * p) = p * D p := by
    calc
      p * (D p * p) = (p * D p) * p := (mul_assoc _ _ _).symm
      _ = (D p * p) * p := congrArg (fun a => a * p) hc.eq
      _ = D p * (p * p) := mul_assoc _ _ _
      _ = D p * p := by rw [hp]
      _ = p * D p := hc.eq.symm
  have hright : p * (p * D p) = p * D p := by rw [← mul_assoc, hp]
  have htwice : p * D p = p * D p + p * D p := by
    calc
      p * D p = p * D (p * p) := by rw [hp]
      _ = p * (D p * p + p * D p) := congrArg (fun a => p * a) (hD p p)
      _ = p * D p + p * D p := by rw [mul_add, hleft, hright]
  have hz : p * D p = 0 := by
    have h : p * D p + 0 = p * D p + p * D p := by simpa using htwice
    exact (add_left_cancel h).symm
  calc
    D p = D p * p + p * D p := by simpa only [hp] using hD p p
    _ = p * D p + p * D p := by rw [hc.eq]
    _ = 0 := by rw [hz, zero_add]

def starConjugateMap (D : A →L[ℂ] A) : A →L[ℂ] A where
  toFun x := star (D (star x))
  map_add' x y := by simp
  map_smul' c x := by simp
  cont := continuous_star.comp (D.continuous.comp continuous_star)

@[simp] theorem starConjugateMap_apply (D : A →L[ℂ] A) (x : A) :
    starConjugateMap D x = star (D (star x)) := rfl

theorem starConjugateMap_leibniz (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) :
    ∀ x y, starConjugateMap D (x * y) =
      starConjugateMap D x * y + x * starConjugateMap D y := by
  intro x y
  simp only [starConjugateMap_apply, star_mul, hD, star_add, star_star]
  exact add_comm _ _

private theorem leibniz_combination (D E : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hE : ∀ x y, E (x * y) = E x * y + x * E y) (c d : ℂ) :
    ∀ x y, (c • D + d • E) (x * y) =
      (c • D + d • E) x * y + x * (c • D + d • E) y := by
  intro x y
  simp only [add_apply, smul_apply,
    hD, hE, smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  abel

theorem exists_antiStar_derivation_decomposition (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) :
    ∃ F G : A →L[ℂ] A,
      (∀ x y, F (x * y) = F x * y + x * F y) ∧
      (∀ x, F (star x) = -star (F x)) ∧
      (∀ x y, G (x * y) = G x * y + x * G y) ∧
      (∀ x, G (star x) = -star (G x)) ∧
      ∀ x, D x = F x + Complex.I • G x := by
  let E := starConjugateMap D
  let F : A →L[ℂ] A := (1 / 2 : ℂ) • D + (-1 / 2 : ℂ) • E
  let G : A →L[ℂ] A := (-Complex.I / 2 : ℂ) • D + (-Complex.I / 2 : ℂ) • E
  have hE := starConjugateMap_leibniz D hD
  refine ⟨F, G, leibniz_combination D E hD hE _ _, ?_,
    leibniz_combination D E hD hE _ _, ?_, ?_⟩
  · intro x
    simp [F, E, star_smul, star_add, star_star]
    module
  · intro x
    simp [G, E, star_smul, star_add, star_star]
    module
  · intro x
    simp only [F, G, add_apply, smul_apply,
      smul_add, smul_smul]
    have hi : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
      calc
        Complex.I * (-Complex.I / 2) = -(Complex.I ^ 2) / 2 := by ring
        _ = 1 / 2 := by rw [Complex.I_sq]; norm_num
    simp only [hi]
    module

theorem inner_derivation_of_antiStar_inner
    (hInner : ∀ F : A →L[ℂ] A,
      (∀ x y, F (x * y) = F x * y + x * F y) →
      (∀ x, F (star x) = -star (F x)) →
      ∃ a : A, ∀ x, F x = a * x - x * a)
    (D : A →L[ℂ] A) (hD : ∀ x y, D (x * y) = D x * y + x * D y) :
    ∃ a : A, ∀ x, D x = a * x - x * a := by
  obtain ⟨F, G, hF, hFs, hG, hGs, hsum⟩ := exists_antiStar_derivation_decomposition D hD
  obtain ⟨a, ha⟩ := hInner F hF hFs
  obtain ⟨b, hb⟩ := hInner G hG hGs
  refine ⟨a + Complex.I • b, fun x => ?_⟩
  rw [hsum, ha, hb]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

end

end KadisonKastler

end OAI
