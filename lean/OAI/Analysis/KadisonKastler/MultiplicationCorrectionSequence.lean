import OAI.Analysis.KadisonKastler.QuadraticMultiplicationCorrection
import OAI.Analysis.KadisonKastler.GeometricCorrectionScale

namespace OAI

/-! # Iterating the quadratic cochain correction

A cochain with unit complete bound and quadratic coboundary remainder
produces successive associative multiplications whose defects halve.
-/

namespace KadisonKastler

noncomputable section

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure SmallAssociativeProduct (q : ℝ) where
  mul : A →ₗ[ℂ] A →ₗ[ℂ] A
  assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  star_mul : ∀ x y, star (mul x y) = mul (star y) (star x)
  bound : HaagerupBound (mul - LinearMap.mul ℂ A) q

/-- The precise local cochain estimate used by the quadratic iteration. -/
def QuadraticCochainSolver : Prop :=
  ∀ q : ℝ, 0 ≤ q → q ≤ 1/11 → ∀ m : SmallAssociativeProduct A q,
    ∃ D : A →ₗ[ℂ] A, CompletelyBoundedBy D q ∧
      (∀ x, D (star x) = star (D x)) ∧
      HaagerupBound (m.mul - LinearMap.mul ℂ A - linearCoboundary D) (2 * q ^ 2)

variable {A}

theorem exists_halving_multiplication_sequence (hsolver : QuadraticCochainSolver A)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1/11) (m : SmallAssociativeProduct A q) :
    ∃ P : (n : ℕ) → SmallAssociativeProduct A (correctionScale q n),
      (P 0).mul = m.mul ∧ ∃ U : ℕ → A ≃ₗ[ℂ] A,
        (∀ n x, U n (star x) = star (U n x)) ∧
        (∀ n, CompletelyBoundedBy ((U n).toLinearMap - LinearMap.id) (correctionScale q n)) ∧
        (∀ n, (P (n+1)).mul = conjugatedBilinear (U n) (P n).mul) := by
  have move (n : ℕ) (p : SmallAssociativeProduct A (correctionScale q n)) :
      ∃ L : A ≃ₗ[ℂ] A,
        (∀ x, L (star x) = star (L x)) ∧
        CompletelyBoundedBy (L.toLinearMap - LinearMap.id) (correctionScale q n) ∧
        (∀ x y z, conjugatedBilinear L p.mul (conjugatedBilinear L p.mul x y) z =
          conjugatedBilinear L p.mul x (conjugatedBilinear L p.mul y z)) ∧
        (∀ x y, star (conjugatedBilinear L p.mul x y) =
          conjugatedBilinear L p.mul (star y) (star x)) ∧
        HaagerupBound (conjugatedBilinear L p.mul - LinearMap.mul ℂ A)
          (correctionScale q (n+1)) := by
    have hn := correctionScale_nonneg hq n
    have hn1 := (correctionScale_le hq n).trans hq1
    obtain ⟨D, hD, hDs, hres⟩ := hsolver _ hn hn1 p
    obtain ⟨L, _, hLs, hLc, hLa, hLst, hLb⟩ :=
      quadratic_multiplication_half_step p.mul p.assoc p.star_mul hn hn1 p.bound D hD hDs hres
    exact ⟨L, hLs, hLc, hLa, hLst, by simpa only [correctionScale_succ] using hLb⟩
  let next (n : ℕ) (p : SmallAssociativeProduct A (correctionScale q n)) :
      SmallAssociativeProduct A (correctionScale q (n+1)) :=
    { mul := conjugatedBilinear (Classical.choose (move n p)) p.mul
      assoc := (Classical.choose_spec (move n p)).2.2.1
      star_mul := (Classical.choose_spec (move n p)).2.2.2.1
      bound := (Classical.choose_spec (move n p)).2.2.2.2 }
  let initial : SmallAssociativeProduct A (correctionScale q 0) :=
    { mul := m.mul
      assoc := m.assoc
      star_mul := m.star_mul
      bound := by simpa only [correctionScale_zero] using m.bound }
  let P : (n : ℕ) → SmallAssociativeProduct A (correctionScale q n) :=
    fun n => Nat.rec initial (fun n p => next n p) n
  let U (n : ℕ) := Classical.choose (move n (P n))
  refine ⟨P, rfl, U, ?_, ?_, ?_⟩
  · intro n
    exact (Classical.choose_spec (move n (P n))).1
  · intro n
    exact (Classical.choose_spec (move n (P n))).2.1
  · intro n
    rfl

end

end KadisonKastler

end OAI
