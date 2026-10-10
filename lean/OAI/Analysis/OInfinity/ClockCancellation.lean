import OAI.Analysis.OInfinity.ClockCorrection

namespace OAI

/-! # The actual cancellation coefficients

These are the algebraic relations of the degree `0,1,-1` coefficients
of the existing cancellation path. They follow from the two orthogonal
isometries and the supplied unitary; no new path or unitarity hypothesis
is introduced for the clock-corrected expression.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- The sum of the two diagonal corner increments. -/
def clockCancellationIncrement (a b u : E) : E :=
  a * (u - 1) * star a + b * (star u - 1) * star b

/-- The positive-degree off-diagonal coefficient. -/
def clockCancellationCross (a b u : E) : E := a * (u - 1) * star b

/-- The constant coefficient of the cancellation polynomial. -/
def clockCancellationDiagonal (a b u : E) (τ : ℝ) : E :=
  1 + τ • clockCancellationIncrement a b u

private lemma clock_corner_mul (a b c x y : E) (hb : star b * b = 1) :
    (a * x * star b) * (b * y * star c) = a * (x * y) * star c := by
  calc
    _ = a * x * (star b * b) * y * star c := by noncomm_ring
    _ = _ := by rw [hb, mul_one]; noncomm_ring

private lemma clock_corner_zero (a b c d x y : E) (hbc : star b * c = 0) :
    (a * x * star b) * (c * y * star d) = 0 := by
  calc
    _ = a * x * (star b * c) * y * star d := by noncomm_ring
    _ = 0 := by rw [hbc, mul_zero, zero_mul, zero_mul]

lemma clockCancellationCross_star (a b u : E) :
    star (clockCancellationCross a b u) = b * (star u - 1) * star a := by
  simp only [clockCancellationCross, star_mul, star_sub, star_one, star_star, mul_assoc]

lemma clockCancellationCross_sq (a b u : E) (hab : star a * b = 0) :
    clockCancellationCross a b u * clockCancellationCross a b u = 0 := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  exact clock_corner_zero a b a b _ _ hba

lemma clockCancellationIncrement_star (a b u : E) :
    star (clockCancellationIncrement a b u) = clockCancellationIncrement a b (star u) := by
  simp only [clockCancellationIncrement, star_add, star_mul, star_sub,
    star_one, star_star, mul_assoc]

lemma clockCancellationIncrement_cross (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0) :
    clockCancellationIncrement a b u * clockCancellationCross a b u =
      clockCancellationCross a b u * star (clockCancellationIncrement a b u) := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  simp only [clockCancellationIncrement_star]
  simp only [clockCancellationIncrement, clockCancellationCross, add_mul, mul_add,
    clock_corner_mul a a b _ _ ha, clock_corner_mul a b b _ _ hb,
    clock_corner_zero b b a b _ _ hba, clock_corner_zero a b a a _ _ hba,
    star_star, zero_add, add_zero]

lemma clockCancellationIncrement_star_cross (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hu : u ∈ unitary E) :
    star (clockCancellationIncrement a b u) * clockCancellationCross a b u =
      clockCancellationCross a b u * clockCancellationIncrement a b u := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have hn : (star u - 1) * (u - 1) = (u - 1) * (star u - 1) := by
    noncomm_ring [hu.1, hu.2]
  simp only [clockCancellationIncrement_star]
  simp only [clockCancellationIncrement, clockCancellationCross, add_mul, mul_add,
    clock_corner_mul a a b _ _ ha, clock_corner_mul a b b _ _ hb,
    clock_corner_zero b b a b _ _ hba, clock_corner_zero a b a a _ _ hba,
    star_star, zero_add, add_zero, hn]

lemma clockCancellationIncrement_gram (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hu : u ∈ unitary E) :
    star (clockCancellationIncrement a b u) * clockCancellationIncrement a b u =
      star (clockCancellationCross a b u) * clockCancellationCross a b u +
        clockCancellationCross a b u * star (clockCancellationCross a b u) := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have hn : (star u - 1) * (u - 1) = (u - 1) * (star u - 1) := by
    noncomm_ring [hu.1, hu.2]
  simp only [clockCancellationIncrement_star, clockCancellationCross_star]
  simp only [clockCancellationIncrement, clockCancellationCross, add_mul, mul_add,
    clock_corner_mul a a a _ _ ha, clock_corner_mul b b b _ _ hb,
    clock_corner_mul b a b _ _ ha, clock_corner_mul a b a _ _ hb,
    clock_corner_zero a a b b _ _ hab, clock_corner_zero b b a a _ _ hba,
    star_star, zero_add, add_zero, hn]
  abel

lemma clockCancellationIncrement_normal (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hu : u ∈ unitary E) :
    star (clockCancellationIncrement a b u) * clockCancellationIncrement a b u =
      clockCancellationIncrement a b u * star (clockCancellationIncrement a b u) := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have hn : (star u - 1) * (u - 1) = (u - 1) * (star u - 1) := by
    noncomm_ring [hu.1, hu.2]
  simp only [clockCancellationIncrement_star]
  simp only [clockCancellationIncrement, add_mul, mul_add,
    clock_corner_mul a a a _ _ ha, clock_corner_mul b b b _ _ hb,
    clock_corner_zero a a b b _ _ hab, clock_corner_zero b b a a _ _ hba,
    star_star, zero_add, add_zero, hn]

lemma clockCancellationIncrement_identity (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hu : u ∈ unitary E) :
    clockCancellationIncrement a b u + star (clockCancellationIncrement a b u) +
      star (clockCancellationIncrement a b u) * clockCancellationIncrement a b u = 0 := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have hn : (star u - 1) * (u - 1) = -(u - 1) - (star u - 1) := by
    noncomm_ring [hu.1]
  have hn' : (u - 1) * (star u - 1) = -(star u - 1) - (u - 1) := by
    noncomm_ring [hu.2]
  simp only [clockCancellationIncrement_star]
  simp only [clockCancellationIncrement, add_mul, mul_add,
    clock_corner_mul a a a _ _ ha, clock_corner_mul b b b _ _ hb,
    clock_corner_zero a a b b _ _ hab, clock_corner_zero b b a a _ _ hba,
    star_star, zero_add, add_zero, hn, hn']
  noncomm_ring

lemma clockCancellationDiagonal_star_cross (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hu : u ∈ unitary E) (τ : ℝ) :
    star (clockCancellationDiagonal a b u τ) * clockCancellationCross a b u =
      clockCancellationCross a b u * clockCancellationDiagonal a b u τ := by
  simp only [clockCancellationDiagonal, star_add, star_one, star_smul, star_trivial,
    add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    clockCancellationIncrement_star_cross a b u ha hb hab hu]

lemma clockCancellationDiagonal_cross (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0) (τ : ℝ) :
    clockCancellationDiagonal a b u τ * clockCancellationCross a b u =
      clockCancellationCross a b u * star (clockCancellationDiagonal a b u τ) := by
  simp only [clockCancellationDiagonal, star_add, star_one, star_smul, star_trivial,
    add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    clockCancellationIncrement_cross a b u ha hb hab]

/-- The constant Gram coefficient is exactly one; the nonzero coefficients
cancel by the preceding cross relations and square-zero identity. -/
lemma clockCancellationDiagonal_gram (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hu : u ∈ unitary E) (τ ν : ℝ) (hτν : τ ^ 2 + ν ^ 2 = τ) :
    star (clockCancellationDiagonal a b u τ) * clockCancellationDiagonal a b u τ +
      (ν ^ 2) • (star (clockCancellationCross a b u) * clockCancellationCross a b u +
        clockCancellationCross a b u * star (clockCancellationCross a b u)) = 1 := by
  have hi := clockCancellationIncrement_identity a b u ha hb hab hu
  have hg := clockCancellationIncrement_gram a b u ha hb hab hu
  have hc : clockCancellationIncrement a b u + star (clockCancellationIncrement a b u) =
      -(star (clockCancellationIncrement a b u) * clockCancellationIncrement a b u) := by
    exact eq_neg_of_add_eq_zero_left hi
  simp only [clockCancellationDiagonal, star_add, star_one, star_smul, star_trivial,
    add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  rw [← hg]
  have hcoef : τ * τ + ν ^ 2 = τ := by nlinarith [hτν]
  calc
    _ = 1 + τ • (clockCancellationIncrement a b u + star (clockCancellationIncrement a b u)) +
        (τ * τ + ν ^ 2) •
          (star (clockCancellationIncrement a b u) * clockCancellationIncrement a b u) := by module
    _ = 1 := by rw [hc, hcoef]; module

lemma clockCancellationDiagonal_cogram (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hu : u ∈ unitary E) (τ ν : ℝ) (hτν : τ ^ 2 + ν ^ 2 = τ) :
    clockCancellationDiagonal a b u τ * star (clockCancellationDiagonal a b u τ) +
      (ν ^ 2) • (star (clockCancellationCross a b u) * clockCancellationCross a b u +
        clockCancellationCross a b u * star (clockCancellationCross a b u)) = 1 := by
  have hg := clockCancellationDiagonal_gram a b u ha hb hab hu τ ν hτν
  have hn := clockCancellationIncrement_normal a b u ha hb hab hu
  have hd : clockCancellationDiagonal a b u τ * star (clockCancellationDiagonal a b u τ) =
      star (clockCancellationDiagonal a b u τ) * clockCancellationDiagonal a b u τ := by
    simp only [clockCancellationDiagonal, star_add, star_one, star_smul, star_trivial,
      add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, ← hn]
    module
  rw [hd]
  exact hg

/-- The trigonometric parameters of the actual cancellation path satisfy
both constant-coefficient Gram identities. -/
lemma clockCancellation_actual_grams (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hu : u ∈ unitary E) (θ : ℝ) :
    (star (clockCancellationDiagonal a b u (Real.cos θ ^ 2)) *
      clockCancellationDiagonal a b u (Real.cos θ ^ 2) +
      (Real.sin θ * Real.cos θ) ^ 2 •
        (star (clockCancellationCross a b u) * clockCancellationCross a b u +
          clockCancellationCross a b u * star (clockCancellationCross a b u)) = 1) ∧
    (clockCancellationDiagonal a b u (Real.cos θ ^ 2) *
      star (clockCancellationDiagonal a b u (Real.cos θ ^ 2)) +
      (Real.sin θ * Real.cos θ) ^ 2 •
        (star (clockCancellationCross a b u) * clockCancellationCross a b u +
          clockCancellationCross a b u * star (clockCancellationCross a b u)) = 1) := by
  have h : (Real.cos θ ^ 2) ^ 2 + (Real.sin θ * Real.cos θ) ^ 2 = Real.cos θ ^ 2 := by
    have ht := congrArg (fun x : ℝ => x * Real.cos θ ^ 2) (Real.sin_sq_add_cos_sq θ)
    nlinarith [ht]
  exact ⟨clockCancellationDiagonal_gram a b u ha hb hab hu _ _ h,
    clockCancellationDiagonal_cogram a b u ha hb hab hu _ _ h⟩

/-- The three actual homogeneous degrees and coefficients. -/
def clockCancellationDegrees : Fin 3 → ℤ := ![0, 1, -1]

def clockCancellationCoefficients (a b u : E) (θ : ℝ) : Fin 3 → E :=
  ![clockCancellationDiagonal a b u (Real.cos θ ^ 2),
    (Real.sin θ * Real.cos θ) • clockCancellationCross a b u,
    -(Real.sin θ * Real.cos θ) • star (clockCancellationCross a b u)]

lemma clockCorrectedCancellation_eq_sum (k : unitary E) (a b u : E) (θ : ℝ) :
    clockCorrectedCancellation k a b u θ =
      ∑ i, clockDegreeCorrection k (clockCancellationDegrees i)
        (clockCancellationCoefficients a b u θ i) := by
  rw [Fin.sum_univ_three]
  change clockCorrectedCancellation k a b u θ =
    clockDegreeCorrection k 0 (clockCancellationDiagonal a b u (Real.cos θ ^ 2)) +
    clockDegreeCorrection k 1 ((Real.sin θ * Real.cos θ) • clockCancellationCross a b u) +
    clockDegreeCorrection k (-1) (-(Real.sin θ * Real.cos θ) • star (clockCancellationCross a b u))
  rw [clockDegreeCorrection_zero, clockCancellationCross_star]
  simp only [clockDegreeCorrection, mul_smul_comm, neg_smul, mul_neg,
    clockCancellationDiagonal, clockCancellationIncrement, clockCancellationCross,
    clockCorrectedCancellation]
  module


/-- The initial Gram polynomial vanishes in every nonzero degree. -/
lemma clockThreeTerm_initial_gram (k : unitary E) (D X : E) (ν : ℝ)
    (hX : X * X = 0) (hDX : star D * X = X * D)
    (hG : star D * D + ν ^ 2 • (star X * X + X * star X) = 1) :
    clockDegreeCorrection k 0 (star D * D) +
      clockDegreeCorrection k 1 (star D * (ν • X)) +
      clockDegreeCorrection k (-1) (star D * (-ν • star X)) +
      (clockDegreeCorrection k (-1) (star (ν • X) * D) +
       clockDegreeCorrection k 0 (star (ν • X) * (ν • X)) +
       clockDegreeCorrection k (-2) (star (ν • X) * (-ν • star X))) +
      (clockDegreeCorrection k 1 (star (-ν • star X) * D) +
       clockDegreeCorrection k 2 (star (-ν • star X) * (ν • X)) +
       clockDegreeCorrection k 0 (star (-ν • star X) * (-ν • star X))) = 1 := by
  have hXX : star X * star X = 0 := by
    simpa only [star_mul, star_zero] using congrArg star hX
  have hDX' : star X * D = star D * star X := by
    simpa only [star_mul, star_star] using congrArg star hDX
  simp only [clockDegreeCorrection, star_smul, star_trivial, star_star,
    smul_mul_assoc, mul_smul_comm, smul_smul, hDX, hDX', hX, hXX,
    smul_zero, mul_zero, neg_zero, zpow_zero, Submonoid.coe_one, one_mul]
  calc
    _ = star D * D + ν ^ 2 • (star X * X + X * star X) := by module
    _ = 1 := hG

/-- The final Gram polynomial has the same exact cancellation. -/
lemma clockThreeTerm_final_gram (k : unitary E) (D X : E) (ν : ℝ)
    (hX : X * X = 0) (hDX : D * X = X * star D)
    (hG : D * star D + ν ^ 2 • (star X * X + X * star X) = 1) :
    clockDegreeCorrection k 0 (D * star D) +
      clockDegreeCorrection k (-1) (D * star (ν • X)) +
      clockDegreeCorrection k 1 (D * star (-ν • star X)) +
      (clockDegreeCorrection k 1 ((ν • X) * star D) +
       clockDegreeCorrection k 0 ((ν • X) * star (ν • X)) +
       clockDegreeCorrection k 2 ((ν • X) * star (-ν • star X))) +
      (clockDegreeCorrection k (-1) ((-ν • star X) * star D) +
       clockDegreeCorrection k (-2) ((-ν • star X) * star (ν • X)) +
       clockDegreeCorrection k 0 ((-ν • star X) * star (-ν • star X))) = 1 := by
  have hXX : star X * star X = 0 := by
    simpa only [star_mul, star_zero] using congrArg star hX
  have hDX' : star X * star D = D * star X := by
    simpa only [star_mul, star_star] using congrArg star hDX
  simp only [clockDegreeCorrection, star_smul, star_trivial, star_star,
    smul_mul_assoc, mul_smul_comm, smul_smul, hDX, hDX', hX, hXX,
    smul_zero, mul_zero, neg_zero, zpow_zero, Submonoid.coe_one, one_mul]
  calc
    _ = D * star D + ν ^ 2 • (star X * X + X * star X) := by module
    _ = 1 := hG

/-- Exact initial and final convolution identities for the actual three
coefficients, before estimating the noncentral clock corrections. -/
lemma clockCancellation_convolution_grams (k : unitary E) (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hu : u ∈ unitary E) (θ : ℝ) :
    (∑ i, ∑ j, clockDegreeCorrection k
      (-clockCancellationDegrees i + clockCancellationDegrees j)
      (star (clockCancellationCoefficients a b u θ i) *
        clockCancellationCoefficients a b u θ j)) = 1 ∧
    (∑ i, ∑ j, clockDegreeCorrection k
      (clockCancellationDegrees i - clockCancellationDegrees j)
      (clockCancellationCoefficients a b u θ i *
        star (clockCancellationCoefficients a b u θ j))) = 1 := by
  have hg := clockCancellation_actual_grams a b u ha hb hab hu θ
  constructor
  · simpa [Fin.sum_univ_three, clockCancellationDegrees,
      clockCancellationCoefficients] using
      clockThreeTerm_initial_gram k
        (clockCancellationDiagonal a b u (Real.cos θ ^ 2))
        (clockCancellationCross a b u) (Real.sin θ * Real.cos θ)
        (clockCancellationCross_sq a b u hab)
        (clockCancellationDiagonal_star_cross a b u ha hb hab hu _) hg.1
  · simpa [Fin.sum_univ_three, clockCancellationDegrees,
      clockCancellationCoefficients] using
      clockThreeTerm_final_gram k
        (clockCancellationDiagonal a b u (Real.cos θ ^ 2))
        (clockCancellationCross a b u) (Real.sin θ * Real.cos θ)
        (clockCancellationCross_sq a b u hab)
        (clockCancellationDiagonal_cross a b u ha hb hab _) hg.2

end WeakPureInfiniteness

end

end OAI
