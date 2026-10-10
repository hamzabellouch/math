import OAI.Probability.DilutedSpin.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

/-- A finite conditional path law. Used only for the finite-kernel proof steps. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)

noncomputable def expect (f : Ω → ℝ) : ℝ := ∑ x, P.weight x * f x

@[simp] theorem expect_const (c : ℝ) : P.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, P.total]

@[simp] theorem expect_add (f g : Ω → ℝ) :
    P.expect (fun x => f x + g x) = P.expect f + P.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

@[simp] theorem expect_sub (f g : Ω → ℝ) :
    P.expect (fun x => f x - g x) = P.expect f - P.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem expect_mul_left (c : ℝ) (f : Ω → ℝ) :
    P.expect (fun x => c * f x) = c * P.expect f := by
  simp [expect, ← Finset.mul_sum, mul_left_comm]

@[simp] theorem expect_mul_right (f : Ω → ℝ) (c : ℝ) :
    P.expect (fun x => f x * c) = P.expect f * c := by
  simp only [expect, Finset.sum_mul, mul_assoc]

@[simp] theorem expect_div (f : Ω → ℝ) (c : ℝ) :
    P.expect (fun x => f x / c) = P.expect f / c := by
  simp [div_eq_mul_inv]

@[simp] theorem expect_neg (f : Ω → ℝ) :
    P.expect (fun x => -f x) = -P.expect f := by
  simp only [expect, mul_neg, Finset.sum_neg_distrib]

@[simp] theorem expect_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    P.expect (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, P.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

-- Finset.sum one-binder version, deliberately avoiding simp's double-binder notation.
theorem expect_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    P.expect (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, P.expect (f i) :=
  P.expect_sum s f

@[simp] theorem expect_fintype_sum {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    P.expect (fun x => ∑ i, f i x) = ∑ i, P.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_congr {f g : Ω → ℝ} (h : ∀ x, f x = g x) : P.expect f = P.expect g := by
  exact congrArg P.expect (funext h)

theorem expect_nonneg {f : Ω → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ P.expect f := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (P.nonneg x) (h x))

theorem expect_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : P.expect f ≤ P.expect g := by
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x))

noncomputable def covariance (f g : Ω → ℝ) : ℝ :=
  P.expect (fun x => f x * g x) - P.expect f * P.expect g

theorem covariance_centered (f g : Ω → ℝ) :
    P.covariance f g = P.expect (fun x => (f x - P.expect f) * (g x - P.expect g)) := by
  rw [covariance]
  calc
    _ = P.expect (fun x => f x * g x - f x * P.expect g -
        P.expect f * g x + P.expect f * P.expect g) := by simp
    _ = _ := P.expect_congr (fun x => by ring)

/-- Two independent centered copies have second moment twice the covariance. -/
theorem difference_product (f g : Ω → ℝ) :
    P.expect (fun y => P.expect (fun z => (f y - f z) * (g y - g z))) =
      2 * P.covariance f g := by
  calc
    _ = P.expect (fun y => P.expect (fun z =>
        f y * g y - f y * g z - f z * g y + f z * g z)) := by
          apply P.expect_congr
          intro y
          exact P.expect_congr (fun z => by ring)
    _ = _ := by simp [covariance]; ring

/-- The normalized site contraction used in sections/decorrelation.tex. -/
noncomputable def dot {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (∑ i, x i * y i) / n

variable {n : ℕ}

theorem dot_sub_right (x y z : Fin n → ℝ) :
    dot x y - dot x z = dot x (fun i => y i - z i) := by
  simp [dot, mul_sub, Finset.sum_sub_distrib, sub_div]

theorem dot_sq (x y : Fin n → ℝ) :
    dot x y ^ 2 = (∑ i, ∑ j, x i * x j * (y i * y j)) / (n : ℝ)^2 := by
  rw [dot, div_pow, pow_two, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact finite-conditional-law three-copy identity, with a square remainder.
No boundedness assumption is needed for this algebraic ingredient. -/
theorem three_copy_identity (X : Ω → Fin n → ℝ) :
    P.expect (fun x => P.expect (fun y => P.expect (fun z =>
      (dot (X x) (X y) - dot (X x) (X z))^2))) =
    (2 / (n : ℝ)^2) *
      ((∑ i, ∑ j, P.covariance (fun x => X x i) (fun x => X x j)^2) +
        P.expect (fun x => (∑ i, P.expect (fun y => X y i) *
          (X x i - P.expect (fun y => X y i)))^2)) := by
  let μ : Fin n → ℝ := fun i => P.expect (fun x => X x i)
  let C : Fin n → Fin n → ℝ := fun i j =>
    P.covariance (fun x => X x i) (fun x => X x j)
  have hrem : P.expect (fun x => (∑ i, μ i * (X x i - μ i))^2) =
      ∑ i, ∑ j, μ i * μ j * C i j := by
    have hsq (x : Ω) : (∑ i, μ i * (X x i - μ i))^2 =
        ∑ i, ∑ j, μ i * μ j * ((X x i - μ i) * (X x j - μ j)) := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [hsq, expect_fintype_sum, expect_mul_left]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [C, μ]
    rw [covariance_centered]
  have hmain : P.expect (fun x => P.expect (fun y => P.expect (fun z =>
      (dot (X x) (X y) - dot (X x) (X z))^2))) =
      (∑ i, ∑ j, 2 * (C i j + μ i * μ j) * C i j) / (n : ℝ)^2 := by
    simp_rw [dot_sub_right, dot_sq, expect_div, expect_fintype_sum,
      expect_mul_left, difference_product, expect_mul_right]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [C, covariance, μ]
    ring
  rw [hmain]
  change _ = (2 / (n : ℝ)^2) * ((∑ i, ∑ j, C i j ^ 2) + _)
  rw [hrem, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  rw [div_mul_eq_mul_div, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- decor:three-copy-bound for each finite conditional path law. -/
theorem three_copy_bound (X : Ω → Fin n → ℝ) :
    (2 / (n : ℝ)^2) *
      (∑ i, ∑ j, P.covariance (fun x => X x i) (fun x => X x j)^2) ≤
    P.expect (fun x => P.expect (fun y => P.expect (fun z =>
      (dot (X x) (X y) - dot (X x) (X z))^2))) := by
  rw [P.three_copy_identity X]
  apply mul_le_mul_of_nonneg_left
  · exact le_add_of_nonneg_right (P.expect_nonneg (fun _ => sq_nonneg _))
  · positivity

/-- Squared conditional covariance density. -/
noncomputable def covarianceEnergy (X : Ω → Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, P.covariance (fun x => X x i) (fun x => X x j)^2) / (n : ℝ)^2

/-- Matrix Cauchy-Schwarz with exactly the manuscript's normalization. -/
theorem normalized_abs_sum_le (C : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, |C i j|) / (n : ℝ)^2 ≤
      Real.sqrt ((∑ i, ∑ j, C i j ^ 2) / (n : ℝ)^2) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsq : (∑ i, ∑ j, |C i j|)^2 ≤ (n : ℝ)^2 * (∑ i, ∑ j, C i j ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun ij : Fin n × Fin n => |C ij.1 ij.2|)
    simpa [Fintype.sum_prod_type, sq_abs, pow_two] using h
  apply Real.le_sqrt_of_sq_le
  rw [div_pow]
  apply (div_le_div_iff₀ (pow_pos (sq_pos_of_pos hn') 2) (sq_pos_of_pos hn')).mpr
  nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (n : ℝ))]

/-- The exact second moment if the other vector is held fixed. -/
theorem centered_contraction_identity (X : Ω → Fin n → ℝ) (b : Fin n → ℝ) :
    P.expect (fun x => (dot (fun i => X x i - P.expect (fun y => X y i)) b)^2) =
      (∑ i, ∑ j, P.covariance (fun x => X x i) (fun x => X x j) * (b i * b j)) /
        (n : ℝ)^2 := by
  simp_rw [dot_sq, expect_div, expect_fintype_sum, expect_mul_right]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [covariance_centered]

/-- decor:contraction-bound, before the last square root, for a fixed multiplier. -/
theorem centered_contraction_bound (X : Ω → Fin n → ℝ) (b : Fin n → ℝ)
    (hb : ∀ i, |b i| ≤ 1) :
    P.expect (fun x => (dot (fun i => X x i - P.expect (fun y => X y i)) b)^2) ≤
      Real.sqrt (P.covarianceEnergy X) := by
  rw [centered_contraction_identity]
  apply le_trans _ (normalized_abs_sum_le (fun i j =>
    P.covariance (fun x => X x i) (fun x => X x j)))
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ |P.covariance (fun x => X x i) (fun x => X x j) * (b i * b j)| := le_abs_self _
    _ = |P.covariance (fun x => X x i) (fun x => X x j)| * (|b i| * |b j|) := by
      simp only [abs_mul]
    _ ≤ |P.covariance (fun x => X x i) (fun x => X x j)| * (1 * 1) := by
      gcongr <;> exact hb _
    _ = _ := by ring

/-- The other multiplier may itself be random, independently sampled under Q. -/
theorem independent_contraction_bound {Λ : Type*} [Fintype Λ]
    (Q : FiniteLaw Λ) (X : Ω → Fin n → ℝ) (B : Λ → Fin n → ℝ)
    (hB : ∀ z i, |B z i| ≤ 1) :
    Q.expect (fun z => P.expect (fun x =>
      (dot (fun i => X x i - P.expect (fun y => X y i)) (B z))^2)) ≤
      Real.sqrt (P.covarianceEnergy X) := by
  calc
    _ ≤ Q.expect (fun _ => Real.sqrt (P.covarianceEnergy X)) :=
      Q.expect_mono (fun z => P.centered_contraction_bound X (B z) (hB z))
    _ = _ := Q.expect_const _

/-- Elementary Jensen for the square, proved from its nonnegative variance. -/
theorem expect_sq_sub_expect (f : Ω → ℝ) :
    P.expect (fun x => (f x - P.expect f)^2) =
      P.expect (fun x => f x ^ 2) - P.expect f ^ 2 := by
  calc
    _ = P.expect (fun x => f x ^ 2 - 2 * P.expect f * f x + P.expect f ^ 2) :=
      P.expect_congr (fun _ => by ring)
    _ = _ := by simp; ring

theorem sq_expect_le_expect_sq (f : Ω → ℝ) :
    P.expect f ^ 2 ≤ P.expect (fun x => f x ^ 2) := by
  have h := P.expect_nonneg (fun x => sq_nonneg (f x - P.expect f))
  rw [expect_sq_sub_expect] at h
  linarith

/-- Jensen for the square root, including possible zero coordinates. -/
theorem expect_sqrt_le (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) :
    P.expect (fun x => Real.sqrt (f x)) ≤ Real.sqrt (P.expect f) := by
  apply Real.le_sqrt_of_sq_le
  simpa only [Real.sq_sqrt (hf _)] using
    P.sq_expect_le_expect_sq (fun x => Real.sqrt (f x))

/-- Root/prefix averaged form of decor:contraction-bound. In the finite model
conditional independence is expressed constructively by the independent laws
P and Q at each prefix, not by an assumed covariance conclusion. -/
theorem conditional_contraction_bound {Γ Λ : Type*} [Fintype Γ] [Fintype Λ]
    (R : FiniteLaw Γ) (P : Γ → FiniteLaw Ω) (Q : Γ → FiniteLaw Λ)
    (X : Γ → Ω → Fin n → ℝ) (B : Γ → Λ → Fin n → ℝ)
    (hB : ∀ γ z i, |B γ z i| ≤ 1) :
    Real.sqrt (R.expect (fun γ => (Q γ).expect (fun z => (P γ).expect (fun x =>
      (dot (fun i => X γ x i - (P γ).expect (fun y => X γ y i)) (B γ z))^2)))) ≤
      Real.sqrt (Real.sqrt (R.expect (fun γ => (P γ).covarianceEnergy (X γ)))) := by
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ R.expect (fun γ => Real.sqrt ((P γ).covarianceEnergy (X γ))) :=
      R.expect_mono (fun γ => (P γ).independent_contraction_bound
        (Q γ) (X γ) (B γ) (hB γ))
    _ ≤ _ := R.expect_sqrt_le _ (fun γ => by
      unfold covarianceEnergy
      positivity)

/-- Prefix-averaged three-copy lower bound, the other half of decor:contractions. -/
theorem conditional_three_copy_bound {Γ : Type*} [Fintype Γ]
    (R : FiniteLaw Γ) (P : Γ → FiniteLaw Ω) (X : Γ → Ω → Fin n → ℝ) :
    2 * R.expect (fun γ => (P γ).covarianceEnergy (X γ)) ≤
      R.expect (fun γ => (P γ).expect (fun x => (P γ).expect (fun y =>
        (P γ).expect (fun z => (dot (X γ x) (X γ y) - dot (X γ x) (X γ z))^2)))) := by
  rw [← expect_mul_left]
  apply R.expect_mono
  intro γ
  convert (P γ).three_copy_bound (X γ) using 1
  unfold covarianceEnergy
  ring

/-- Finite-law Cauchy-Schwarz. -/
theorem expect_mul_sq_le (f g : Ω → ℝ) :
    P.expect (fun x => f x * g x)^2 ≤
      P.expect (fun x => f x^2) * P.expect (fun x => g x^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => Real.sqrt (P.weight x) * f x)
    (fun x => Real.sqrt (P.weight x) * g x)
  have hm (x : Ω) : Real.sqrt (P.weight x) * f x *
      (Real.sqrt (P.weight x) * g x) = P.weight x * (f x * g x) := by
    calc
      _ = Real.sqrt (P.weight x)^2 * (f x * g x) := by ring
      _ = _ := by rw [Real.sq_sqrt (P.nonneg x)]
  simpa only [hm, mul_pow, Real.sq_sqrt (P.nonneg _), expect] using h

noncomputable def l2 (f : Ω → ℝ) : ℝ := Real.sqrt (P.expect (fun x => f x^2))

theorem l2_nonneg (f : Ω → ℝ) : 0 ≤ P.l2 f := Real.sqrt_nonneg _

@[simp] theorem l2_sq (f : Ω → ℝ) : P.l2 f ^ 2 = P.expect (fun x => f x^2) :=
  Real.sq_sqrt (P.expect_nonneg (fun _ => sq_nonneg _))

@[simp] theorem l2_zero : P.l2 (fun _ => 0) = 0 := by simp [l2]

theorem expect_mul_le_l2 (f g : Ω → ℝ) :
    P.expect (fun x => f x * g x) ≤ P.l2 f * P.l2 g := by
  have h := P.expect_mul_sq_le f g
  have hf := P.l2_nonneg f
  have hg := P.l2_nonneg g
  rw [← P.l2_sq f, ← P.l2_sq g, ← mul_pow] at h
  exact (sq_le_sq₀ (by positivity) (mul_nonneg hf hg)).mp
    (by simpa only [sq_abs] using h) |>.trans' (le_abs_self _)

/-- Minkowski is used for successive projection of independent child shapes. -/
theorem l2_add_le (f g : Ω → ℝ) :
    P.l2 (fun x => f x + g x) ≤ P.l2 f + P.l2 g := by
  apply (sq_le_sq₀ (P.l2_nonneg _) (add_nonneg (P.l2_nonneg _) (P.l2_nonneg _))).mp
  rw [l2_sq]
  have heq : P.expect (fun x => (f x + g x)^2) =
      P.expect (fun x => f x^2) + 2 * P.expect (fun x => f x * g x) +
        P.expect (fun x => g x^2) := by
    calc
      _ = P.expect (fun x => f x^2 + 2 * (f x * g x) + g x^2) :=
        P.expect_congr (fun _ => by ring)
      _ = _ := by simp
  rw [heq, ← P.l2_sq f, ← P.l2_sq g]
  nlinarith [P.expect_mul_le_l2 f g]

theorem l2_mono {f g : Ω → ℝ} (h : ∀ x, |f x| ≤ |g x|) : P.l2 f ≤ P.l2 g := by
  apply Real.sqrt_le_sqrt
  apply P.expect_mono
  intro x
  exact sq_le_sq.mpr (h x)

theorem l2_mul_le (f g : Ω → ℝ) (hg : ∀ x, |g x| ≤ 1) :
    P.l2 (fun x => f x * g x) ≤ P.l2 f := by
  apply P.l2_mono
  intro x
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hg x) (abs_nonneg (f x))

/-- A finite mixture, to represent the root and the independent kernels exactly. -/
noncomputable def bind {Λ : Type*} [Fintype Λ] (Q : Ω → FiniteLaw Λ) : FiniteLaw (Ω × Λ) where
  weight x := P.weight x.1 * (Q x.1).weight x.2
  nonneg x := mul_nonneg (P.nonneg x.1) ((Q x.1).nonneg x.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, (Q _).total, mul_one, P.total]

@[simp] theorem expect_bind {Λ : Type*} [Fintype Λ] (Q : Ω → FiniteLaw Λ)
    (f : Ω × Λ → ℝ) :
    (P.bind Q).expect f = P.expect (fun x => (Q x).expect (fun y => f (x, y))) := by
  simp only [expect, bind, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- Conditional expectation contracts the L2 norm for a finite kernel. -/
theorem l2_condition_le {Λ : Type*} [Fintype Λ] (Q : Ω → FiniteLaw Λ)
    (f : Ω × Λ → ℝ) :
    P.l2 (fun x => (Q x).expect (fun y => f (x, y))) ≤ (P.bind Q).l2 f := by
  apply Real.sqrt_le_sqrt
  rw [expect_bind]
  exact P.expect_mono (fun x => (Q x).sq_expect_le_expect_sq _)


/-- Positive functions have positive finite expectation, without a full-support
assumption on the kernel. -/
theorem expect_pos {f : Ω → ℝ} (hf : ∀ x, 0 < f x) : 0 < P.expect f := by
  have hw : ∃ x, 0 < P.weight x := by
    by_contra! h
    have hz : (∑ x, P.weight x) ≤ ∑ _x : Ω, (0 : ℝ) :=
      Finset.sum_le_sum (fun x _ => h x)
    simp only [P.total, Finset.sum_const_zero] at hz
    linarith
  obtain ⟨x, hx⟩ := hw
  exact Finset.sum_pos' (fun y _ => mul_nonneg (P.nonneg y) (hf y).le)
    ⟨x, Finset.mem_univ _, mul_pos hx (hf x)⟩

noncomputable def expMoment (m : ℝ) (f : Ω → ℝ) : ℝ :=
  P.expect (fun x => Real.exp (m * f x))

@[simp] theorem expMoment_pos (m : ℝ) (f : Ω → ℝ) : 0 < P.expMoment m f :=
  P.expect_pos (fun _ => Real.exp_pos _)

/-- One tilted path kernel (trees.tex, original-tilt). -/
noncomputable def tilt (m : ℝ) (f : Ω → ℝ) : FiniteLaw Ω where
  weight x := P.weight x * Real.exp (m * f x) / P.expMoment m f
  nonneg x := div_nonneg (mul_nonneg (P.nonneg x) (Real.exp_pos _).le)
    (P.expMoment_pos _ _).le
  total := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (P.expMoment_pos _ _))

noncomputable def logMean (m : ℝ) (f : Ω → ℝ) : ℝ :=
  Real.log (P.expMoment m f) / m

theorem tilt_expect (m : ℝ) (f g : Ω → ℝ) :
    (P.tilt m f).expect g =
      P.expect (fun x => Real.exp (m * f x) * g x) / P.expMoment m f := by
  simp only [expect, tilt, div_mul_eq_mul_div, ← Finset.sum_div, mul_assoc]

@[simp] theorem expMoment_add (m c : ℝ) (f : Ω → ℝ) :
    P.expMoment m (fun x => f x + c) = P.expMoment m f * Real.exp (m * c) := by
  simp only [expMoment, mul_add, Real.exp_add, expect_mul_right]

@[simp] theorem logMean_add {m : ℝ} (hm : m ≠ 0) (c : ℝ) (f : Ω → ℝ) :
    P.logMean m (fun x => f x + c) = P.logMean m f + c := by
  simp only [logMean, expMoment_add,
    Real.log_mul (ne_of_gt (P.expMoment_pos _ _)) (ne_of_gt (Real.exp_pos _)),
    Real.log_exp, add_div]
  field_simp

theorem logMean_mono {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    P.logMean m f ≤ P.logMean m g := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (P.expMoment_pos _ _)
  exact P.expect_mono (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (h x) hm.le))

/-- Root-measurable uniform bounds pass unchanged through each power mean. -/
theorem logMean_stability {m c : ℝ} (hm : 0 < m) {f g : Ω → ℝ}
    (h : ∀ x, |f x - g x| ≤ c) : |P.logMean m f - P.logMean m g| ≤ c := by
  have hfg : P.logMean m f ≤ P.logMean m g + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).2; linarith)
  have hgf : P.logMean m g ≤ P.logMean m f + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Exact insertion identity for a single finite backward step. -/
theorem logMean_insertion {m : ℝ} (f a : Ω → ℝ) :
    P.logMean m (fun x => f x + a x) - P.logMean m f =
      (P.tilt m f).logMean m a := by
  have hmom : (P.tilt m f).expMoment m a =
      P.expMoment m (fun x => f x + a x) / P.expMoment m f := by
    rw [expMoment, tilt_expect]
    congr 1
    exact P.expect_congr (fun x => by rw [mul_add, Real.exp_add])
  rw [logMean, logMean, logMean, hmom,
    Real.log_div (ne_of_gt (P.expMoment_pos _ _)) (ne_of_gt (P.expMoment_pos _ _)),
    sub_div]

/-- Differentiation commutes with a finite path kernel. -/
theorem hasDerivAt_expect {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} {u : ℝ}
    (h : ∀ x, HasDerivAt (fun t => f t x) (f' x) u) :
    HasDerivAt (fun t => P.expect (f t)) (P.expect f') u := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun x _ => (h x).const_mul (P.weight x))
  have heq : (∑ x, fun t => P.weight x * f t x) = (fun t => P.expect (f t)) := by
    funext t
    simp only [Finset.sum_apply, expect]
  rw [heq] at hd
  exact hd

/-- First variation of a power-mean step: the derivative is the tilted score. -/
theorem hasDerivAt_logMean {m : ℝ} (hm : m ≠ 0)
    {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} {u : ℝ}
    (h : ∀ x, HasDerivAt (fun t => f t x) (f' x) u) :
    HasDerivAt (fun t => P.logMean m (f t)) ((P.tilt m (f u)).expect f') u := by
  have he := P.hasDerivAt_expect (fun x => ((h x).const_mul m).exp)
  have hl := (he.log (ne_of_gt (P.expMoment_pos m (f u)))).div_const m
  change HasDerivAt (fun t => P.logMean m (f t)) _ u at hl
  suffices heqv : (P.tilt m (f u)).expect f' =
      (P.expect (fun x => Real.exp (m * f u x) * (m * f' x)) / P.expMoment m (f u)) / m by
    rw [heqv]
    exact hl
  rw [tilt_expect]
  have heq : P.expect (fun x => Real.exp (m * f u x) * (m * f' x)) =
      m * P.expect (fun x => Real.exp (m * f u x) * f' x) := by
    rw [← expect_mul_left]
    exact P.expect_congr (fun x => by ring)
  rw [heq]
  field_simp


/-- Differentiating an observable under a finite exponentially tilted kernel. -/
theorem hasDerivAt_tilt_expect {m : ℝ}
    {f g : ℝ → Ω → ℝ} {f' g' : Ω → ℝ} {u : ℝ}
    (hf : ∀ x, HasDerivAt (fun t => f t x) (f' x) u)
    (hg : ∀ x, HasDerivAt (fun t => g t x) (g' x) u) :
    HasDerivAt (fun t => (P.tilt m (f t)).expect (g t))
      ((P.tilt m (f u)).expect g' +
        m * (P.tilt m (f u)).covariance (g u) f') u := by
  have hnum := P.hasDerivAt_expect
    (fun x => (((hf x).const_mul m).exp).mul (hg x))
  have hden := P.hasDerivAt_expect (fun x => ((hf x).const_mul m).exp)
  have hd := hnum.div hden (ne_of_gt (P.expMoment_pos m (f u)))
  simp only [tilt_expect]
  apply hd.congr_deriv
  have hnum' : P.expect (fun x =>
      Real.exp (m * f u x) * (m * f' x) * g u x + Real.exp (m * f u x) * g' x) =
      m * P.expect (fun x => Real.exp (m * f u x) * (g u x * f' x)) +
        P.expect (fun x => Real.exp (m * f u x) * g' x) := by
    rw [expect_add, ← expect_mul_left]
    congr 1
    exact P.expect_congr (fun x => by ring)
  have hden' : P.expect (fun x => Real.exp (m * f u x) * (m * f' x)) =
      m * P.expect (fun x => Real.exp (m * f u x) * f' x) := by
    rw [← expect_mul_left]
    exact P.expect_congr (fun x => by ring)
  rw [hnum', hden', covariance, tilt_expect, tilt_expect, tilt_expect]
  simp only [expMoment, Pi.mul_apply]
  have hne : P.expect (fun x => Real.exp (m * f u x)) ≠ 0 :=
    ne_of_gt (P.expMoment_pos m (f u))
  field_simp [hne]
  ring

/-- The second variation identity used in bounded score concentration. -/
theorem hasDerivAt_tilt_score {m : ℝ}
    {f f' : ℝ → Ω → ℝ} {f'' : Ω → ℝ} {u : ℝ}
    (hf : ∀ x, HasDerivAt (fun t => f t x) (f' u x) u)
    (hf' : ∀ x, HasDerivAt (fun t => f' t x) (f'' x) u) :
    HasDerivAt (fun t => (P.tilt m (f t)).expect (f' t))
      ((P.tilt m (f u)).expect f'' +
        m * (P.tilt m (f u)).covariance (f' u) (f' u)) u :=
  P.hasDerivAt_tilt_expect hf hf'

/-- Total variance at one edge of a finite probability tree. -/
theorem variance_bind {Λ : Type*} [Fintype Λ] (Q : Ω → FiniteLaw Λ)
    (f : Ω × Λ → ℝ) :
    (P.bind Q).covariance f f =
      P.expect (fun x => (Q x).covariance (fun y => f (x,y)) (fun y => f (x,y))) +
        P.covariance (fun x => (Q x).expect (fun y => f (x,y)))
          (fun x => (Q x).expect (fun y => f (x,y))) := by
  simp only [covariance, expect_bind, expect_sub]
  ring

theorem covariance_self_nonneg (f : Ω → ℝ) : 0 ≤ P.covariance f f := by
  rw [covariance_centered]
  exact P.expect_nonneg (fun x => mul_self_nonneg _)

/-- A bounded spin product has total conditional variance at most one. -/
theorem covariance_self_le_one {f : Ω → ℝ} (hf : ∀ x, |f x| ≤ 1) :
    P.covariance f f ≤ 1 := by
  have hs : P.expect (fun x => f x * f x) ≤ 1 := by
    rw [← P.expect_const 1]
    apply P.expect_mono
    intro x
    nlinarith [sq_le_sq.mpr (show |f x| ≤ |(1 : ℝ)| by simpa using hf x)]
  unfold covariance
  nlinarith [sq_nonneg (P.expect f)]


@[ext] theorem weights_ext {P Q : FiniteLaw Ω} (h : ∀ x, P.weight x = Q.weight x) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

@[simp] theorem logMean_const {m : ℝ} (hm : m ≠ 0) (c : ℝ) :
    P.logMean m (fun _ => c) = c := by
  simp only [logMean, expMoment, expect_const, Real.log_exp]
  field_simp

/-- The edge-density form of the normalized tilted finite kernel. -/
theorem tilt_weight {m : ℝ} (hm : m ≠ 0) (f : Ω → ℝ) (x : Ω) :
    (P.tilt m f).weight x = P.weight x * Real.exp (m * (f x - P.logMean m f)) := by
  have hlog : m * P.logMean m f = Real.log (P.expMoment m f) := by
    unfold logMean
    field_simp
  rw [mul_sub, hlog, Real.exp_sub, Real.exp_log (P.expMoment_pos m f)]
  simp only [tilt, mul_div_assoc]

/-- Exact composition of two one-step insertions, with no support assumption. -/
theorem tilt_insertion (m : ℝ) (f a : Ω → ℝ) :
    (P.tilt m f).tilt m a = P.tilt m (fun x => f x + a x) := by
  apply weights_ext
  intro x
  have he : (P.tilt m f).expMoment m a =
      P.expMoment m (fun x => f x + a x) / P.expMoment m f := by
    rw [expMoment, tilt_expect]
    congr 1
    exact P.expect_congr (fun x => by rw [mul_add, Real.exp_add])
  change (P.weight x * Real.exp (m * f x) / P.expMoment m f) * Real.exp (m * a x) /
    (P.tilt m f).expMoment m a = _
  rw [he]
  simp only [tilt, mul_add, Real.exp_add]
  field_simp [ne_of_gt (P.expMoment_pos m f)]

/-- Independent product of finitely many finite conditional laws. -/
noncomputable def pi {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (Q : (i : ι) → FiniteLaw (α i)) : FiniteLaw ((i : ι) → α i) where
  weight x := ∏ i, (Q i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (Q i).nonneg _)
  total := by rw [← Fintype.prod_sum]; simp only [(Q _).total, Finset.prod_const_one]

/-- Finite independence identity, valid for arbitrary and distinct kernels. -/
theorem expect_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → ℝ) :
    (pi Q).expect (fun x => ∏ i, f i (x i)) = ∏ i, (Q i).expect (f i) := by
  simp only [expect, pi, ← Finset.prod_mul_distrib, Fintype.prod_sum]

theorem abs_expect_le {f : Ω → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    |P.expect f| ≤ B := by
  apply abs_le.mpr
  constructor
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).1)
    simpa only [expect_const] using h
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).2)
    simpa only [expect_const] using h

theorem continuousOn_expect {S : Set ℝ} {f : ℝ → Ω → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S) :
    ContinuousOn (fun t => P.expect (f t)) S := by
  unfold expect
  apply continuousOn_finsetSum
  intro x _
  exact continuousOn_const.mul (hf x)

theorem continuousOn_logMean {S : Set ℝ} {f : ℝ → Ω → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S) (m : ℝ) :
    ContinuousOn (fun t => P.logMean m (f t)) S := by
  apply ContinuousOn.div_const
  apply ContinuousOn.log
  · exact P.continuousOn_expect (fun x => (continuousOn_const.mul (hf x)).rexp)
  · intro t _
    exact ne_of_gt (P.expMoment_pos m (f t))

theorem continuousOn_tilt_expect {S : Set ℝ} {f g : ℝ → Ω → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S)
    (hg : ∀ x, ContinuousOn (fun t => g t x) S) (m : ℝ) :
    ContinuousOn (fun t => (P.tilt m (f t)).expect (g t)) S := by
  simp_rw [tilt_expect]
  apply ContinuousOn.div
  · exact P.continuousOn_expect (fun x => ((continuousOn_const.mul (hf x)).rexp).mul (hg x))
  · exact P.continuousOn_expect (fun x => (continuousOn_const.mul (hf x)).rexp)
  · intro t _
    exact ne_of_gt (P.expMoment_pos m (f t))

theorem continuousOn_tilt_covariance {S : Set ℝ} {f g : ℝ → Ω → ℝ}
    (hf : ∀ x, ContinuousOn (fun t => f t x) S)
    (hg : ∀ x, ContinuousOn (fun t => g t x) S) (m : ℝ) :
    ContinuousOn (fun t => (P.tilt m (f t)).covariance (g t) (g t)) S := by
  unfold covariance
  exact (P.continuousOn_tilt_expect hf (fun x => (hg x).mul (hg x)) m).sub
    ((P.continuousOn_tilt_expect hf hg m).mul (P.continuousOn_tilt_expect hf hg m))

end FiniteLaw
end DilutedSpinGlass

end

end OAI
