import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Decoding.MaskMomentLemmas
import OAI.Computability.UniqueGames.Games.Variation

namespace OAI

section

/-!
The finite calculation of projected total variation. The three singleton
lines are averaged before the divergence is taken; projection choices are
not part of the compared sample space. Coordinates are independently sampled
occurrences, irrespective of whether their equation IDs coincide.
-/

namespace UniqueGamesTheorem.Decoder.SparseLaw

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Information

noncomputable section

variable {α : Type*} [Fintype α]

def uniformWeights (α : Type*) [Fintype α] : α → ℝ :=
  fun _ => 1 / Fintype.card α

theorem uniformWeights_pos [Nonempty α] (a : α) : 0 < uniformWeights α a := by
  exact div_pos (by norm_num) (Nat.cast_pos.mpr Fintype.card_pos)

theorem uniformWeights_isProbability [Nonempty α] :
    IsProbability (uniformWeights α) := by
  constructor
  · exact fun a => (uniformWeights_pos a).le
  · simp [uniformWeights, Fintype.card_ne_zero]

/-- Pearson divergence against the uniform law, written with its constant
denominator cleared. `uniformChiSquare_eq_pearson` identifies the actual
likelihood-ratio definition. -/
def uniformChiSquare (p : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ) * ∑ a, (p a - uniformWeights α a) ^ 2

theorem uniformChiSquare_eq_pearson [Nonempty α] (p : α → ℝ) :
    uniformChiSquare p =
      ∑ a, uniformWeights α a * (p a / uniformWeights α a - 1) ^ 2 := by
  rw [uniformChiSquare, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [uniformWeights]
  field_simp [hn]

theorem uniformChiSquare_eq_secondMoment [Nonempty α] (p : α → ℝ)
    (hp : IsProbability p) :
    uniformChiSquare p = (Fintype.card α : ℝ) * (∑ a, p a ^ 2) - 1 := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpoint (a : α) :
      (Fintype.card α : ℝ) * (p a - uniformWeights α a) ^ 2 =
        (Fintype.card α : ℝ) * p a ^ 2 - 2 * p a + uniformWeights α a := by
    simp only [uniformWeights]
    field_simp [hn]
    ring
  rw [uniformChiSquare, Finset.mul_sum]
  simp only [hpoint, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2,
    (uniformWeights_isProbability (α := α)).2]
  ring

theorem uniformChiSquare_nonneg (p : α → ℝ) : 0 ≤ uniformChiSquare p := by
  unfold uniformChiSquare
  positivity

def mixture (β : ℝ) (p : α → ℝ) : α → ℝ :=
  fun a => (1 - β) * uniformWeights α a + β * p a

theorem mixture_isProbability [Nonempty α] (p : α → ℝ) (hp : IsProbability p)
    {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1) : IsProbability (mixture β p) := by
  constructor
  · intro a
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hβ') (uniformWeights_pos a).le)
      (mul_nonneg hβ (hp.1 a))
  · simp only [mixture, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2,
      (uniformWeights_isProbability (α := α)).2]
    ring

theorem uniformChiSquare_mixture (p : α → ℝ) (β : ℝ) :
    uniformChiSquare (mixture β p) = β ^ 2 * uniformChiSquare p := by
  have hpoint (a : α) :
      (mixture β p a - uniformWeights α a) ^ 2 =
        β ^ 2 * (p a - uniformWeights α a) ^ 2 := by
    unfold mixture
    ring
  simp only [uniformChiSquare, hpoint, ← Finset.mul_sum]
  ring

theorem totalVariation_le_half_sqrt (p : α → ℝ) :
    totalVariation p (uniformWeights α) ≤ Real.sqrt (uniformChiSquare p) / 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun _ => (1 : ℝ)) (fun a => |p a - uniformWeights α a|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, sq_abs] at hcs
  have hs := Real.le_sqrt_of_sq_le hcs
  exact div_le_div_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2)

def independentWeights (p : α → ℝ) (k : ℕ) : (Fin k → α) → ℝ :=
  fun x => ∏ i, p (x i)

theorem independentWeights_isProbability (p : α → ℝ) (hp : IsProbability p)
    (k : ℕ) : IsProbability (independentWeights p k) := by
  constructor
  · intro x
    exact Finset.prod_nonneg fun i _ => hp.1 (x i)
  · change (∑ x : Fin k → α, ∏ i, p (x i)) = 1
    rw [← Fintype.sum_pow, hp.2, one_pow]

theorem uniformChiSquare_independent [Nonempty α] (p : α → ℝ)
    (hp : IsProbability p) (k : ℕ) :
    uniformChiSquare (independentWeights p k) = (1 + uniformChiSquare p) ^ k - 1 := by
  rw [uniformChiSquare_eq_secondMoment _ (independentWeights_isProbability p hp k),
    uniformChiSquare_eq_secondMoment p hp]
  have hsecond : (∑ x : Fin k → α, independentWeights p k x ^ 2) =
      (∑ a, p a ^ 2) ^ k := by
    simp only [independentWeights, ← Finset.prod_pow]
    exact (Fintype.sum_pow (fun a => p a ^ 2) k).symm
  rw [hsecond]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [← mul_pow]
  exact congrArg (fun t : ℝ => t ^ k - 1) (by ring)

/-- A finite bound sufficient for the cube asymptotic, without introducing a
limit theorem or choosing the alphabet after the repetition count. -/
theorem pow_mul_one_sub_le_one (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k * (1 - k * x) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 ≤ (1 + x) ^ k := pow_nonneg (by linarith) _
    have herr : 0 ≤ (1 + x) ^ k * ((k : ℝ) + 1) * x ^ 2 :=
      mul_nonneg (mul_nonneg hp (by positivity)) (sq_nonneg x)
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem pow_sub_one_le_fraction (x : ℝ) (hx : 0 ≤ x) (k : ℕ)
    (hk : (k : ℝ) * x < 1) :
    (1 + x) ^ k - 1 ≤ (k : ℝ) * x / (1 - (k : ℝ) * x) := by
  apply (le_div_iff₀ (sub_pos.mpr hk)).2
  have h := pow_mul_one_sub_le_one x hx k
  nlinarith

theorem pow_sub_one_le_twice (x : ℝ) (hx : 0 ≤ x) (k : ℕ)
    (hk : (k : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ k - 1 ≤ 2 * (k : ℝ) * x := by
  have hk' : (k : ℝ) * x < 1 := by linarith
  refine (pow_sub_one_le_fraction x hx k hk').trans ?_
  apply (div_le_iff₀ (sub_pos.mpr hk')).2
  have hn : 0 ≤ (k : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  nlinarith

section Singleton

variable (V : Type*) [Fintype V] [Zero V] [DecidableEq V]

/-- At the origin all three singleton lines contribute. -/
def lineCount (z : V × V) : ℝ :=
  (if z.2 = 0 then 1 else 0) + (if z.1 = 0 then 1 else 0) +
    (if z.1 = z.2 then 1 else 0)

/-- The average of the laws of `(a,0)`, `(0,a)`, and `(a,a)` for uniform `a`. -/
def singletonPairWeights (z : V × V) : ℝ := lineCount V z / (3 * Fintype.card V)

/-- Explicit finite pushforward of the three equally likely singleton choices.
The same uniform slope supplies both entries of the diagonal choice. -/
def singletonSamplerWeights (z : V × V) : ℝ :=
  ((∑ a : V, if (a, 0) = z then uniformWeights V a else 0) +
    (∑ a : V, if (0, a) = z then uniformWeights V a else 0) +
    (∑ a : V, if (a, a) = z then uniformWeights V a else 0)) / 3

theorem singletonSamplerWeights_eq (z : V × V) :
    singletonSamplerWeights V z = singletonPairWeights V z := by
  classical
  rcases z with ⟨x, y⟩
  have hleft : (∑ a : V, if (a, 0) = (x, y) then uniformWeights V a else 0) =
      if y = 0 then 1 / (Fintype.card V : ℝ) else 0 := by
    by_cases hy : y = 0
    · simp [hy, uniformWeights]
    · simp [Prod.mk.injEq, Ne.symm hy, hy]
  have hright : (∑ a : V, if (0, a) = (x, y) then uniformWeights V a else 0) =
      if x = 0 then 1 / (Fintype.card V : ℝ) else 0 := by
    by_cases hx : x = 0
    · simp [hx, uniformWeights]
    · simp [Prod.mk.injEq, Ne.symm hx, hx]
  have hdiag : (∑ a : V, if (a, a) = (x, y) then uniformWeights V a else 0) =
      if x = y then 1 / (Fintype.card V : ℝ) else 0 := by
    by_cases hxy : x = y
    · simp [hxy, uniformWeights]
    · have hnone (a : V) : (a, a) ≠ (x, y) := by
        intro ha
        have he := Prod.mk.inj ha
        exact hxy (he.1.symm.trans he.2)
      simp [hnone, hxy]
  simp only [singletonSamplerWeights, hleft, hright, hdiag,
    singletonPairWeights, lineCount]
  split_ifs <;> ring

theorem lineCount_sum : ∑ z : V × V, lineCount V z = 3 * Fintype.card V := by
  have h₁ : (∑ z : V × V, if z.2 = 0 then (1 : ℝ) else 0) = Fintype.card V := by
    rw [Fintype.sum_prod_type]
    simp
  have h₂ : (∑ z : V × V, if z.1 = 0 then (1 : ℝ) else 0) = Fintype.card V := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp
  have h₃ : (∑ z : V × V, if z.1 = z.2 then (1 : ℝ) else 0) = Fintype.card V := by
    rw [Fintype.sum_prod_type]
    simp
  simp only [lineCount, Finset.sum_add_distrib, h₁, h₂, h₃]
  ring

omit [Fintype V] in
theorem lineCount_sq (z : V × V) :
    lineCount V z ^ 2 = lineCount V z + (if z.1 = 0 ∧ z.2 = 0 then 6 else 0) := by
  by_cases hx : z.1 = 0 <;> by_cases hy : z.2 = 0 <;>
    by_cases hxy : z.1 = z.2 <;> simp_all [lineCount]
  norm_num

theorem lineCount_sq_sum :
    ∑ z : V × V, lineCount V z ^ 2 = 3 * Fintype.card V + 6 := by
  simp only [lineCount_sq, Finset.sum_add_distrib, lineCount_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (0 : V)]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem singletonPairWeights_isProbability : IsProbability (singletonPairWeights V) := by
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  constructor
  · intro z
    unfold singletonPairWeights lineCount
    positivity
  · simp only [singletonPairWeights, div_eq_mul_inv, ← Finset.sum_mul, lineCount_sum]
    exact mul_inv_cancel₀ (ne_of_gt (mul_pos (by norm_num) hn))

theorem singletonPairWeights_secondMoment :
    ∑ z : V × V, singletonPairWeights V z ^ 2 =
      (3 * Fintype.card V + 6) / (3 * Fintype.card V) ^ 2 := by
  simp only [singletonPairWeights, div_pow]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, lineCount_sq_sum]

theorem singletonPairWeights_chiSquare :
    uniformChiSquare (singletonPairWeights V) = ((Fintype.card V : ℝ) - 1) / 3 := by
  rw [uniformChiSquare_eq_secondMoment _ (singletonPairWeights_isProbability V),
    singletonPairWeights_secondMoment]
  simp only [Fintype.card_prod, Nat.cast_mul]
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hn]
  ring

/-- Exact finite divergence of the padded slope law. -/
theorem paddedSlope_chiSquare (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (k : ℕ) :
    uniformChiSquare (independentWeights (mixture β (singletonPairWeights V)) k) =
      (1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1 := by
  rw [uniformChiSquare_independent _
    (mixture_isProbability _ (singletonPairWeights_isProbability V) hβ hβ'),
    uniformChiSquare_mixture, singletonPairWeights_chiSquare]
  exact congrArg (fun t : ℝ => (1 + t) ^ k - 1) (by ring)

theorem paddedSlope_totalVariation (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (k : ℕ) :
    totalVariation (independentWeights (mixture β (singletonPairWeights V)) k)
      (uniformWeights (Fin k → V × V)) ≤
        Real.sqrt ((1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1) / 2 := by
  simpa only [paddedSlope_chiSquare V β hβ hβ' k] using
    totalVariation_le_half_sqrt (independentWeights (mixture β (singletonPairWeights V)) k)

theorem paddedSlope_totalVariation_small (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (k : ℕ)
    (hk : (k : ℝ) * (β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ≤ 1 / 2) :
    totalVariation (independentWeights (mixture β (singletonPairWeights V)) k)
      (uniformWeights (Fin k → V × V)) ≤
        Real.sqrt (2 * (k : ℝ) * (β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3)) / 2 := by
  have hn : (1 : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card V))
  refine (paddedSlope_totalVariation V β hβ hβ' k).trans ?_
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Real.sqrt_le_sqrt
  exact pow_sub_one_le_twice _ (by positivity) _ hk

theorem cubeSlope_totalVariation (m : ℕ) (hm : 0 < m)
    (hsize : 2 * ((Fintype.card V : ℝ) - 1) / 3 ≤ m) :
    totalVariation
      (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
      (uniformWeights (Fin (m ^ 3) → V × V)) ≤
        Real.sqrt (2 * ((Fintype.card V : ℝ) - 1) / (3 * m)) / 2 := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hbeta : (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hmpos)).2
    nlinarith
  have hproduct : ((m ^ 3 : ℕ) : ℝ) *
      ((1 / (m : ℝ) ^ 2) ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) =
        ((Fintype.card V : ℝ) - 1) / (3 * m) := by
    push_cast
    field_simp [hmpos.ne']
  have hsmall : ((m ^ 3 : ℕ) : ℝ) *
      ((1 / (m : ℝ) ^ 2) ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ≤ 1 / 2 := by
    rw [hproduct]
    apply (div_le_iff₀ (mul_pos (by norm_num) hmpos)).2
    linarith
  have h := paddedSlope_totalVariation_small V (1 / (m : ℝ) ^ 2)
    (by positivity) hbeta (m ^ 3) hsmall
  convert h using 1
  congr 2
  calc
    2 * ((Fintype.card V : ℝ) - 1) / (3 * m) =
        2 * (((Fintype.card V : ℝ) - 1) / (3 * m)) := by ring
    _ = _ := by rw [← hproduct]; ring

/-- Arbitrarily many expected singleton coordinates coexist with arbitrarily
small variation error: taking `k=m³` and `beta=m⁻²` leaves `k*beta=m`.
The bound involves only the fixed alphabet and requested error. -/
theorem exists_cubeSlope_totalVariation_le (η : ℝ) (hη : 0 < η) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < m ∧
      totalVariation
        (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
        (uniformWeights (Fin (m ^ 3) → V × V)) ≤ η := by
  obtain ⟨m, hm⟩ := exists_nat_ge
    (max (max (1 : ℝ) N)
      (max (2 * ((Fintype.card V : ℝ) - 1) / 3)
        (((Fintype.card V : ℝ) - 1) / (6 * η ^ 2))))
  have hlow : max (1 : ℝ) N ≤ m := (le_max_left _ _).trans hm
  have hmone : (1 : ℝ) ≤ m := (le_max_left _ _).trans hlow
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by norm_num) hmone
  have hN : (N : ℝ) ≤ m := (le_max_right _ _).trans hlow
  have hhigh : max (2 * ((Fintype.card V : ℝ) - 1) / 3)
      (((Fintype.card V : ℝ) - 1) / (6 * η ^ 2)) ≤ m :=
    (le_max_right _ _).trans hm
  have hsize := (le_max_left _ _).trans hhigh
  have hrate := (le_max_right _ _).trans hhigh
  have hrate' : (Fintype.card V : ℝ) - 1 ≤ (m : ℝ) * (6 * η ^ 2) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * η ^ 2)).mp hrate
  refine ⟨m, by exact_mod_cast hN, Nat.cast_pos.mp hmpos, ?_⟩
  refine (cubeSlope_totalVariation V m (Nat.cast_pos.mp hmpos) hsize).trans ?_
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  apply (Real.sqrt_le_left (by positivity : 0 ≤ η * 2)).2
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * m)).2
  nlinarith

theorem cube_expected_singletons (m : ℕ) (hm : 0 < m) :
    ((m ^ 3 : ℕ) : ℝ) * (1 / (m : ℝ) ^ 2) = m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  push_cast
  field_simp [hm']

end Singleton

section Intercept

variable {V : Type*} [Fintype V] [AddGroup V] [DecidableEq V]

omit [Fintype α] [DecidableEq V] in
/-- Pulling back an independent uniform intercept through any translation,
even one depending on all slopes and projection choices, leaves its joint law
unchanged. No independence of that translation from the slopes is assumed. -/
theorem translated_uniform_intercept (p : α → ℝ) (shift : α → V) (a : α) (z : V) :
    p a * uniformWeights V (z - shift a) = p a * uniformWeights V z := rfl

theorem uniform_intercept_pushforward (shift z : V) :
    (∑ t : V, if t + shift = z then uniformWeights V t else 0) =
      uniformWeights V z := by
  classical
  simp [← eq_sub_iff_add_eq, uniformWeights]

omit [Fintype α] in
theorem joint_intercept_pushforward (p : α → ℝ) (shift : α → V) (a : α) (z : V) :
    (∑ t : V, if t + shift a = z then p a * uniformWeights V t else 0) =
      p a * uniformWeights V z := by
  classical
  calc
    _ = p a * (∑ t : V, if t + shift a = z then uniformWeights V t else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      split <;> simp_all
    _ = _ := by rw [uniform_intercept_pushforward]

omit [DecidableEq V] in
theorem totalVariation_append_uniform_intercept (p q : α → ℝ) :
    totalVariation (fun az : α × V => p az.1 * uniformWeights V az.2)
      (fun az : α × V => q az.1 * uniformWeights V az.2) = totalVariation p q := by
  exact UniqueGamesTheorem.Foundations.Repetition.totalVariation_append_kernel p q
    (fun _ => uniformWeights V) (fun _ => uniformWeights_isProbability)

end Intercept

end
end UniqueGamesTheorem.Decoder.SparseLaw

end

section

namespace UniqueGamesTheorem.Decoder.ConstantSelection

open UniqueGamesTheorem.Foundations.Information
open SparseLaw

noncomputable section

/-- Probability of actual visible data carrying a transferred witness. -/
def visibleMass (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  α * g₀ / (8 * (2 : ℝ) ^ (ell * r))

/-- Independent private decoding success on a transferred witness. -/
def conditionalMass (α : ℝ) (ell r : ℕ) : ℝ :=
  (α / 8) ^ 2 / (2 : ℝ) ^ (ell * r) / (2 : ℝ) ^ r

def decodingMass (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  visibleMass α g₀ ell r * conditionalMass α ell r

/-- The whole-table TV budget includes the coefficient of both compared
events in the witness-margin inequality. -/
def variationBudget (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  visibleMass α g₀ ell r / (1 + α / 4)

theorem visibleMass_pos {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r : ℕ) : 0 < visibleMass α g₀ ell r := by
  unfold visibleMass
  positivity

theorem conditionalMass_pos {α : ℝ} (hα : 0 < α) (ell r : ℕ) :
    0 < conditionalMass α ell r := by
  unfold conditionalMass
  positivity

theorem decodingMass_pos {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r : ℕ) : 0 < decodingMass α g₀ ell r :=
  mul_pos (visibleMass_pos hα hg₀ ell r) (conditionalMass_pos hα ell r)

theorem variationBudget_pos {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r : ℕ) : 0 < variationBudget α g₀ ell r := by
  exact div_pos (visibleMass_pos hα hg₀ ell r) (by positivity)

theorem variationBudget_suffices {α g₀ ε : ℝ} (hα : 0 < α) (ell r : ℕ)
    (hε : ε ≤ variationBudget α g₀ ell r) :
    (1 + α / 4) * ε ≤ α * g₀ * (1 / (2 : ℝ) ^ (ell * r)) / 8 := by
  have hd : 0 < 1 + α / 4 := by positivity
  have h := (le_div_iff₀ hd).mp hε
  calc
    (1 + α / 4) * ε = ε * (1 + α / 4) := mul_comm _ _
    _ ≤ visibleMass α g₀ ell r := h
    _ = α * g₀ * (1 / (2 : ℝ) ^ (ell * r)) / 8 := by
      unfold visibleMass
      ring

/-- Exponential clean-mask decay persists after increasing the cube root. -/
theorem cube_exponential_antitone {m n : ℕ} (hmn : m ≤ n)
    {N : ℝ} (hN : 0 < N) :
    Real.exp (-(n : ℝ) / (3600 * N)) ≤
      Real.exp (-(m : ℝ) / (3600 * N)) := by
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact neg_le_neg (by exact_mod_cast hmn)

/-- One tuple length meets the sparse-law and repetition requirements, while
exceeding any independent inverse/erasure dimension threshold. -/
theorem exists_simultaneous_cube (V : Type*) [Fintype V] [Zero V] [DecidableEq V]
    {N ε γ : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hγ : 0 < γ) (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ 0 < m ∧
      totalVariation
        (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
        (uniformWeights (Fin (m ^ 3) → V × V)) ≤ ε ∧
      (1 - ((1 / (m : ℝ) ^ 2) / N) / 3600) ^ (m ^ 3) < γ := by
  obtain ⟨m₀, hm₀, hexp⟩ := Clean.exists_cube_exponential_lt
    (show 0 < N by linarith) hγ
  obtain ⟨m, hlarge, hm, htv⟩ := exists_cubeSlope_totalVariation_le V ε hε
    (max lower m₀)
  have hbase : m₀ ≤ m := (le_max_right _ _).trans hlarge
  refine ⟨m, (le_max_left _ _).trans hlarge, hm, htv, ?_⟩
  have hdecay := (Clean.cube_mask_rate_le_exp (Nat.succ_le_iff.mpr hm) hN).trans
    (cube_exponential_antitone hbase (by linarith : 0 < N))
  have hbeta : (1 / (m : ℝ)) ^ 2 = 1 / (m : ℝ) ^ 2 := by ring
  rw [hbeta] at hdecay
  exact hdecay.trans_lt hexp

/-- All scalar requirements for the final decoding contradiction can be met
after the fixed alphabet and inverse parameters have been chosen. -/
theorem exists_matrix_cube (V : Type*) [Fintype V] [Zero V] [DecidableEq V]
    {α g₀ : ℝ} (hα : 0 < α) (hg₀ : 0 < g₀)
    (ell r dimW lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ 0 < m ∧
      totalVariation
        (independentWeights (mixture (1 / (m : ℝ) ^ 2) (singletonPairWeights V)) (m ^ 3))
        (uniformWeights (Fin (m ^ 3) → V × V)) ≤ variationBudget α g₀ ell r ∧
      (1 - ((1 / (m : ℝ) ^ 2) / (2 : ℝ) ^ (dimW + r)) / 3600) ^ (m ^ 3) <
        decodingMass α g₀ ell r := by
  exact exists_simultaneous_cube V (one_le_pow₀ (by norm_num))
    (variationBudget_pos hα hg₀ ell r) (decodingMass_pos hα hg₀ ell r) lower

end
end UniqueGamesTheorem.Decoder.ConstantSelection

end

end OAI
