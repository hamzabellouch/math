import Mathlib
import OAI.Computability.MinUncut.PCP.DegreeReplacement

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.PCP.CayleySampling

open scoped BigOperators
open Finset
open MinUncutGames.Foundations.Hastad

variable {V D : Type*}

abbrev FalseFiber (χ : V → Bool) := {x : V // χ x = false}

def falseRepresentative (χ : V → Bool) (flip : V → V)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) : FalseFiber χ :=
  if h : χ x = false then ⟨x, h⟩
  else ⟨flip x, by cases hx : χ x <;> simp_all⟩

def booleanSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    V ≃ Bool × FalseFiber χ where
  toFun x := (χ x, falseRepresentative χ flip hχ x)
  invFun p := if p.1 then flip p.2.val else p.2.val
  left_inv x := by
    cases hx : χ x <;> simp [falseRepresentative, hx]
    exact hflip x
  right_inv p := by
    rcases p with ⟨b, x⟩
    apply Prod.ext
    · cases b <;> simp [hχ, x.property]
    · cases b <;> apply Subtype.ext <;>
        simp [falseRepresentative, hχ, x.property]
      exact hflip x.val

@[simp] theorem booleanSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) :
    (booleanSplitEquiv χ flip hflip hχ x).1 = χ x := rfl

def sampleSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    (D → V) ≃ (D → Bool) × (D → FalseFiber χ) :=
  (Equiv.piCongrRight fun _ : D => booleanSplitEquiv χ flip hflip hχ).trans
    (Equiv.arrowProdEquivProdArrow D (fun _ => Bool) (fun _ => FalseFiber χ))

@[simp] theorem sampleSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (g : D → V) :
    (sampleSplitEquiv χ flip hflip hχ g).1 = fun d => χ (g d) := rfl

theorem card_boolean_split [Fintype V] (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    Fintype.card V = 2 * Fintype.card (FalseFiber χ) := by
  simpa using Fintype.card_congr (booleanSplitEquiv χ flip hflip hχ)

theorem expect_boolean_samples [Fintype V] [Nonempty V] [Fintype D] [DecidableEq D]
    (χ : V → Bool) (flip : V → V) (hflip : Function.Involutive flip)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (F : (D → Bool) → ℝ) :
    (𝔼 g : D → V, F (fun d => χ (g d))) = 𝔼 b : D → Bool, F b := by
  classical
  have : Nonempty (FalseFiber χ) :=
    ⟨falseRepresentative χ flip hχ (Classical.choice ‹Nonempty V›)⟩
  calc
    (𝔼 g : D → V, F (fun d => χ (g d))) =
        𝔼 p : (D → Bool) × (D → FalseFiber χ), F p.1 := by
      apply Fintype.expect_equiv (sampleSplitEquiv χ flip hflip hχ)
      intro g
      rfl
    _ = 𝔼 b : D → Bool, F b := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

section Walsh

variable {I : Type*} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]

omit [DecidableEq I] in
theorem exists_true_of_ne_zero (s : Cube I) (hs : s ≠ fun _ => false) :
    ∃ i, s i = true := by
  by_contra h
  apply hs
  funext i
  cases hi : s i
  · rfl
  · exact False.elim (h ⟨i, hi⟩)

theorem expect_parity_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → Bool) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => AssignmentTester.parity s (g d))) =
      𝔼 b : D → Bool, F b := by
  obtain ⟨i, hi⟩ := exists_true_of_ne_zero s hs
  exact expect_boolean_samples (AssignmentTester.parity s) (AssignmentTester.flipAt i)
    (AssignmentTester.flipAt_twice i)
    (fun x => AssignmentTester.parity_flipAt s i x hi) F

theorem expect_walsh_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → ℝ) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => walsh s (g d))) =
      𝔼 b : D → Bool, F (fun d => bitSign (b d)) := by
  simpa only [AssignmentTester.bitSign_parity] using
    expect_parity_samples s hs (fun b => F (fun d => bitSign (b d)))

theorem expect_walsh_mean (s : Cube I) (hs : s ≠ fun _ => false) (F : ℝ → ℝ) :
    (𝔼 g : D → Cube I, F (𝔼 d, walsh s (g d))) =
      𝔼 b : D → Bool, F (𝔼 d, bitSign (b d)) :=
  expect_walsh_samples s hs (fun z => F (𝔼 d, z d))

end Walsh

end MinUncutGames.Foundations.PCP.CayleySampling

end
end
section
namespace MinUncutGames.Foundations.PCP.CayleyTailCount

open scoped BigOperators
open MinUncutGames.Foundations.Hastad (bitSign)

variable {α : Type*} [DecidableEq α]

def upperMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => 3 * m ≤ t.card

def lowerMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => t.card ≤ m

def badMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  lowerMasks s m ∪ upperMasks s m

omit [DecidableEq α] in

theorem upperMasks_weight (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    (upperMasks s m).card * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by
  calc
    _ = ∑ _t ∈ upperMasks s m, 3 ^ (3 * m) := by simp
    _ ≤ ∑ t ∈ upperMasks s m, 3 ^ t.card := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.pow_le_pow_right (by decide) (Finset.mem_filter.mp ht).2
    _ ≤ ∑ t ∈ s.powerset, 3 ^ t.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro t _ _
        exact Nat.zero_le _
    _ = 4 ^ s.card := by
      simpa using Finset.sum_pow_mul_eq_add_pow (3 : ℕ) 1 s
    _ = 4 ^ (4 * m) := by rw [hcard]

theorem lowerMasks_complement_image (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).image (fun t => s \ t) = upperMasks s m := by
  ext u
  constructor
  · intro hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hts, htlo⟩ := Finset.mem_filter.mp ht
    have hsub := Finset.mem_powerset.mp hts
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega
  · intro hu
    obtain ⟨hus, huhi⟩ := Finset.mem_filter.mp hu
    have hsub := Finset.mem_powerset.mp hus
    apply Finset.mem_image.mpr
    refine ⟨s \ u, ?_, Finset.sdiff_sdiff_eq_self hsub⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega

theorem lowerMasks_card_eq_upperMasks (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).card = (upperMasks s m).card := by
  have hinj : Set.InjOn (fun t : Finset α => s \ t) (lowerMasks s m) := by
    intro a ha b hb hab
    have has := Finset.mem_powerset.mp (Finset.mem_filter.mp ha).1
    have hbs := Finset.mem_powerset.mp (Finset.mem_filter.mp hb).1
    have h := congrArg (fun t : Finset α => s \ t) hab
    simpa only [Finset.sdiff_sdiff_eq_self has, Finset.sdiff_sdiff_eq_self hbs] using h
  calc
    _ = ((lowerMasks s m).image (fun t => s \ t)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = _ := congrArg Finset.card (lowerMasks_complement_image s m hcard)

private theorem ratio_le_of_weight (c m : ℕ)
    (h : c * 3 ^ (3 * m) ≤ 4 ^ (4 * m)) :
    (c : ℝ) / 2 ^ (4 * m) ≤ (16 / 27 : ℝ) ^ m := by
  have hc : (c : ℝ) * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by exact_mod_cast h
  have h3 : 0 < (3 : ℝ) ^ (3 * m) := by positivity
  have h2 : 0 < (2 : ℝ) ^ (4 * m) := by positivity
  calc
    _ ≤ ((4 : ℝ) ^ (4 * m) / 3 ^ (3 * m)) / 2 ^ (4 * m) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ h3).mpr hc) h2.le
    _ = _ := by
      rw [pow_mul, pow_mul, pow_mul, ← div_pow, ← div_pow]
      norm_num

omit [DecidableEq α] in
theorem upperMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((upperMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [hcard]
  exact ratio_le_of_weight _ m (upperMasks_weight s m hcard)

theorem lowerMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((lowerMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [lowerMasks_card_eq_upperMasks s m hcard]
  exact upperMasks_ratio_le s m hcard

theorem badMasks_ratio_le_sharp (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (16 / 27 : ℝ) ^ m := by
  have hc : ((badMasks s m).card : ℝ) ≤
      (lowerMasks s m).card + (upperMasks s m).card := by
    exact_mod_cast (Finset.card_union_le (lowerMasks s m) (upperMasks s m))
  have hpos : 0 < (2 : ℝ) ^ s.card := by positivity
  calc
    _ ≤ ((lowerMasks s m).card + (upperMasks s m).card : ℝ) / 2 ^ s.card :=
      div_le_div_of_nonneg_right hc hpos.le
    _ = ((lowerMasks s m).card : ℝ) / 2 ^ s.card +
        ((upperMasks s m).card : ℝ) / 2 ^ s.card := add_div _ _ _
    _ ≤ (16 / 27 : ℝ) ^ m + (16 / 27 : ℝ) ^ m :=
      add_le_add (lowerMasks_ratio_le s m hcard) (upperMasks_ratio_le s m hcard)
    _ = _ := by ring

theorem badMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (2 / 3 : ℝ) ^ m := by
  apply (badMasks_ratio_le_sharp s m hcard).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by norm_num)

section Words

variable {D : Type*} [Fintype D]

def trueMask (word : D → Bool) : Finset D :=
  Finset.univ.filter fun i => word i = true

def countTrue (word : D → Bool) : ℕ := (trueMask word).card

def badWord (m : ℕ) (word : D → Bool) : Prop :=
  countTrue word ≤ m ∨ 3 * m ≤ countTrue word

instance (m : ℕ) (word : D → Bool) : Decidable (badWord m word) :=
  inferInstanceAs (Decidable (countTrue word ≤ m ∨ 3 * m ≤ countTrue word))

theorem bitSign_mean_eq [Nonempty D] (word : D → Bool) :
    (𝔼 i, bitSign (word i)) =
      1 - 2 * ((countTrue word : ℝ) / Fintype.card D) := by
  have hsign (b : Bool) : bitSign b = 1 - 2 * (if b = true then (1 : ℝ) else 0) := by
    cases b <;> norm_num [bitSign]
  calc
    _ = (𝔼 i : D, (1 - 2 * (if word i = true then (1 : ℝ) else 0))) := by
      apply Finset.expect_congr rfl
      intro i _
      exact hsign (word i)
    _ = 1 - 2 * (𝔼 i, if word i = true then (1 : ℝ) else 0) := by
      rw [Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const]
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]
      rfl

theorem not_badWord_bias (m : ℕ) (hcard : Fintype.card D = 4 * m) (hm : 0 < m)
    (word : D → Bool) (hword : ¬ badWord m word) :
    |𝔼 i, bitSign (word i)| ≤ (1 / 2 : ℝ) := by
  have hD : 0 < Fintype.card D := by rw [hcard]; omega
  let : Nonempty D := Fintype.card_pos_iff.mp hD
  have hlo : m < countTrue word := lt_of_not_ge (not_or.mp hword).1
  have hhi : countTrue word < 3 * m := lt_of_not_ge (not_or.mp hword).2
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlor : (m : ℝ) ≤ countTrue word := by exact_mod_cast hlo.le
  have hhir : (countTrue word : ℝ) ≤ 3 * m := by exact_mod_cast hhi.le
  have hden : 0 < 4 * (m : ℝ) := by positivity
  have hratioLo : (1 / 4 : ℝ) ≤ (countTrue word : ℝ) / (4 * m) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  have hratioHi : (countTrue word : ℝ) / (4 * m) ≤ (3 / 4 : ℝ) :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  rw [bitSign_mean_eq word, hcard]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  apply abs_le.mpr
  constructor <;> linarith

def wordMaskEquiv [DecidableEq D] : (D → Bool) ≃ Finset D where
  toFun := trueMask
  invFun s i := decide (i ∈ s)
  left_inv word := by
    funext i
    cases h : word i <;> simp [trueMask, h]
  right_inv s := by
    ext i
    simp [trueMask]

theorem twoTail_probability [DecidableEq D] (m : ℕ) (hcard : Fintype.card D = 4 * m) :
    (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) ≤
      2 * (2 / 3 : ℝ) ^ m := by
  classical
  have he : (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) =
      (𝔼 s : Finset D, if s.card ≤ m ∨ 3 * m ≤ s.card then (1 : ℝ) else 0) := by
    apply Finset.expect_equiv (wordMaskEquiv (D := D))
    · intro word
      simp
    · intro word _
      rfl
  have hs : (Finset.univ.filter fun s : Finset D => s.card ≤ m ∨ 3 * m ≤ s.card) =
      badMasks (Finset.univ : Finset D) m := by
    ext s
    simp [badMasks, lowerMasks, upperMasks]
  rw [he, Fintype.expect_eq_sum_div_card, Finset.sum_boole, hs, Fintype.card_finset]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Finset.card_univ] using
    badMasks_ratio_le (Finset.univ : Finset D) m (by simpa using hcard)

end Words

theorem union_bound_le_half (n m : ℕ) (hm : 3 * (n + 2) ≤ m) :
    (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) ≤ 1 / 2 := by
  have hpow : (2 / 3 : ℝ) ^ m ≤ (2 / 3 : ℝ) ^ (3 * (n + 2)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hbase : (2 / 3 : ℝ) ^ (3 * (n + 2)) ≤ (1 / 2 : ℝ) ^ (n + 2) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) (n + 2)
  calc
    _ ≤ (2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (n + 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hpow.trans hbase) (by norm_num)) (by positivity)
    _ = 1 / 2 := by
      rw [pow_add, div_pow]
      norm_num
      field_simp
      norm_num

theorem fixed_parameters : 3 * (448 + 2) ≤ 16384 ∧ 4 * 16384 = 2 ^ 16 := by
  norm_num

theorem fixed_union_bound :
    (2 : ℝ) ^ 448 * (2 * (2 / 3 : ℝ) ^ 16384) ≤ 1 / 2 :=
  union_bound_le_half 448 16384 fixed_parameters.1

theorem seventh_power_size : (2 : ℕ) ^ 448 = (((2 : ℕ) ^ 16) ^ 7) ^ 4 := by
  rw [← pow_mul, ← pow_mul]

theorem seventh_power_abs_le {a : ℝ} (ha : |a| ≤ 1 / 2) : |a ^ 7| ≤ 1 / 128 := by
  rw [abs_pow]
  calc
    |a| ^ 7 ≤ (1 / 2 : ℝ) ^ 7 := pow_le_pow_left₀ (abs_nonneg a) ha 7
    _ = 1 / 128 := by norm_num

end MinUncutGames.Foundations.PCP.CayleyTailCount

end
section
namespace MinUncutGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def mean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := Finset.univ.expect f

def energy {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := mean (fun x => (f x) ^ 2)

def correlation {A : Type*} [Fintype A] (f g : A → ℝ) : ℝ :=
  mean (fun x => f x * g x)

def averagingOperator {V D : Type*} [Fintype D] (G : PortGraph V D)
    (f : V → ℝ) (v : V) : ℝ := Finset.univ.expect (fun d => f (G.rot (v, d)).1)

def iterateOperator {V D : Type*} [Fintype D] (G : PortGraph V D) :
    Nat → (V → ℝ) → (V → ℝ)
  | 0, f => f
  | n + 1, f => averagingOperator G (iterateOperator G n f)

def edgeProfile {V D : Type*} [Fintype D] (bad : V × D → Bool) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then 1 else 0)

def edgeDensity {V D : Type*} [Fintype V] [Fintype D] (bad : V × D → Bool) : ℝ :=
  mean (edgeProfile bad)

def markedStep {V D : Type*} [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then f (G.rot (v, d)).1 else 0)

def returnMass {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (bad : V × D → Bool) (gap : Nat) : ℝ :=
  mean (markedStep G bad (iterateOperator G gap (edgeProfile bad)))

structure SpectralCertificate {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (lambda : ℝ) : Prop where
  nonnegative : 0 ≤ lambda
  lt_one : lambda < 1
  contraction : ∀ f : V → ℝ, mean f = 0 →
    energy (averagingOperator G f) ≤ lambda ^ 2 * energy f

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_eq_sum_div_card (f : A → ℝ) :
    mean f = (∑ x, f x) / (Fintype.card A : ℝ) :=
  Fintype.expect_eq_sum_div_card f

theorem mean_equiv (e : A ≃ B) (f : B → ℝ) :
    mean (fun x => f (e x)) = mean f :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem mean_prod (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simpa only [mean, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset A) (Finset.univ : Finset B) f

@[simp] theorem mean_const [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c :=
  Fintype.expect_const c

theorem mean_add (f g : A → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g :=
  Finset.expect_add_distrib _ f g

theorem mean_sub (f g : A → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g :=
  Finset.expect_sub_distrib _ f g

theorem mean_mul_left (c : ℝ) (f : A → ℝ) :
    mean (fun x => c * f x) = c * mean f :=
  (Finset.mul_expect _ f c).symm

theorem mean_mul_right (f : A → ℝ) (c : ℝ) :
    mean (fun x => f x * c) = mean f * c :=
  (Finset.expect_mul _ f c).symm

theorem mean_nonnegative (f : A → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  Finset.expect_nonneg (fun x _ => hf x)

theorem mean_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  Finset.expect_le_expect (fun x _ => h x)

theorem energy_nonnegative (f : A → ℝ) : 0 ≤ energy f :=
  mean_nonnegative _ (fun x => sq_nonneg (f x))

theorem correlation_sq_le (f g : A → ℝ) :
    correlation f g ^ 2 ≤ energy f * energy g :=
  Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f g

theorem energy_sub_const [Nonempty A] (f : A → ℝ) (c : ℝ) :
    energy (fun x => f x - c) = energy f - 2 * c * mean f + c ^ 2 := by
  have h : (fun x => (f x - c) ^ 2) =
      (fun x => (f x) ^ 2 - (2 * c) * f x + c ^ 2) := by
    funext x
    ring
  unfold energy
  rw [h, mean_add, mean_sub, mean_mul_left, mean_const]

theorem correlation_sub_const [Nonempty A] (f g : A → ℝ) (c d : ℝ) :
    correlation (fun x => f x - c) (fun x => g x - d) =
      correlation f g - d * mean f - c * mean g + c * d := by
  have h : (fun x => (f x - c) * (g x - d)) =
      (fun x => f x * g x - d * f x - c * g x + c * d) := by
    funext x
    ring
  unfold correlation
  rw [h, mean_add, mean_sub, mean_sub, mean_mul_left, mean_mul_left, mean_const]

end Averages

section Graph

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  (G : PortGraph V D)

omit [Nonempty V] in
theorem mean_operator (f : V → ℝ) : mean (averagingOperator G f) = mean f := by
  calc
    mean (averagingOperator G f) = mean (fun e : V × D => f (G.rot e).1) :=
      (mean_prod (fun e : V × D => f (G.rot e).1)).symm
    _ = mean (fun e : V × D => f e.1) := mean_equiv G.rot (fun e => f e.1)
    _ = mean (fun v : V => mean (fun _ : D => f v)) :=
      mean_prod (fun e : V × D => f e.1)
    _ = mean f := by simp only [mean_const]

omit [Fintype V] [Nonempty V] in
theorem operator_sub_const (f : V → ℝ) (c : ℝ) :
    averagingOperator G (fun v => f v - c) = fun v => averagingOperator G f v - c := by
  funext v
  change mean (fun d => f (G.rot (v, d)).1 - c) = _
  rw [mean_sub, mean_const]
  rfl

omit [Nonempty V] in
theorem mean_iterate (n : Nat) (f : V → ℝ) : mean (iterateOperator G n f) = mean f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, mean_operator, ih]

omit [Fintype V] [Nonempty V] in
theorem iterate_sub_const (n : Nat) (f : V → ℝ) (c : ℝ) :
    iterateOperator G n (fun v => f v - c) = fun v => iterateOperator G n f v - c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, ih, operator_sub_const]; rfl

omit [Nonempty V] [Nonempty D] in
theorem mean_markedStep (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (f : V → ℝ) :
    mean (markedStep G bad f) = correlation (edgeProfile bad) f := by
  calc
    mean (markedStep G bad f) =
        mean (fun e : V × D => if bad e then f (G.rot e).1 else 0) := by
      exact (mean_prod (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad (G.rot e)
          then f (G.rot (G.rot e)).1 else 0) :=
      (mean_equiv G.rot (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad e then f e.1 else 0) := by
      congr 1
      funext e
      rw [reversal e, G.rot_involutive e]
    _ = mean (fun v => mean (fun d => if bad (v, d) then f v else 0)) :=
      mean_prod (fun e : V × D => if bad e then f e.1 else 0)
    _ = correlation (edgeProfile bad) f := by
      unfold correlation
      congr 1
      funext v
      have h : (fun d => if bad (v, d) then f v else 0) =
          (fun d => (if bad (v, d) then (1 : ℝ) else 0) * f v) := by
        funext d
        cases bad (v, d) <;> simp
      rw [h, mean_mul_right]
      rfl

omit [Nonempty V] [Nonempty D] in
theorem returnMass_eq_correlation (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap = correlation (edgeProfile bad)
      (iterateOperator G gap (edgeProfile bad)) :=
  mean_markedStep G bad reversal _

omit [Nonempty V] in
theorem iterate_energy_bound (lambda : ℝ) (certificate : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) (n : Nat) :
    energy (iterateOperator G n f) ≤ (lambda ^ n) ^ 2 * energy f := by
  induction n with
  | zero => simp [iterateOperator]
  | succ n ih =>
      calc
        energy (iterateOperator G (n + 1) f) ≤
            lambda ^ 2 * energy (iterateOperator G n f) :=
          certificate.contraction _ ((mean_iterate G n f).trans hf)
        _ ≤ lambda ^ 2 * ((lambda ^ n) ^ 2 * energy f) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg lambda)
        _ = (lambda ^ (n + 1)) ^ 2 * energy f := by rw [pow_succ]; ring

omit [Nonempty V] in
theorem zero_mean_correlation_bound (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (f : V → ℝ)
    (hf : mean f = 0) (n : Nat) :
    correlation f (iterateOperator G n f) ≤ lambda ^ n * energy f := by
  have hsq : correlation f (iterateOperator G n f) ^ 2 ≤
      (lambda ^ n * energy f) ^ 2 := by
    calc
      _ ≤ energy f * energy (iterateOperator G n f) := correlation_sq_le _ _
      _ ≤ energy f * ((lambda ^ n) ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (iterate_energy_bound G lambda certificate f hf n)
          (energy_nonnegative f)
      _ = _ := by ring
  exact le_of_sq_le_sq hsq
    (mul_nonneg (pow_nonneg certificate.nonnegative n) (energy_nonnegative f))

theorem correlation_centered (f : V → ℝ) (n : Nat) :
    correlation f (iterateOperator G n f) = mean f ^ 2 +
      correlation (fun v => f v - mean f)
        (iterateOperator G n (fun v => f v - mean f)) := by
  rw [iterate_sub_const, correlation_sub_const, mean_iterate]
  ring

end Graph

section Profiles

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

omit [Nonempty V] [Nonempty D] in
theorem edgeDensity_eq_edge_mean (bad : V × D → Bool) :
    edgeDensity bad = mean (fun e => if bad e then (1 : ℝ) else 0) :=
  (mean_prod (fun e : V × D => if bad e then (1 : ℝ) else 0)).symm

omit [Nonempty V] [Nonempty D] in
theorem edgeDensity_eq_card (bad : V × D → Bool) :
    edgeDensity bad =
      ((Finset.univ.filter (fun e => bad e = true)).card : ℝ) /
        (Fintype.card (V × D) : ℝ) := by
  rw [edgeDensity_eq_edge_mean, mean_eq_sum_div_card]
  simp only [Finset.sum_boole]

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem edgeProfile_nonnegative (bad : V × D → Bool) (v : V) : 0 ≤ edgeProfile bad v :=
  mean_nonnegative _ (fun d => by cases bad (v, d) <;> norm_num)

omit [Fintype V] [Nonempty V] in
theorem edgeProfile_le_one (bad : V × D → Bool) (v : V) : edgeProfile bad v ≤ 1 := by
  change mean (fun d => if bad (v, d) then (1 : ℝ) else 0) ≤ 1
  calc
    _ ≤ mean (fun _ : D => (1 : ℝ)) := mean_mono (fun d => by
      cases bad (v, d) <;> norm_num)
    _ = 1 := mean_const _

omit [Nonempty V] [Nonempty D] in
theorem edgeDensity_nonnegative (bad : V × D → Bool) : 0 ≤ edgeDensity bad :=
  mean_nonnegative _ (edgeProfile_nonnegative bad)

theorem edgeDensity_le_one (bad : V × D → Bool) : edgeDensity bad ≤ 1 := by
  calc
    _ ≤ mean (fun _ : V => (1 : ℝ)) := mean_mono (edgeProfile_le_one bad)
    _ = 1 := mean_const _

omit [Nonempty V] in
theorem edgeProfile_energy_le_density (bad : V × D → Bool) :
    energy (edgeProfile bad) ≤ edgeDensity bad :=
  mean_mono (fun v => by
    have h0 := edgeProfile_nonnegative bad v
    have h1 := edgeProfile_le_one bad v
    nlinarith)

theorem edgeProfile_centered_energy (bad : V × D → Bool) :
    energy (fun v => edgeProfile bad v - edgeDensity bad) ≤
      edgeDensity bad * (1 - edgeDensity bad) := by
  rw [energy_sub_const]
  have h := edgeProfile_energy_le_density bad
  change energy (edgeProfile bad) - 2 * edgeDensity bad * edgeDensity bad +
    edgeDensity bad ^ 2 ≤ _
  nlinarith

theorem returnMass_le_sharp (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 +
      lambda ^ gap * (edgeDensity bad * (1 - edgeDensity bad)) := by
  rw [returnMass_eq_correlation G bad reversal, correlation_centered]
  have hzero : mean (fun v => edgeProfile bad v - edgeDensity bad) = 0 := by
    rw [mean_sub, mean_const]
    simp only [edgeDensity, sub_self]
  have hc := zero_mean_correlation_bound G lambda certificate
    (fun v => edgeProfile bad v - edgeDensity bad) hzero gap
  have hv := mul_le_mul_of_nonneg_left (edgeProfile_centered_energy bad)
    (pow_nonneg certificate.nonnegative gap)
  change edgeDensity bad ^ 2 + _ ≤ _
  exact add_le_add (le_refl _) (hc.trans hv)

theorem returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap := by
  have h := returnMass_le_sharp G lambda certificate bad reversal gap
  have hvar : edgeDensity bad * (1 - edgeDensity bad) ≤ edgeDensity bad := by
    nlinarith [sq_nonneg (edgeDensity bad)]
  have hm := mul_le_mul_of_nonneg_left hvar (pow_nonneg certificate.nonnegative gap)
  nlinarith

theorem adjacent_returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) :
    returnMass G bad 0 ≤ edgeDensity bad := by
  have h := returnMass_le_sharp G lambda certificate bad reversal 0
  norm_num at h
  nlinarith

end Profiles

theorem geometric_sum_le (lambda : ℝ) (h0 : 0 ≤ lambda) (h1 : lambda < 1) (n : Nat) :
    (∑ k ∈ Finset.range n, lambda ^ k) ≤ 1 / (1 - lambda) := by
  have hsum : (∑ k ∈ Finset.range n, lambda ^ k) * (1 - lambda) = 1 - lambda ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  have hden : 0 < 1 - lambda := by linarith
  apply (le_div_iff₀ hden).2
  rw [hsum]
  linarith [pow_nonneg h0 n]

section ReturnSums

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

theorem sum_returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ gap ∈ Finset.range n, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda) := by
  calc
    _ ≤ ∑ gap ∈ Finset.range n,
        (edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap) :=
      Finset.sum_le_sum (fun gap _ => returnMass_le G lambda certificate bad reversal gap)
    _ = (n : ℝ) * edgeDensity bad ^ 2 +
        edgeDensity bad * (∑ gap ∈ Finset.range n, lambda ^ gap) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad * (1 / (1 - lambda)) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (geometric_sum_le lambda certificate.nonnegative certificate.lt_one n)
          (edgeDensity_nonnegative bad))
    _ = _ := by ring

theorem triangular_returnMass_sum_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
        (n : ℝ) * (edgeDensity bad / (1 - lambda)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hrow := sum_returnMass_le G lambda certificate bad reversal n
      have h := add_le_add ih hrow
      calc
        _ ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
            (n : ℝ) * (edgeDensity bad / (1 - lambda)) +
            ((n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda)) := h
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring

theorem secondMoment_return_envelope (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (n : ℝ) * edgeDensity bad +
        2 * (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad *
        (1 + 2 / (1 - lambda) + ((n : ℝ) - 1) * edgeDensity bad) := by
  calc
    _ ≤ (n : ℝ) * edgeDensity bad +
        2 * (((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
          (n : ℝ) * (edgeDensity bad / (1 - lambda))) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (triangular_returnMass_sum_le G lambda certificate bad reversal n) (by norm_num))
    _ = _ := by ring

end ReturnSums

end

end MinUncutGames.Foundations.PCP.SpectralReturn

end

end OAI
