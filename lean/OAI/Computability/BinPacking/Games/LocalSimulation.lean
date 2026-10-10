import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import OAI.Computability.BinPacking.Games.GameConditioning
import OAI.Computability.BinPacking.Information.GamesAdapter
import OAI.Computability.BinPacking.Information.SharedProfiles

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Repetition

open scoped BigOperators
open Information

variable {α β : Type*} [Fintype α] [Fintype β]

theorem totalVariation_triangle (p q r : α → ℝ) :
    totalVariation p r ≤ totalVariation p q + totalVariation q r := by
  have hpoint : ∀ a, |p a - r a| ≤ |p a - q a| + |q a - r a| := by
    intro a
    have := abs_add_le (p a - q a) (q a - r a)
    simpa only [sub_add_sub_cancel] using this
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [Finset.sum_add_distrib] at hsum
  unfold totalVariation
  linarith

noncomputable def conditionWeights (p : α → ℝ) (event : α → Bool) (z : ℝ) : α → ℝ :=
  fun a => if event a then p a / z else 0

theorem conditionWeights_isProbability (p : α → ℝ) (hp : IsProbability p)
    (event : α → Bool) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, (if event a then p a else 0) = z) :
    IsProbability (conditionWeights p event z) := by
  constructor
  · intro a
    dsimp [conditionWeights]
    split
    · exact div_nonneg (hp.1 a) hz.le
    · exact le_rfl
  · have hpoint : ∀ a, conditionWeights p event z a =
        (if event a then p a else 0) / z := by
      intro a
      simp only [conditionWeights]
      split <;> simp
    simp only [hpoint, div_eq_mul_inv, ← Finset.sum_mul, hmass, mul_inv_cancel₀ hz.ne']

theorem totalVariation_condition_le (p q : α → ℝ) (event : α → Bool)
    {z : ℝ} (hz : 0 < z) :
    totalVariation (conditionWeights p event z) (conditionWeights q event z) ≤
      totalVariation p q / z := by
  have hpoint : ∀ a,
      |conditionWeights p event z a - conditionWeights q event z a| ≤
        |p a - q a| / z := by
    intro a
    dsimp [conditionWeights]
    split
    · rw [← sub_div, abs_div, abs_of_pos hz]
    · simp only [sub_self, abs_zero]
      positivity
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [div_eq_mul_inv, ← Finset.sum_mul] at hsum
  have hsum' : (∑ a, |conditionWeights p event z a - conditionWeights q event z a|) ≤
      (∑ a, |p a - q a|) / z := by
    simpa only [div_eq_mul_inv] using hsum
  unfold totalVariation
  calc
    _ ≤ (∑ a, |p a - q a|) / z / 2 := div_le_div_of_nonneg_right hsum' (by norm_num)
    _ = _ := by ring

theorem totalVariation_condition_half_le (p q : α → ℝ) (event : α → Bool) :
    totalVariation (conditionWeights p event (1 / 2))
      (conditionWeights q event (1 / 2)) ≤ 2 * totalVariation p q := by
  have h := totalVariation_condition_le p q event (z := 1 / 2) (by norm_num)
  convert h using 1
  ring

theorem totalVariation_append_kernel (p q : α → ℝ) (kernel : α → β → ℝ)
    (hk : ∀ a, IsProbability (kernel a)) :
    totalVariation (fun ab : α × β => p ab.1 * kernel ab.1 ab.2)
      (fun ab : α × β => q ab.1 * kernel ab.1 ab.2) = totalVariation p q := by
  unfold totalVariation
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  have habs : ∀ b, |kernel a b| = kernel a b := fun b => abs_of_nonneg ((hk a).1 b)
  simp only [← sub_mul, abs_mul, habs, ← Finset.mul_sum, (hk a).2,
    mul_one]

noncomputable def kernelPushforward (p : α → ℝ) (kernel : α → β → ℝ) : β → ℝ :=
  fun b => ∑ a, p a * kernel a b

theorem totalVariation_kernelPushforward_le (p q : α → ℝ) (kernel : α → β → ℝ)
    (hk : ∀ a, IsProbability (kernel a)) :
    totalVariation (kernelPushforward p kernel) (kernelPushforward q kernel) ≤
      totalVariation p q := by
  have hpoint : ∀ b,
      |kernelPushforward p kernel b - kernelPushforward q kernel b| ≤
        ∑ a, |p a - q a| * kernel a b := by
    intro b
    simp only [kernelPushforward, ← Finset.sum_sub_distrib, ← sub_mul]
    have h := Finset.abs_sum_le_sum_abs (fun a => (p a - q a) * kernel a b) Finset.univ
    have habs : ∀ a, |kernel a b| = kernel a b := fun a => abs_of_nonneg ((hk a).1 b)
    simpa only [abs_mul, habs] using h
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset β)) => hpoint b)
  rw [Finset.sum_comm] at hsum
  simp only [← Finset.mul_sum, (hk _).2, mul_one] at hsum
  exact div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)

end BinPackingGames.Foundations.Repetition

namespace BinPackingGames.Foundations.Games

open scoped BigOperators

namespace FiniteDistribution

theorem pushforward_eq_of_agree_on_support
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f g : Ω → Γ)
    (h : ∀ x, μ.weight x ≠ 0 → f x = g x) :
    μ.pushforward f = μ.pushforward g := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : μ.weight x = 0
  · simp [hx]
  · rw [h x hx]

theorem product_pushforward
    {Ω Γ A B : Type*} [Fintype Ω] [Fintype Γ] [Fintype A] [Fintype B]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → A) (g : Γ → B) :
    (μ.product ν).pushforward (fun z => (f z.1, g z.2)) =
      (μ.pushforward f).product (ν.pushforward g) := by
  classical
  apply eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [pushforward, product]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = a <;> by_cases hy : g y = b <;> simp [hx, hy]

theorem table_row_weight_ne_zero
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (answers : Q → A)
    (h : (table responses).weight answers ≠ 0) (q : Q) :
    (responses q).weight (answers q) ≠ 0 := by
  intro hq
  apply h
  change (∏ r, (responses r).weight (answers r)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ q) hq

theorem table_repair_pushforward
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (repair : Q → A → A)
    (hrepair : ∀ q a, (responses q).weight a ≠ 0 → repair q a = a) (q : Q) :
    (table responses).pushforward (fun answers => repair q (answers q)) =
      responses q := by
  calc
    _ = (table responses).pushforward (fun answers => answers q) := by
      apply pushforward_eq_of_agree_on_support
      intro answers h
      exact hrepair q (answers q) (table_row_weight_ne_zero responses answers h q)
    _ = responses q := table_eval_pushforward responses q

end FiniteDistribution

namespace KernelSampling

abbrev Seed (Q₁ Q₂ A B : Type*) := (Q₁ → A) × (Q₂ → B)

def readLeft {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₁) : A := seed.1 q
def readRight {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₂) : B := seed.2 q

def seedLaw {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B) :
    FiniteDistribution (Seed Q₁ Q₂ A B) :=
  (FiniteDistribution.table left).product (FiniteDistribution.table right)

theorem read_joint_pushforward {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B)
    (x : Q₁) (y : Q₂) :
    (seedLaw left right).pushforward (fun seed => (readLeft seed x, readRight seed y)) =
      (left x).product (right y) := by
  unfold seedLaw readLeft readRight
  rw [FiniteDistribution.product_pushforward
      (FiniteDistribution.table left) (FiniteDistribution.table right)
      (fun answers => answers x) (fun answers => answers y),
    FiniteDistribution.table_eval_pushforward, FiniteDistribution.table_eval_pushforward]

theorem repaired_joint_pushforward {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B)
    (repairLeft : Q₁ → A → A) (repairRight : Q₂ → B → B)
    (hleft : ∀ x a, (left x).weight a ≠ 0 → repairLeft x a = a)
    (hright : ∀ y b, (right y).weight b ≠ 0 → repairRight y b = b)
    (x : Q₁) (y : Q₂) :
    (seedLaw left right).pushforward (fun seed =>
      (repairLeft x (readLeft seed x), repairRight y (readRight seed y))) =
      (left x).product (right y) := by
  unfold seedLaw readLeft readRight
  rw [FiniteDistribution.product_pushforward
      (FiniteDistribution.table left) (FiniteDistribution.table right)
      (fun answers => repairLeft x (answers x)) (fun answers => repairRight y (answers y)),
    FiniteDistribution.table_repair_pushforward left repairLeft hleft,
    FiniteDistribution.table_repair_pushforward right repairRight hright]

variable {I A B S : Type*} [DecidableEq I]

def completedLeft (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) : I → A :=
  Function.update (readLeft seed q) j q.1

def completedRight (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) : I → B :=
  Function.update (readRight seed q) j q.1

@[simp] theorem completedLeft_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) :
    completedLeft j seed q j = q.1 := by simp [completedLeft]

@[simp] theorem completedRight_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) :
    completedRight j seed q j = q.1 := by simp [completedRight]

private theorem update_eq_of_coordinate (xs : I → A) (j : I) (a : A)
    (h : xs j = a) : Function.update xs j a = xs := by
  funext i
  by_cases hi : i = j <;> simp [Function.update, hi, h]

theorem completed_joint_pushforward
    [Fintype I] [Fintype A] [Fintype B] [Fintype S]
    [DecidableEq A] [DecidableEq B] [DecidableEq S]
    (left : (A × S) → FiniteDistribution (I → A))
    (right : (B × S) → FiniteDistribution (I → B)) (j : I)
    (hleft : ∀ q xs, (left q).weight xs ≠ 0 → xs j = q.1)
    (hright : ∀ q ys, (right q).weight ys ≠ 0 → ys j = q.1)
    (x : A × S) (y : B × S) :
    (seedLaw left right).pushforward
        (fun seed => (completedLeft j seed x, completedRight j seed y)) =
      (left x).product (right y) := by
  apply repaired_joint_pushforward left right
    (fun q xs => Function.update xs j q.1) (fun q ys => Function.update ys j q.1)
  · intro q xs h
    exact update_eq_of_coordinate xs j q.1 (hleft q xs h)
  · intro q ys h
    exact update_eq_of_coordinate ys j q.1 (hright q ys h)

end KernelSampling
end BinPackingGames.Foundations.Games

namespace BinPackingGames.Foundations.Repetition

open scoped BigOperators
open Information

private theorem min_half_formula (x y : ℝ) :
    min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem sum_min_one_sub_tv {Ω : Type*} [Fintype Ω]
    (p q : Ω → ℝ) (hp : IsProbability p) (hq : IsProbability q) :
    (∑ z, min (p z) (q z)) = 1 - totalVariation p q := by
  classical
  simp_rw [min_half_formula]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp.2, hq.2, totalVariation]
  ring

private theorem discount_le_self {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c / (1 + t) ≤ c := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + t)).2
  nlinarith [mul_nonneg hc ht]

private theorem discount_loss_le_mul {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c - c / (1 + t) ≤ c * t := by
  have hd : 0 < 1 + t := by linarith
  have hid : c - c / (1 + t) = c * t / (1 + t) := by
    field_simp [hd.ne']
    ring
  rw [hid]
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg (mul_nonneg hc ht) ht]

noncomputable def discountedCommonMass {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (t : X → ℝ) : ℝ :=
  ∑ z, min (p z) (min (a z) (b z)) / (1 + t z.1)

theorem discounted_common_mass_bounds {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (μ t : X → ℝ)
    (hp : IsProbability p) (ha : IsProbability a) (hb : IsProbability b)
    (ht : ∀ x, 0 ≤ t x)
    (hrow : ∀ x, (∑ s, a (x, s)) = μ x)
    (htv : (∑ x, μ x * t x) = totalVariation a b) :
    1 - 2 * totalVariation p a - 2 * totalVariation p b ≤ discountedCommonMass p a b t ∧
      discountedCommonMass p a b t ≤ 1 := by
  classical
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have hC0 : ∀ z, 0 ≤ C z := by
    intro z
    exact le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
  have hCp : ∀ z, C z ≤ p z := by
    intro z
    exact min_le_left _ _
  have hCa : ∀ z, C z ≤ a z := by
    intro z
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmass : 1 - totalVariation p a - totalVariation p b ≤ ∑ z, C z := by
    have hpoint : ∀ z, min (p z) (a z) + min (p z) (b z) - p z ≤ C z := by
      intro z
      dsimp [C]
      refine le_min ?_ (le_min ?_ ?_)
      · linarith [min_le_left (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (b z), min_le_left (p z) (a z)]
    have hsum := Finset.sum_le_sum
      (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
    rw [sum_min_one_sub_tv p a hp ha, sum_min_one_sub_tv p b hp hb, hp.2] at hsum
    linarith
  have hrowC : ∀ x, (∑ s, C (x, s)) ≤ μ x := by
    intro x
    calc
      (∑ s, C (x, s)) ≤ ∑ s, a (x, s) := Finset.sum_le_sum (fun s _ => hCa (x, s))
      _ = μ x := hrow x
  have hweighted : (∑ z, C z * t z.1) ≤ totalVariation a b := by
    rw [← htv, Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro x _
    change (∑ s, C (x, s) * t x) ≤ μ x * t x
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrowC x) (ht x)
  have hloss : (∑ z, C z) - discountedCommonMass p a b t ≤ ∑ z, C z * t z.1 := by
    change (∑ z, C z) - (∑ z, C z / (1 + t z.1)) ≤ ∑ z, C z * t z.1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun z _ => discount_loss_le_mul (hC0 z) (ht z.1))
  have htriangle : totalVariation a b ≤ totalVariation p a + totalVariation p b := by
    have h := totalVariation_triangle a p b
    rw [totalVariation_symm a p] at h
    exact h
  have hupper : discountedCommonMass p a b t ≤ 1 := by
    change (∑ z, C z / (1 + t z.1)) ≤ 1
    calc
      _ ≤ ∑ z, p z := Finset.sum_le_sum
        (fun z _ => (discount_le_self (hC0 z) (ht z.1)).trans (hCp z))
      _ = 1 := hp.2
  exact ⟨by linarith, hupper⟩

noncomputable def diagonalWeights {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) : X × S × S → ℝ := by
  classical
  exact fun z => if z.2.1 = z.2.2 then p (z.1, z.2.1) else 0

theorem diagonalWeights_isProbability {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (hp : IsProbability p) : IsProbability (diagonalWeights p) := by
  classical
  constructor
  · intro z
    dsimp [diagonalWeights]
    split
    · exact hp.1 _
    · exact le_rfl
  · simpa [diagonalWeights, Fintype.sum_prod_type] using hp.2

theorem diagonal_overlap_identity {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (sim : X × S × S → ℝ)
    (hp : IsProbability p) (hsim : IsProbability sim) :
    totalVariation sim (diagonalWeights p) =
      1 - ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
  classical
  have h := sum_min_one_sub_tv sim (diagonalWeights p) hsim (diagonalWeights_isProbability p hp)
  have heq : (∑ z, min (sim z) (diagonalWeights p z)) =
      ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
    simp only [Fintype.sum_prod_type, diagonalWeights]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro s _
    have hpoint : ∀ s', min (sim (x, s, s')) (if s = s' then p (x, s) else 0) =
        if s = s' then min (p (x, s)) (sim (x, s, s')) else 0 := by
      intro s'
      by_cases he : s = s'
      · simp [he, min_comm]
      · simp [he, min_eq_right (hsim.1 (x, s, s'))]
    simp only [hpoint]
    simp
  rw [heq] at h
  linarith

theorem diagonal_sampler_totalVariation_le {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (μ : X → ℝ) (L R : X → S → ℝ)
    (sim : X × S × S → ℝ) (hp : IsProbability p) (hμ : IsProbability μ)
    (hL : ∀ x, IsProbability (L x)) (hR : ∀ x, IsProbability (R x))
    (hsim : IsProbability sim) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hdiag : ∀ x s, μ x * min (L x s) (R x s) /
      (1 + totalVariation (L x) (R x)) * (1 - τ) ≤ sim (x, s, s)) :
    totalVariation sim (diagonalWeights p) ≤
      2 * totalVariation p (fun z => μ z.1 * L z.1 z.2) +
      2 * totalVariation p (fun z => μ z.1 * R z.1 z.2) + τ := by
  classical
  let a : X × S → ℝ := fun z => μ z.1 * L z.1 z.2
  let b : X × S → ℝ := fun z => μ z.1 * R z.1 z.2
  let t : X → ℝ := fun x => totalVariation (L x) (R x)
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have ha : IsProbability a := kernelProduct_isProbability μ L hμ hL
  have hb : IsProbability b := kernelProduct_isProbability μ R hμ hR
  have ht : ∀ x, 0 ≤ t x := fun x => totalVariation_nonneg (L x) (R x)
  have hrow : ∀ x, (∑ s, a (x, s)) = μ x := by
    intro x
    simp only [a, ← Finset.mul_sum, (hL x).2, mul_one]
  have htv : (∑ x, μ x * t x) = totalVariation a b :=
    (totalVariation_joint_common_weights μ L R hμ.1).symm
  obtain ⟨hBlower, hBupper⟩ := discounted_common_mass_bounds p a b μ t hp ha hb ht hrow htv
  have hpoint : ∀ z : X × S,
      (1 - τ) * (C z / (1 + t z.1)) ≤ min (p z) (sim (z.1, z.2, z.2)) := by
    intro z
    have hden : 0 < 1 + t z.1 := by linarith [ht z.1]
    have hC0 : 0 ≤ C z := le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
    have hCp : C z ≤ p z := min_le_left _ _
    have hdisc0 : 0 ≤ C z / (1 + t z.1) := div_nonneg hC0 hden.le
    have hmin : min (a z) (b z) = μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      dsimp [a, b]
      rcases le_total (L z.1 z.2) (R z.1 z.2) with h | h
      · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
      · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
    have hCmin : C z ≤ μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      rw [← hmin]
      exact min_le_right _ _
    apply le_min
    · calc
        _ ≤ 1 * (C z / (1 + t z.1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hdisc0
        _ ≤ C z := by simpa using discount_le_self hC0 (ht z.1)
        _ ≤ p z := hCp
    · have hd := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hCmin hden.le) (by linarith : 0 ≤ 1 - τ)
      calc
        _ ≤ (1 - τ) * (μ z.1 * min (L z.1 z.2) (R z.1 z.2) / (1 + t z.1)) := hd
        _ ≤ sim (z.1, z.2, z.2) := by
          simpa only [t, mul_comm] using hdiag z.1 z.2
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
  rw [← Finset.mul_sum] at hsum
  change (1 - τ) * discountedCommonMass p a b t ≤ _ at hsum
  rw [diagonal_overlap_identity p sim hp hsim]
  have hτB := mul_le_mul_of_nonneg_left hBupper hτ0
  change 1 - _ ≤ 2 * totalVariation p a + 2 * totalVariation p b + τ
  nlinarith

end BinPackingGames.Foundations.Repetition

namespace BinPackingGames.Foundations.Games.FiniteDistribution
open scoped BigOperators
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem weight_eq_probability_singleton [DecidableEq A] (μ : FiniteDistribution A) (a : A) :
    μ.weight a = μ.probability (fun x => decide (x = a)) := by
  classical
  simp [probability]

theorem pushforward_comp (μ : FiniteDistribution A) (f : A → B) (g : B → C) :
    (μ.pushforward f).pushforward g = μ.pushforward (fun a => g (f a)) := by
  classical
  apply eq_of_weight_eq
  intro c
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward]

theorem transport_eq_pushforward (μ : FiniteDistribution A) (e : A ≃ B) :
    μ.transport e = μ.pushforward e := by
  classical
  apply eq_of_weight_eq
  intro b
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton,
    probability_transport, probability_pushforward]

theorem expectation_pushforward (μ : FiniteDistribution A) (f : A → B) (h : B → ℝ) :
    (μ.pushforward f).expectation h = μ.expectation (fun a => h (f a)) := by
  classical
  simp only [expectation, pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem pushforward_mixture (μ : FiniteDistribution A) (ν : A → FiniteDistribution B)
    (f : B → C) :
    (μ.mixture ν).pushforward f = μ.mixture (fun a => (ν a).pushforward f) := by
  classical
  apply eq_of_weight_eq
  intro c
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward, probability_mixture]

end BinPackingGames.Foundations.Games.FiniteDistribution

namespace BinPackingGames.Foundations.Repetition

open scoped BigOperators
open Games

universe u

def TraceSeed (σ : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => σ × TraceSeed σ n

instance traceSeedFintype {σ : Type*} [Fintype σ] (n : Nat) : Fintype (TraceSeed σ n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (σ × TraceSeed σ n))

instance traceSeedUniqueZero {σ : Type*} : Unique (TraceSeed σ 0) :=
  inferInstanceAs (Unique PUnit)

def traceList {σ : Type*} : (n : Nat) → TraceSeed σ n → List σ
  | 0, _ => []
  | n + 1, seed => seed.1 :: traceList n seed.2

def traceSeedLaw {σ : Type*} [Fintype σ] (μ : FiniteDistribution σ) :
    (n : Nat) → FiniteDistribution (TraceSeed σ n)
  | 0 => { weight := fun _ => 1, nonnegative := by intro; norm_num,
           normalized := by simp }
  | n + 1 => μ.product (traceSeedLaw μ n)

theorem traceSeedLaw_expectation {σ : Type*} [Fintype σ]
    (μ : FiniteDistribution σ) (n : Nat) (f : List σ → ℝ) :
    (traceSeedLaw μ n).expectation (fun seed => f (traceList n seed)) =
      CorrelatedSampling.traceAverage μ.weight n f := by
  induction n generalizing f with
  | zero => simp [traceSeedLaw, traceList, FiniteDistribution.expectation,
      CorrelatedSampling.traceAverage]
  | succ n ih =>
      change (μ.product (traceSeedLaw μ n)).expectation
        (fun seed => f (seed.1 :: traceList n seed.2)) = _
      rw [FiniteDistribution.expectation_product]
      simp only [CorrelatedSampling.traceAverage, FiniteDistribution.expectation]
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      exact ih (fun xs => f (s :: xs))

def sharedOutputLaw {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) :
    FiniteDistribution ((X × Y) × S × S) :=
  (μ.product seedLaw).pushforward
    (fun z => (z.1, left z.2 z.1.1, right z.2 z.1.2))

theorem sharedOutputLaw_weight {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) (x : X) (y : Y) (a b : S) :
    (sharedOutputLaw μ seedLaw left right).weight ((x,y),a,b) =
      μ.weight (x,y) * seedLaw.expectation
        (fun seed => if left seed x = a ∧ right seed y = b then 1 else 0) := by
  classical
  simp only [sharedOutputLaw, FiniteDistribution.pushforward,
    FiniteDistribution.product, Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [and_assoc, ite_and]
  simp [FiniteDistribution.expectation, Finset.mul_sum, mul_ite]

open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

def samplerLocal (thresholds : List ℝ) (profile : X → FiniteDistribution S)
    (fallback : S) (n : Nat) (seed : TraceSeed (RectangleSeed thresholds S) n)
    (x : X) : S :=
  localSample (rectangleAccept thresholds (profile x).weight) Prod.fst fallback
    (traceList n seed)

def samplerOutputLaw (thresholds : List ℝ) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) : FiniteDistribution ((X × Y) × S × S) :=
  sharedOutputLaw μ (traceSeedLaw (rectangleDistribution thresholds) n)
    (samplerLocal thresholds L fallback n) (samplerLocal thresholds R fallback n)

omit [Nonempty S] [DecidableEq S] in
theorem probability_weight_le_one (μ : FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

theorem samplerOutputLaw_diagonal (thresholds : List ℝ)
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (hL : ∀ x s, (L x).weight s ∈ thresholds)
    (hR : ∀ y s, (R y).weight s ∈ thresholds)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds (L x).weight s ||
            rectangleAccept thresholds (R y).weight s)) ^ n) ≤
      (samplerOutputLaw thresholds μ L R fallback n).weight ((x,y),a,a) := by
  have h := rectangle_label_diagonal_bound thresholds (L x).weight (R y).weight
    fallback a (hL x) (hR y) (L x).nonnegative (R y).nonnegative
    (probability_weight_le_one (L x)) (probability_weight_le_one (R y))
    (L x).normalized (R y).normalized n
  rw [samplerOutputLaw, sharedOutputLaw_weight]
  have he : (traceSeedLaw (rectangleDistribution (α := S) thresholds) n).expectation
      (fun seed => if samplerLocal thresholds L fallback n seed x = a ∧
        samplerLocal thresholds R fallback n seed y = a then 1 else 0) =
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds (L x).weight)
          (rectangleAccept thresholds (R y).weight) Prod.fst fallback a) := by
    exact traceSeedLaw_expectation (rectangleDistribution (α := S) thresholds) n
      (localDiagonal (rectangleAccept thresholds (L x).weight)
        (rectangleAccept thresholds (R y).weight) Prod.fst fallback a)
  rw [he]
  simp only [Information.totalVariation, CorrelatedSampling.totalVariation] at h ⊢
  simpa only [mul_div_assoc, mul_assoc] using
    mul_le_mul_of_nonneg_left h (μ.nonnegative (x,y))

theorem samplerOutputLaw_uniform_diagonal
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - uniformRejectionRate S ^ n) ≤
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight ((x,y),a,a) := by
  have hp := pow_le_pow_left₀ (sharedProfileReject_nonnegative L R x y)
    (sharedProfile_reject_le_rate L R x y) n
  have hco : 0 ≤ μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
      (1 + Information.totalVariation (L x).weight (R y).weight) :=
    div_nonneg (mul_nonneg (μ.nonnegative (x,y))
      (le_min ((L x).nonnegative a) ((R y).nonnegative a)))
      (by linarith [Information.totalVariation_nonneg (L x).weight (R y).weight])
  have h := samplerOutputLaw_diagonal (sharedProfileThresholds L R) μ L R
    (left_mem_sharedProfileThresholds L R) (right_mem_sharedProfileThresholds L R)
    fallback n x y a
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hp 1) hco).trans h

theorem samplerOutputLaw_totalVariation
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) :
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) +
      uniformRejectionRate S ^ n := by
  apply diagonal_sampler_totalVariation_le p.weight μ.weight
    (fun xy => (L xy.1).weight) (fun xy => (R xy.2).weight) _
    (Information.gameLaw_isProbability p) (Information.gameLaw_isProbability μ)
    (fun xy => Information.gameLaw_isProbability (L xy.1))
    (fun xy => Information.gameLaw_isProbability (R xy.2))
    (Information.gameLaw_isProbability _)
    (pow_nonneg (uniformRejectionRate_nonnegative S) n)
  · exact pow_le_one₀ (uniformRejectionRate_nonnegative S)
      (uniformRejectionRate_lt_one S).le
  · intro xy a
    exact samplerOutputLaw_uniform_diagonal μ L R fallback n xy.1 xy.2 a

theorem samplerOutputLaw_arbitrarily_close
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (η : ℝ) (hη : 0 < η) : ∃ n : Nat,
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) + η := by
  obtain ⟨n,hn⟩ := exists_uniformRejectionRate_pow_lt S η hη
  exact ⟨n, (samplerOutputLaw_totalVariation p μ L R fallback n).trans
    (by linarith)⟩

end BinPackingGames.Foundations.Repetition

namespace BinPackingGames.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

section DistributionIdentities

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem mixture_pushforward_base (μ : FiniteDistribution A) (f : A → B)
    (K : B → FiniteDistribution C) :
    (μ.pushforward f).mixture K = μ.mixture (fun a => K (f a)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  exact FiniteDistribution.expectation_pushforward μ f (fun b => (K b).weight c)

theorem product_pushforward_eq_mixture_right (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (f : A × B → C) :
    (μ.product ν).pushforward f =
      ν.mixture (fun b => μ.pushforward (fun a => f (a, b))) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f (a, b) = c <;> simp [h, mul_comm]

theorem product_product_pushforward_eq_mixture (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (κ : FiniteDistribution C) (f : A → B → C → D) :
    (μ.product (ν.product κ)).pushforward (fun z => f z.1 z.2.1 z.2.2) =
      (μ.product ν).mixture
        (fun z => κ.pushforward (fun c => f z.1 z.2 c)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro d
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

theorem mixture_totalVariation_le (μ ν : FiniteDistribution A)
    (K : A → FiniteDistribution B) :
    (μ.mixture K).totalVariation (ν.mixture K) ≤ μ.totalVariation ν := by
  simpa only [FiniteDistribution.totalVariation, FiniteDistribution.mixture,
    Information.totalVariation, kernelPushforward] using
      totalVariation_kernelPushforward_le μ.weight ν.weight
        (fun a => (K a).weight) (fun a => Information.gameLaw_isProbability (K a))

end DistributionIdentities

section Diagonal

variable {Z S : Type*} [Fintype Z] [Fintype S]

def diagonalLaw (σ : FiniteDistribution (Z × S)) : FiniteDistribution (Z × S × S) :=
  Information.toGameLaw (diagonalWeights σ.weight)
    (diagonalWeights_isProbability _ (Information.gameLaw_isProbability σ))

theorem diagonalLaw_eq_pushforward (σ : FiniteDistribution (Z × S)) :
    diagonalLaw σ = σ.pushforward (fun z => (z.1, z.2, z.2)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨z, a, b⟩
  change diagonalWeights σ.weight (z, a, b) =
    (σ.pushforward (fun t => (t.1, t.2, t.2))).weight (z, a, b)
  simp only [diagonalWeights, FiniteDistribution.pushforward,
    Fintype.sum_prod_type, Prod.mk.injEq]
  by_cases hab : a = b
  · subst b
    simp [ite_and]
  · simp [hab, ite_and]

theorem diagonalLaw_mixture {T : Type*} [Fintype T]
    (σ : FiniteDistribution (Z × S)) (K : Z × S × S → FiniteDistribution T) :
    (diagonalLaw σ).mixture K = σ.mixture (fun z => K (z.1, z.2, z.2)) := by
  rw [diagonalLaw_eq_pushforward, mixture_pushforward_base]

end Diagonal

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

abbrev Seed (Γ X Y S U V : Type*) :=
  Γ × KernelSampling.Seed (X × S) (Y × S) U V

def seedLaw (γ : FiniteDistribution Γ)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (Seed Γ X Y S U V) :=
  γ.product (KernelSampling.seedLaw L R)

def left (sL : Γ → X → S) (seed : Seed Γ X Y S U V) (x : X) : U :=
  KernelSampling.readLeft seed.2 (x, sL seed.1 x)

def right (sR : Γ → Y → S) (seed : Seed Γ X Y S U V) (y : Y) : V :=
  KernelSampling.readRight seed.2 (y, sR seed.1 y)

def completionKernel (L : X × S → FiniteDistribution U)
    (R : Y × S → FiniteDistribution V) (z : (X × Y) × S × S) :
    FiniteDistribution (U × V) :=
  (L (z.1.1, z.2.1)).product (R (z.1.2, z.2.2))

def outputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (U × V) :=
  (seedLaw γ L R).mixture (fun seed =>
    μ.pushforward (fun q => (left sL seed q.1, right sR seed q.2)))

theorem outputLaw_eq_product_pushforward
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (μ.product (seedLaw γ L R)).pushforward
        (fun z => (left sL z.2 z.1.1, right sR z.2 z.1.2)) := by
  exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
    (fun z : (X × Y) × Seed Γ X Y S U V =>
      (left sL z.2 z.1.1, right sR z.2 z.1.2))).symm

theorem outputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    outputLaw μ γ sL sR L R =
        (μ.product γ).mixture (fun z =>
          (KernelSampling.seedLaw L R).pushforward (fun table =>
            (KernelSampling.readLeft table (z.1.1, sL z.2 z.1.1),
             KernelSampling.readRight table (z.1.2, sR z.2 z.1.2)))) := by
      rw [outputLaw_eq_product_pushforward]
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.readLeft table (q.1, sL seed q.1),
           KernelSampling.readRight table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.read_joint_pushforward L R
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

omit [DecidableEq X] [DecidableEq Y] [DecidableEq S] in

theorem diagonalLaw_completion_mixture
    (σ : FiniteDistribution ((X × Y) × S))
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    (diagonalLaw σ).mixture (completionKernel L R) =
      σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2))) := by
  exact diagonalLaw_mixture σ (completionKernel L R)

theorem outputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (outputLaw μ γ sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [outputLaw_eq_mixture, ← diagonalLaw_completion_mixture σ L R]
  exact mixture_totalVariation_le _ _ (completionKernel L R)

end Completion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def coordinateLeft (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) : I → X :=
  KernelSampling.completedLeft j seed.2 (x, sL seed.1 x)

def coordinateRight (j : I) (sR : Γ → Y → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (y : Y) : I → Y :=
  KernelSampling.completedRight j seed.2 (y, sR seed.1 y)

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
@[simp] theorem coordinateLeft_preserves (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) :
    coordinateLeft j sL seed x j = x := by
  simp [coordinateLeft]

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
@[simp] theorem coordinateRight_preserves (j : I) (sR : Γ → Y → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (y : Y) :
    coordinateRight j sR seed y j = y := by
  simp [coordinateRight]

def coordinateOutputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y)) :
    FiniteDistribution ((I → X) × (I → Y)) :=
  (seedLaw γ L R).mixture (fun seed => μ.pushforward
    (fun q => (coordinateLeft j sL seed q.1, coordinateRight j sR seed q.2)))

theorem coordinateOutputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    coordinateOutputLaw μ γ j sL sR L R =
        (μ.product (seedLaw γ L R)).pushforward
          (fun z => (coordinateLeft j sL z.2 z.1.1,
            coordinateRight j sR z.2 z.1.2)) := by
      exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
        (fun z : (X × Y) × Seed Γ X Y S (I → X) (I → Y) =>
          (coordinateLeft j sL z.2 z.1.1, coordinateRight j sR z.2 z.1.2))).symm
    _ = (μ.product γ).mixture (fun z =>
        (KernelSampling.seedLaw L R).pushforward (fun table =>
          (KernelSampling.completedLeft j table (z.1.1, sL z.2 z.1.1),
           KernelSampling.completedRight j table (z.1.2, sR z.2 z.1.2)))) := by
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.completedLeft j table (q.1, sL seed q.1),
           KernelSampling.completedRight j table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.completed_joint_pushforward L R j hL hR
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

theorem coordinateOutputLaw_eq_outputLaw
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R = outputLaw μ γ sL sR L R := by
  rw [coordinateOutputLaw_eq_mixture μ γ j sL sR L R hL hR, outputLaw_eq_mixture]

theorem coordinateOutputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (coordinateOutputLaw μ γ j sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [coordinateOutputLaw_eq_outputLaw μ γ j sL sR L R hL hR]
  exact outputLaw_totalVariation_le μ γ sL sR L R σ

end BinPackingGames.Foundations.Repetition.CompletedSampling

namespace BinPackingGames.Foundations.Repetition
open scoped BigOperators
open Games CorrelatedSampling
variable {Q₁ Q₂ A₁ A₂ S : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype S]
  [Nonempty A₁] [Nonempty A₂] [Nonempty S]
  [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq S] {n : Nat}

theorem coordinate_probability_le_value_of_local_completion
    (G : Game Q₁ Q₂ A₁ A₂) (j : Fin n)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (σ : FiniteDistribution ((Q₁ × Q₂) × S))
    (profileL : Q₁ → FiniteDistribution S) (profileR : Q₂ → FiniteDistribution S)
    (completionL : Q₁ × S → FiniteDistribution (Fin n → Q₁))
    (completionR : Q₂ × S → FiniteDistribution (Fin n → Q₂))
    (supportL : ∀ q xs, (completionL q).weight xs ≠ 0 → xs j = q.1)
    (supportR : ∀ q ys, (completionR q).weight ys ≠ 0 → ys j = q.1)
    (fallback : S) :
    (σ.mixture (fun z => (completionL (z.1.1,z.2)).product
      (completionR (z.1.2,z.2)))).probability (G.coordinateWin strategy j) ≤
      G.value +
        (2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
         2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)) := by
  let targetLaw := σ.mixture (fun z => (completionL (z.1.1,z.2)).product (completionR (z.1.2,z.2)))
  let δ := 2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
    2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)
  change targetLaw.probability (G.coordinateWin strategy j) ≤ G.value + δ
  by_contra h
  have gap : 0 < targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ) :=
    sub_pos.mpr (lt_of_not_ge h)
  let η := (targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ)) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨N,hN⟩ := samplerOutputLaw_arbitrarily_close σ G.questions profileL profileR fallback η hη
  let thresholds := sharedProfileThresholds profileL profileR
  let γ := traceSeedLaw (rectangleDistribution (α := S) thresholds) N
  let sL := samplerLocal thresholds profileL fallback N
  let sR := samplerLocal thresholds profileR fallback N
  have hvariation := CompletedSampling.coordinateOutputLaw_totalVariation_le
    G.questions γ j sL sR completionL completionR supportL supportR σ
  have hclose : (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw ≤ δ + η :=
    hvariation.trans hN
  have hsuccess := G.coordinate_probability_le_value_add_embedding_distance j targetLaw
    (CompletedSampling.seedLaw γ completionL completionR)
    (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)
    (CompletedSampling.coordinateLeft_preserves j sL)
    (CompletedSampling.coordinateRight_preserves j sR) strategy
  have hsym : targetLaw.totalVariation
      (G.localEmbeddingLaw (CompletedSampling.seedLaw γ completionL completionR)
        (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)) =
      (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw := by
    unfold FiniteDistribution.totalVariation
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    exact abs_sub_comm _ _
  rw [hsym] at hsuccess
  dsimp [η] at hclose
  linarith

end BinPackingGames.Foundations.Repetition

end

end OAI
