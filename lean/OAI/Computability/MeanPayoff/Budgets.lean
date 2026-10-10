import OAI.Computability.MeanPayoff.FiniteBox

namespace OAI

section
namespace MeanPayoff

structure Budgets (n : ℕ) where
  alpha : Fin n → ℚ
  beta : Fin n → ℚ
  k : ℚ
  m : ℚ
  alpha_pos : ∀ i, 0 < alpha i
  beta_pos : ∀ i, 0 < beta i
  k_pos : 0 < k
  m_pos : 0 < m

def AdmissibleSub {n : ℕ} (F : Vec (Fin n) → Vec (Fin n))
    (a b y : Vec (Fin n)) (P : Budgets n) : Prop :=
  Subsolution F a b y ∧ mass P.alpha (lowerActive a y) ≤ P.k

def AdmissibleSuper {n : ℕ} (F : Vec (Fin n) → Vec (Fin n))
    (a b z : Vec (Fin n)) (P : Budgets n) : Prop :=
  Supersolution F a b z ∧ mass P.beta (upperActive b z) ≤ P.m

def Budgets.density {n : ℕ} (P : Budgets n) (i : Fin n) : ℚ := 1 / (P.alpha i * P.beta i)
def Budgets.totalDensity {n : ℕ} (P : Budgets n) : ℚ := mass P.density Finset.univ
def Budgets.parameter {n : ℕ} (P : Budgets n) : ℚ := P.k * P.m * P.totalDensity
def Budgets.measure {n : ℕ} (P : Budgets n) (S : Finset (Fin n)) : ℚ :=
  mass P.density S / P.totalDensity

theorem Budgets.density_pos {n : ℕ} (P : Budgets n) (i : Fin n) : 0 < P.density i :=
  one_div_pos.mpr (mul_pos (P.alpha_pos i) (P.beta_pos i))

theorem Budgets.totalDensity_pos {n : ℕ} (P : Budgets n) (hn : 0 < n) :
    0 < P.totalDensity := by
  exact Finset.sum_pos (fun i _ => P.density_pos i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem Budgets.parameter_pos {n : ℕ} (P : Budgets n) (hn : 0 < n) :
    0 < P.parameter := mul_pos (mul_pos P.k_pos P.m_pos) (P.totalDensity_pos hn)

theorem Budgets.measure_nonneg {n : ℕ} (P : Budgets n) (hn : 0 < n) (S : Finset (Fin n)) :
    0 ≤ P.measure S := div_nonneg (mass_nonneg (fun i => le_of_lt (P.density_pos i)) S)
      (le_of_lt (P.totalDensity_pos hn))

theorem Budgets.measure_univ {n : ℕ} (P : Budgets n) (hn : 0 < n) :
    P.measure Finset.univ = 1 := div_self (ne_of_gt (P.totalDensity_pos hn))

theorem Budgets.measure_compl {n : ℕ} (P : Budgets n) (hn : 0 < n) (S : Finset (Fin n)) :
    P.measure Sᶜ = 1 - P.measure S := by
  have hs : mass P.density S + mass P.density Sᶜ = P.totalDensity :=
    Finset.sum_add_sum_compl S P.density
  unfold Budgets.measure
  rw [← div_self (ne_of_gt (P.totalDensity_pos hn))]
  rw [← sub_div]
  congr 1
  linarith

def smallRankAnswer {n : ℕ} (a b : Vec (Fin n)) (P : Budgets n) : Vec (Fin n) :=
  fun i => if P.m < P.beta i then b i else a i

theorem small_rank_comparisons {n : ℕ} (P : Budgets n) (hR : P.parameter < 1)
    {F : Vec (Fin n) → Vec (Fin n)} {a b y z : Vec (Fin n)}
    (hy : AdmissibleSub F a b y P) (hz : AdmissibleSuper F a b z P) :
    y ≤ smallRankAnswer a b P ∧ smallRankAnswer a b P ≤ z := by
  have hprod (i : Fin n) : P.k * P.m < P.alpha i * P.beta i := by
    have hs := weight_le_mass (fun j => le_of_lt (P.density_pos j)) (Finset.mem_univ i)
    have hm := mul_le_mul_of_nonneg_left hs (le_of_lt (mul_pos P.k_pos P.m_pos))
    have hq : P.k * P.m / (P.alpha i * P.beta i) < 1 := by
      have : P.k * P.m * P.density i < 1 := hm.trans_lt hR
      simpa only [Budgets.density, mul_one_div] using this
    exact (div_lt_one (mul_pos (P.alpha_pos i) (P.beta_pos i))).mp hq
  have hya (i : Fin n) (hi : P.k < P.alpha i) : y i = a i := by
    have hlow : a i ≤ y i := hy.1.1.1 i
    by_contra hh
    have hm := weight_le_mass (fun j => le_of_lt (P.alpha_pos j))
      (show i ∈ lowerActive a y by simp [lowerActive]; omega)
    exact (not_lt_of_ge (hm.trans hy.2)) hi
  have hzb (i : Fin n) (hi : P.m < P.beta i) : z i = b i := by
    have hup : z i ≤ b i := hz.1.1.2 i
    by_contra hh
    have hm := weight_le_mass (fun j => le_of_lt (P.beta_pos j))
      (show i ∈ upperActive b z by simp [upperActive]; omega)
    exact (not_lt_of_ge (hm.trans hz.2)) hi
  constructor
  · intro i
    dsimp [smallRankAnswer]
    split_ifs with hi
    · exact hy.1.1.2 i
    · have hk : P.k < P.alpha i := by
        have hb : P.beta i ≤ P.m := le_of_not_gt hi
        have hp := hprod i
        nlinarith [P.alpha_pos i, P.k_pos, P.beta_pos i]
      rw [hya i hk]
  · intro i
    dsimp [smallRankAnswer]
    split_ifs with hi
    · exact (hzb i hi).symm.le
    · exact hz.1.1.1 i

def halve {n : ℕ} (a : Fin n → ℚ) (H : Finset (Fin n)) : Fin n → ℚ :=
  fun i => if i ∈ H then a i / 2 else a i

theorem halve_pos {n : ℕ} {a : Fin n → ℚ} (ha : ∀ i, 0 < a i)
    (H : Finset (Fin n)) (i : Fin n) : 0 < halve a H i := by
  unfold halve
  split_ifs
  · exact div_pos (ha i) (by norm_num)
  · exact ha i

theorem mass_halve {n : ℕ} (a : Fin n → ℚ) (H S : Finset (Fin n)) :
    mass (halve a H) S = mass a S - mass a (S ∩ H) / 2 := by
  have he (i : Fin n) : halve a H i = a i - (if i ∈ H then a i else 0) / 2 := by
    unfold halve
    split_ifs <;> ring
  simp only [mass, he, Finset.sum_sub_distrib, ← Finset.sum_div]
  congr 1
  rw [← Finset.sum_filter]
  congr 2

def Budgets.reduceK {n : ℕ} (P : Budgets n) : Budgets n :=
  { P with k := (4 / 5) * P.k, k_pos := mul_pos (by norm_num) P.k_pos }
def Budgets.reduceM {n : ℕ} (P : Budgets n) : Budgets n :=
  { P with m := (4 / 5) * P.m, m_pos := mul_pos (by norm_num) P.m_pos }
def Budgets.reweightK {n : ℕ} (P : Budgets n) (H : Finset (Fin n)) : Budgets n :=
  { P with
    alpha := halve P.alpha H
    alpha_pos := halve_pos P.alpha_pos H
    k := (3 / 5) * P.k
    k_pos := mul_pos (by norm_num) P.k_pos }
def Budgets.reweightM {n : ℕ} (P : Budgets n) (H : Finset (Fin n)) : Budgets n :=
  { P with
    beta := halve P.beta H
    beta_pos := halve_pos P.beta_pos H
    m := (3 / 5) * P.m
    m_pos := mul_pos (by norm_num) P.m_pos }

theorem Budgets.reduceK_parameter {n : ℕ} (P : Budgets n) :
    P.reduceK.parameter = (4 / 5) * P.parameter := by
  unfold Budgets.parameter Budgets.totalDensity Budgets.density Budgets.reduceK
  ring

theorem Budgets.reduceM_parameter {n : ℕ} (P : Budgets n) :
    P.reduceM.parameter = (4 / 5) * P.parameter := by
  unfold Budgets.parameter Budgets.totalDensity Budgets.density Budgets.reduceM
  ring

theorem density_reweightK {n : ℕ} (P : Budgets n) (H : Finset (Fin n)) (i : Fin n) :
    (P.reweightK H).density i = P.density i + if i ∈ H then P.density i else 0 := by
  simp only [Budgets.density, Budgets.reweightK, halve]
  split_ifs <;> ring

theorem density_reweightM {n : ℕ} (P : Budgets n) (H : Finset (Fin n)) (i : Fin n) :
    (P.reweightM H).density i = P.density i + if i ∈ H then P.density i else 0 := by
  simp only [Budgets.density, Budgets.reweightM, halve]
  split_ifs <;> ring

theorem reweight_admissible_sub {n : ℕ} {F : Vec (Fin n) → Vec (Fin n)}
    {P : Budgets n} {a b y : Vec (Fin n)} {H : Finset (Fin n)}
    (hy : AdmissibleSub F a b y P)
    (hw : (4 / 5) * P.k < mass P.alpha (lowerActive a y ∩ H)) :
    AdmissibleSub F a b y (P.reweightK H) := by
  refine ⟨hy.1, ?_⟩
  change mass (halve P.alpha H) (lowerActive a y) ≤ (3 / 5) * P.k
  rw [mass_halve]
  linarith [hy.2]

theorem reweight_admissible_super {n : ℕ} {F : Vec (Fin n) → Vec (Fin n)}
    {P : Budgets n} {a b z : Vec (Fin n)} {H : Finset (Fin n)}
    (hz : AdmissibleSuper F a b z P)
    (hw : (4 / 5) * P.m < mass P.beta (upperActive b z ∩ H)) :
    AdmissibleSuper F a b z (P.reweightM H) := by
  refine ⟨hz.1, ?_⟩
  change mass (halve P.beta H) (upperActive b z) ≤ (3 / 5) * P.m
  rw [mass_halve]
  linarith [hz.2]

theorem Budgets.reweightK_totalDensity {n : ℕ} (P : Budgets n) (H : Finset (Fin n)) :
    (P.reweightK H).totalDensity = P.totalDensity + mass P.density H := by
  simp only [Budgets.totalDensity, mass, density_reweightK, Finset.sum_add_distrib]
  congr 1
  simp

theorem Budgets.reweightM_totalDensity {n : ℕ} (P : Budgets n) (H : Finset (Fin n)) :
    (P.reweightM H).totalDensity = P.totalDensity + mass P.density H := by
  simp only [Budgets.totalDensity, mass, density_reweightM, Finset.sum_add_distrib]
  congr 1
  simp

theorem Budgets.reweightK_contraction {n : ℕ} (P : Budgets n) (hn : 0 < n)
    {H : Finset (Fin n)} (hH : P.measure H ≤ 1 / 2) :
    (P.reweightK H).parameter ≤ (9 / 10) * P.parameter := by
  have hm := (div_le_iff₀ (P.totalDensity_pos hn)).mp hH
  change (3 / 5) * P.k * P.m * (P.reweightK H).totalDensity ≤ _
  rw [P.reweightK_totalDensity]
  unfold Budgets.parameter
  have hk := mul_pos P.k_pos P.m_pos
  nlinarith [mul_le_mul_of_nonneg_left hm (le_of_lt hk)]

theorem Budgets.reweightM_contraction {n : ℕ} (P : Budgets n) (hn : 0 < n)
    {H : Finset (Fin n)} (hH : P.measure H ≤ 1 / 2) :
    (P.reweightM H).parameter ≤ (9 / 10) * P.parameter := by
  have hm := (div_le_iff₀ (P.totalDensity_pos hn)).mp hH
  change P.k * ((3 / 5) * P.m) * (P.reweightM H).totalDensity ≤ _
  rw [P.reweightM_totalDensity]
  unfold Budgets.parameter
  have hk := mul_pos P.k_pos P.m_pos
  nlinarith [mul_le_mul_of_nonneg_left hm (le_of_lt hk)]

theorem parameter_rank_exists (R : ℚ) : ∃ d : ℕ, (9 / 10 : ℚ) ^ d * R < 1 := by
  by_cases hR : 0 < R
  · obtain ⟨d, hd⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hR)
      (show (9 / 10 : ℚ) < 1 by norm_num)
    exact ⟨d, (lt_div_iff₀ hR).mp hd⟩
  · exact ⟨0, by simp; linarith⟩

noncomputable def parameterRank (R : ℚ) : ℕ := Nat.find (parameter_rank_exists R)

theorem parameterRank_spec (R : ℚ) : (9 / 10 : ℚ) ^ parameterRank R * R < 1 :=
  Nat.find_spec (parameter_rank_exists R)

theorem parameterRank_zero_iff (R : ℚ) : parameterRank R = 0 ↔ R < 1 := by
  rw [parameterRank, Nat.find_eq_zero]
  simp

theorem parameterRank_decreases {R R' : ℚ} (hR : 1 ≤ R) (h : R' ≤ (9 / 10) * R) :
    parameterRank R' < parameterRank R := by
  have hp : 0 < parameterRank R := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact (not_lt_of_ge hR) ((parameterRank_zero_iff R).mp hz)
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hs := parameterRank_spec R
  rw [hd, pow_succ] at hs
  have hs' : (9 / 10 : ℚ) ^ d * R' < 1 := by
    have hh := mul_le_mul_of_nonneg_left h (show (0 : ℚ) ≤ (9 / 10 : ℚ) ^ d by positivity)
    nlinarith
  have hmin : parameterRank R' ≤ d := Nat.find_min' (parameter_rank_exists R') hs'
  omega



inductive RandomTree (α : Type) where
  | leaf : α → RandomTree α
  | coin : RandomTree α → RandomTree α → RandomTree α

namespace RandomTree

def bind {α β : Type} : RandomTree α → (α → RandomTree β) → RandomTree β
  | .leaf a, f => f a
  | .coin l r, f => .coin (bind l f) (bind r f)

def map {α β : Type} (f : α → β) (t : RandomTree α) : RandomTree β :=
  t.bind (fun a => .leaf (f a))

def expect {α : Type} : RandomTree α → (α → ℚ) → ℚ
  | .leaf a, f => f a
  | .coin l r, f => (expect l f + expect r f) / 2

def All {α : Type} : RandomTree α → (α → Prop) → Prop
  | .leaf a, P => P a
  | .coin l r, P => All l P ∧ All r P

@[simp] theorem expect_leaf {α : Type} (a : α) (f : α → ℚ) :
    expect (.leaf a) f = f a := rfl
@[simp] theorem expect_coin {α : Type} (l r : RandomTree α) (f : α → ℚ) :
    expect (.coin l r) f = (expect l f + expect r f) / 2 := rfl

@[simp] theorem expect_bind {α β : Type} (t : RandomTree α)
    (f : α → RandomTree β) (g : β → ℚ) :
    expect (t.bind f) g = expect t (fun a => expect (f a) g) := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp [bind, hl, hr]

@[simp] theorem expect_map {α β : Type} (t : RandomTree α)
    (f : α → β) (g : β → ℚ) : expect (t.map f) g = expect t (g ∘ f) := by
  simp [map, Function.comp_def]

@[simp] theorem expect_const {α : Type} (t : RandomTree α) (c : ℚ) :
    expect t (fun _ => c) = c := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp [hl, hr]

theorem expect_add {α : Type} (t : RandomTree α) (f g : α → ℚ) :
    expect t (fun a => f a + g a) = expect t f + expect t g := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp [hl, hr]; ring

theorem expect_mul {α : Type} (t : RandomTree α) (c : ℚ) (f : α → ℚ) :
    expect t (fun a => c * f a) = c * expect t f := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp [hl, hr]; ring

theorem expect_mono_all {α : Type} (t : RandomTree α) (f g : α → ℚ)
    (h : t.All (fun a => f a ≤ g a)) : expect t f ≤ expect t g := by
  induction t with
  | leaf a => exact h
  | coin l r hl hr =>
    have := hl h.1
    have := hr h.2
    simp only [expect_coin]
    linarith

theorem all_of_forall {α : Type} (t : RandomTree α) {P : α → Prop} (h : ∀ a, P a) :
    t.All P := by
  induction t with
  | leaf a => exact h a
  | coin l r hl hr => exact ⟨hl, hr⟩

theorem expect_mono {α : Type} (t : RandomTree α) (f g : α → ℚ)
    (h : ∀ a, f a ≤ g a) : expect t f ≤ expect t g :=
  expect_mono_all t f g (all_of_forall t h)

theorem expect_nonneg {α : Type} (t : RandomTree α) (f : α → ℚ)
    (h : ∀ a, 0 ≤ f a) : 0 ≤ expect t f := by
  simpa using expect_mono t (fun _ => 0) f h

@[simp] theorem all_bind {α β : Type} (t : RandomTree α)
    (f : α → RandomTree β) (P : β → Prop) :
    (t.bind f).All P ↔ t.All (fun a => (f a).All P) := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp only [bind, All, hl, hr]

theorem all_mono {α : Type} (t : RandomTree α) {P Q : α → Prop}
    (h : t.All P) (hPQ : ∀ a, P a → Q a) : t.All Q := by
  induction t with
  | leaf a => exact hPQ a h
  | coin l r hl hr => exact ⟨hl h.1, hr h.2⟩

noncomputable def probability {α : Type} (t : RandomTree α) (P : α → Prop) : ℚ := by
  classical
  exact t.expect (fun a => if P a then 1 else 0)

theorem probability_nonneg {α : Type} (t : RandomTree α) (P : α → Prop) :
    0 ≤ t.probability P := by
  classical
  exact expect_nonneg t _ (fun a => by split_ifs <;> norm_num)

theorem probability_le_one {α : Type} (t : RandomTree α) (P : α → Prop) :
    t.probability P ≤ 1 := by
  classical
  have := expect_mono t (fun a => if P a then 1 else 0) (fun _ => 1)
    (fun a => by split_ifs <;> norm_num)
  simpa [probability] using this

theorem probability_mono {α : Type} (t : RandomTree α) {P Q : α → Prop}
    (h : ∀ a, P a → Q a) : t.probability P ≤ t.probability Q := by
  classical
  apply expect_mono
  intro a
  by_cases hp : P a <;> by_cases hq : Q a <;> simp_all

theorem probability_compl {α : Type} (t : RandomTree α) (P : α → Prop) :
    t.probability (fun a => ¬ P a) = 1 - t.probability P := by
  classical
  have he (a : α) : (if P a then (1 : ℚ) else 0) +
      (if ¬P a then (1 : ℚ) else 0) = 1 := by split_ifs <;> simp_all
  have hh := expect_add t (fun a => if P a then 1 else 0) (fun a => if ¬P a then 1 else 0)
  simp only [he, expect_const] at hh
  unfold probability
  convert (show t.expect (fun a => if ¬P a then 1 else 0) =
    1 - t.expect (fun a => if P a then 1 else 0) by linarith) using 1 ;
    congr 1 ; funext a ; by_cases h : P a <;> simp [h]

theorem qualified_bind_error {α β : Type} (t : RandomTree α) (f : α → RandomTree β)
    (Q : α → Prop) (bad : α → β → Prop) (ρ : ℚ) (_hρ : 0 ≤ ρ)
    (h : ∀ a, Q a → (f a).probability (bad a) ≤ ρ) :
    (t.bind (fun a => (f a).map (fun b => (a, b)))).probability
      (fun p => Q p.1 ∧ bad p.1 p.2) ≤ ρ * t.probability Q := by
  classical
  unfold probability
  rw [expect_bind]
  simp only [expect_map, Function.comp_def]
  rw [← expect_mul]
  apply expect_mono
  intro a
  by_cases hQ : Q a
  · simpa only [probability, hQ, true_and, ite_true, mul_one] using h a hQ
  · simp [hQ]

open scoped Classical

noncomputable def badCount {α : Type} (P : α → Prop) : List α → ℕ
  | [] => 0
  | a :: as => (if P a then 0 else 1) + badCount P as

def trials {α : Type} (t : RandomTree α) : ℕ → RandomTree (List α)
  | 0 => .leaf []
  | j + 1 => t.bind (fun a => (trials t j).map (fun as => a :: as))

theorem trials_length {α : Type} (t : RandomTree α) (J : ℕ) :
    (trials t J).All (fun as => as.length = J) := by
  induction J with
  | zero => rfl
  | succ j hj =>
    rw [trials, all_bind]
    apply all_of_forall
    intro a
    rw [map, all_bind]
    exact all_mono _ hj (fun as hs => by simp [All, hs])

noncomputable def moment {α : Type} (P : α → Prop) (as : List α) : ℚ :=
  16 ^ badCount P as

theorem moment_cons {α : Type} (P : α → Prop) (a : α) (as : List α) :
    moment P (a :: as) = (if P a then 1 else 16) * moment P as := by
  classical
  by_cases h : P a <;> simp [moment, badCount, h, pow_add]

theorem failure_moment {α : Type} (t : RandomTree α) (P : α → Prop) :
    t.expect (fun a => if P a then 1 else 16) =
      1 + 15 * t.probability (fun a => ¬ P a) := by
  classical
  have he (a : α) : (if P a then (1 : ℚ) else 16) =
      1 + 15 * (if ¬P a then 1 else 0) := by by_cases h : P a <;> norm_num [h]
  simp only [he, expect_add, expect_mul, expect_const, probability]
  congr 2
  congr 1
  funext a
  by_cases h : P a <;> simp [h]

theorem amplification_moment {α : Type} (t : RandomTree α) (P : α → Prop)
    (h : t.probability (fun a => ¬ P a) ≤ 1 / 16) (J : ℕ) :
    (trials t J).expect (moment P) ≤ 2 ^ J := by
  classical
  induction J with
  | zero => simp [trials, moment, badCount]
  | succ j hj =>
    rw [trials, expect_bind]
    simp only [expect_map, Function.comp_def, moment_cons, expect_mul]
    have he (a : α) : (if P a then (1 : ℚ) else 16) *
        (trials t j).expect (moment P) =
        (trials t j).expect (moment P) * (if P a then 1 else 16) := mul_comm _ _
    simp only [he, expect_mul, failure_moment]
    have hn := expect_nonneg (trials t j) (moment P) (fun as => by unfold moment; positivity)
    have hf := probability_nonneg t (fun a => ¬P a)
    have hu : 1 + 15 * t.probability (fun a => ¬P a) ≤ 2 := by linarith
    calc
      (trials t j).expect (moment P) * (1 + 15 * t.probability (fun a => ¬P a))
          ≤ (trials t j).expect (moment P) * 2 := mul_le_mul_of_nonneg_left hu hn
      _ ≤ 2 ^ j * 2 := mul_le_mul_of_nonneg_right hj (by norm_num)
      _ = 2 ^ (j + 1) := (pow_succ _ _).symm

theorem amplification {α : Type} (t : RandomTree α) (P : α → Prop)
    (h : t.probability (fun a => ¬ P a) ≤ 1 / 16) (J : ℕ) :
    (trials t J).probability (fun as => J ≤ 2 * badCount P as) ≤ (1 / 2 : ℚ) ^ J := by
  classical
  have he := amplification_moment t P h J
  have hm : (4 : ℚ) ^ J * (trials t J).probability (fun as => J ≤ 2 * badCount P as)
      ≤ (trials t J).expect (moment P) := by
    unfold probability
    rw [← expect_mul]
    apply expect_mono
    intro as
    split_ifs with ha
    · rw [mul_one]
      calc
        (4 : ℚ) ^ J ≤ 4 ^ (2 * badCount P as) := pow_le_pow_right₀ (by norm_num) ha
        _ = moment P as := by unfold moment; rw [pow_mul]; norm_num
    · simp only [mul_zero]
      unfold moment
      positivity
  have hh : (trials t J).probability (fun as => J ≤ 2 * badCount P as) ≤
      (2 : ℚ) ^ J / 4 ^ J := (le_div_iff₀ (by positivity)).mpr (by linarith)
  simpa only [← div_pow, show (2 : ℚ) / 4 = 1 / 2 by norm_num] using hh

end RandomTree
end MeanPayoff
end

end OAI
