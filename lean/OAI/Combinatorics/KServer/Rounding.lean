import Mathlib

namespace OAI

/- Prescribed correlated-total rounding and minimization over finite joint laws, without an independence requirement. -/


noncomputable section
open Finset
open scoped BigOperators
namespace KServer.Rounding

variable {J : Type*} [Fintype J] [DecidableEq J]

def move (p : J → ℝ) (x y : J) (ε : ℝ) : J → ℝ :=
  fun z => p z + ε * ((if z = y then 1 else 0) - (if z = x then 1 else 0))

omit [Fintype J] in
lemma move_nonneg {p : J → ℝ} (hp : ∀ z, 0 ≤ p z) {x y : J} {ε : ℝ}
    (hε : 0 ≤ ε) (hx : ε ≤ p x) : ∀ z, 0 ≤ move p x y ε z := by
  intro z
  by_cases hz : z = x
  · subst z
    by_cases hy : x = y
    · simp [move, hy, hp]
    · simp only [move, ite_eq_right hy, ite_true]
      linarith
  · by_cases hy : z = y
    · simp only [move, ite_eq_left hy, ite_eq_right hz]
      linarith [hp z]
    · simpa only [move, ite_eq_right hy, ite_eq_right hz, sub_self, mul_zero, add_zero] using hp z

lemma move_sum (p : J → ℝ) (x y : J) (ε : ℝ) (f : J → ℝ) :
    (∑ z, move p x y ε z * f z) = (∑ z, p z * f z) + ε * (f y - f x) := by
  calc (∑ z, move p x y ε z * f z) =
      ∑ z, (p z * f z + (if z = y then ε * f z else 0) -
        (if z = x then ε * f z else 0)) := by
          apply sum_congr rfl
          intro z _
          simp only [move]
          split_ifs <;> ring
    _ = _ := by rw [sum_sub_distrib, sum_add_distrib]; simp; ring

omit [Fintype J] in
lemma move_coordinate (p : J → ℝ) {x y z : J} {ε : ℝ} (hε : 0 ≤ ε)
    (hz : z ≠ x) : p z ≤ move p x y ε z := by
  by_cases hy : z = y
  · simp only [move, ite_eq_left hy, ite_eq_right hz]; linarith
  · simp [move, hy, hz]

variable {S I : Type*} [Fintype S] [Fintype I] [DecidableEq S] [DecidableEq I]

/-- Each fiber records the actual observed total, not a conditional mean. -/
abbrev Outcome (r : S → ℕ) := {x : S × Finset I // x.2.card = r x.1}

def subset {r : S → ℕ} (x : Outcome (I := I) r) : Finset I := x.val.2
def state {r : S → ℕ} (x : Outcome (I := I) r) : S := x.val.1

def Marginal {r : S → ℕ} (p : Outcome (I := I) r → ℝ) (i : I) : ℝ :=
  ∑ x, p x * (if i ∈ subset x then 1 else 0)

def Mass {r : S → ℕ} (p : Outcome (I := I) r → ℝ) (ω : S) : ℝ :=
  ∑ x, p x * (if state x = ω then 1 else 0)

def Feasible {r : S → ℕ} (p₀ p : Outcome (I := I) r → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∀ ω, Mass p ω = Mass p₀ ω

omit [DecidableEq I] in
lemma mass_total {r : S → ℕ} (p : Outcome (I := I) r → ℝ) :
    (∑ ω, Mass p ω) = ∑ x, p x := by
  simp only [Mass]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp

lemma marginal_total {r : S → ℕ} (p : Outcome (I := I) r → ℝ) :
    (∑ i, Marginal p i) = ∑ ω, Mass p ω * r ω := by
  simp only [Marginal, Mass]
  rw [sum_comm]
  simp_rw [sum_mul]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro x _
  have hx : (subset x).card = r (state x) := x.property
  simp only [← mul_sum]
  have h : (∑ i : I, if i ∈ subset x then (1 : ℝ) else 0) = (subset x).card := by simp
  rw [h, hx]
  simp

omit [DecidableEq I] in
lemma feasible_mass {r : S → ℕ} {p₀ p : Outcome (I := I) r → ℝ}
    (hp : Feasible p₀ p) : (∑ x, p x) = ∑ x, p₀ x := by
  rw [← mass_total p, ← mass_total p₀]
  exact sum_congr rfl fun ω _ => hp.2 ω

lemma move_feasible {r : S → ℕ} {p₀ p : Outcome (I := I) r → ℝ} (hp : Feasible p₀ p)
    {x y : Outcome (I := I) r} (hxy : state x = state y)
    {ε : ℝ} (hε : 0 ≤ ε) (hx : ε ≤ p x) : Feasible p₀ (move p x y ε) := by
  refine ⟨move_nonneg hp.1 hε hx, ?_⟩
  intro ω
  rw [Mass, move_sum, hxy]
  simpa [Mass] using hp.2 ω

omit [DecidableEq I] in
lemma continuous_mass {r : S → ℕ} (ω : S) : Continuous (fun p : Outcome (I := I) r → ℝ => Mass p ω) := by
  unfold Mass
  fun_prop

omit [DecidableEq S] in
lemma continuous_marginal {r : S → ℕ} (i : I) : Continuous (fun p : Outcome (I := I) r → ℝ => Marginal p i) := by
  unfold Marginal
  fun_prop

omit [DecidableEq I] in
lemma feasible_compact {r : S → ℕ} (p₀ : Outcome (I := I) r → ℝ)
    (h₀ : ∑ x, p₀ x = 1) : IsCompact {p | Feasible p₀ p} := by
  have hc : IsClosed {p | Feasible p₀ p} := by
    change IsClosed ({p : Outcome (I := I) r → ℝ | ∀ x, 0 ≤ p x} ∩
      {p | ∀ ω, Mass p ω = Mass p₀ ω})
    apply IsClosed.inter
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun ω => isClosed_eq (continuous_mass ω) continuous_const
  apply (isCompact_pi_infinite fun _ : Outcome (I := I) r =>
    isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset hc
  intro p hp x
  refine ⟨hp.1 x, ?_⟩
  have he : ∑ z, p z = 1 := (feasible_mass hp).trans h₀
  rw [← he]
  exact single_le_sum (fun z _ => hp.1 z) (mem_univ x)

def Objective {r : S → ℕ} (c : Outcome (I := I) r → ℝ) (f : I → ℝ)
    (p : Outcome (I := I) r → ℝ) : ℝ :=
  (∑ x, p x * c x) + 10 * ∑ i, |Marginal p i - f i|

omit [DecidableEq S] in
lemma objective_continuous {r : S → ℕ} (c : Outcome (I := I) r → ℝ) (f : I → ℝ) :
    Continuous (Objective c f) := by
  apply Continuous.add
  · fun_prop
  · apply Continuous.const_mul
    apply continuous_finsetSum
    intro i _
    exact ((continuous_marginal i).sub continuous_const).abs

lemma exists_minimizer {r : S → ℕ} (p₀ c : Outcome (I := I) r → ℝ) (f : I → ℝ)
    (hp₀ : ∀ x, 0 ≤ p₀ x) (h₀ : ∑ x, p₀ x = 1) :
    ∃ p, Feasible p₀ p ∧ IsMinOn (Objective c f) {p | Feasible p₀ p} p := by
  exact (feasible_compact p₀ h₀).exists_isMinOn ⟨p₀, hp₀, fun _ => rfl⟩
    (objective_continuous c f).continuousOn

def exchange (A : Finset I) (i j : I) : Finset I := insert j (A.erase i)

omit [Fintype I] in
lemma exchange_card {A : Finset I} {i j : I} (hi : i ∈ A) (hj : j ∉ A) :
    (exchange A i j).card = A.card := by
  rw [exchange, card_insert_of_notMem (fun h => hj (mem_of_mem_erase h)), card_erase_of_mem hi]
  have := card_pos.mpr ⟨i, hi⟩
  omega

omit [Fintype I] in
lemma exchange_indicator {A : Finset I} {i j : I} (hi : i ∈ A) (hj : j ∉ A) (a : I) :
    (if a ∈ exchange A i j then (1 : ℝ) else 0) = (if a ∈ A then 1 else 0) +
       (if a = j then 1 else 0) - (if a = i then 1 else 0) := by
  have hij : i ≠ j := by intro h; subst j; contradiction
  by_cases ha : a = i
  · subst a; simp [exchange, hij, hi]
  · by_cases hb : a = j
    · subst a; simp [exchange, Ne.symm hij, hj]
    · simp [exchange, ha, hb]

def afterExchange {r : S → ℕ} (x : Outcome (I := I) r) (i j : I)
    (hi : i ∈ subset x) (hj : j ∉ subset x) : Outcome (I := I) r :=
  ⟨(state x, exchange (subset x) i j), (exchange_card hi hj).trans x.property⟩

omit [Fintype I] [Fintype S] [DecidableEq S] in
lemma exchange_state {r : S → ℕ} (x : Outcome (I := I) r) (i j : I)
    (hi : i ∈ subset x) (hj : j ∉ subset x) :
    state (afterExchange x i j hi hj) = state x := rfl

lemma move_exchange_marginal {r : S → ℕ} (p : Outcome (I := I) r → ℝ)
    (x : Outcome (I := I) r) (i j : I) (hi : i ∈ subset x) (hj : j ∉ subset x)
    (ε : ℝ) (a : I) :
    Marginal (move p x (afterExchange x i j hi hj) ε) a = Marginal p a +
      ε * ((if a = j then 1 else 0) - (if a = i then 1 else 0)) := by
  rw [Marginal, move_sum]
  change _ + ε * ((if a ∈ exchange (subset x) i j then 1 else 0) - _) = _
  rw [exchange_indicator hi hj]
  unfold Marginal
  ring

lemma deviation_descent (a f : I → ℝ) {i j : I} (hij : i ≠ j) {ε : ℝ}
    (hε : 0 ≤ ε) (hi : ε ≤ a i - f i) (hj : ε ≤ f j - a j) :
    (∑ x, |a x + ε * ((if x = j then 1 else 0) - (if x = i then 1 else 0)) - f x|) =
    (∑ x, |a x - f x|) - 2 * ε := by
  have he (x : I) :
      |a x + ε * ((if x = j then 1 else 0) - (if x = i then 1 else 0)) - f x| =
      |a x - f x| - (if x = i then ε else 0) - (if x = j then ε else 0) := by
    by_cases hx : x = i
    · subst x
      simp only [ite_eq_right hij, ite_true]
      rw [abs_of_nonneg (by linarith : 0 ≤ a i + ε * (0 - 1) - f i),
        abs_of_nonneg (by linarith : 0 ≤ a i - f i)]
      ring
    · by_cases hy : x = j
      · subst x
        simp only [ite_true, ite_eq_right (Ne.symm hij)]
        rw [abs_of_nonpos (by linarith : a j + ε * (1 - 0) - f j ≤ 0),
          abs_of_nonpos (by linarith : a j - f j ≤ 0)]
        ring
      · simp [hx, hy]
  simp_rw [he]
  rw [sum_sub_distrib, sum_sub_distrib]
  simp
  ring

omit [DecidableEq I] in
lemma discrepancy_pair (a f : I → ℝ) (hs : ∑ i, a i = ∑ i, f i)
    (hne : ¬∀ i, a i = f i) : ∃ i j, a i > f i ∧ a j < f j := by
  have hi : ∃ i, f i < a i := by
    by_contra! h
    apply hne
    intro i
    exact (sum_eq_sum_iff_of_le (fun i _ => h i)).mp hs i (mem_univ _)
  have hj : ∃ j, a j < f j := by
    by_contra! h
    apply hne
    have he := (sum_eq_sum_iff_of_le (fun i _ => h i)).mp hs.symm
    intro i
    exact (he i (mem_univ i)).symm
  obtain ⟨i, hi⟩ := hi
  obtain ⟨j, hj⟩ := hj
  exact ⟨i, j, hi, hj⟩

omit [DecidableEq S] in
lemma support_mem {r : S → ℕ} {p : Outcome (I := I) r → ℝ} (hp : ∀x, 0 ≤ p x)
    {i : I} (hi : 0 < Marginal p i) : ∃ x, 0 < p x ∧ i ∈ subset x := by
  by_contra! h
  have he : Marginal p i = 0 := by
    apply sum_eq_zero
    intro x _
    by_cases hh : 0 < p x
    · simp [h x hh]
    · have hz := le_antisymm (le_of_not_gt hh) (hp x)
      simp [hz]
  linarith

omit [DecidableEq S] in
lemma support_notMem {r : S → ℕ} {p : Outcome (I := I) r → ℝ} (hp : ∀x, 0 ≤ p x)
    (h₁ : ∑ x, p x = 1) {i : I} (hi : Marginal p i < 1) :
    ∃ x, 0 < p x ∧ i ∉ subset x := by
  by_contra! h
  have he : Marginal p i = ∑ x, p x := by
    apply sum_congr rfl
    intro x _
    by_cases hh : 0 < p x
    · simp [h x hh]
    · have hz := le_antisymm (le_of_not_gt hh) (hp x)
      simp [hz]
  linarith

omit [Fintype I] in
lemma exists_bridge {A B : Finset I} {i j : I} (hij : i ≠ j)
    (hiA : i ∈ A) (hjA : j ∈ A) (hiB : i ∉ B) (hjB : j ∉ B)
    (hc : A.card ≤ B.card + 1) : ∃ h, h ∈ B ∧ h ∉ A := by
  by_contra! hh
  have hBA : B ⊆ A := hh
  have hsub : insert i (insert j B) ⊆ A := by
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact hiA
    rcases mem_insert.mp ha with rfl | ha
    · exact hjA
    exact hBA ha
  have hcard := card_le_card hsub
  have hn : i ∉ insert j B := by simp [hij, hiB]
  rw [card_insert_of_notMem hn, card_insert_of_notMem hjB] at hcard
  omega

/-- The local Lipschitz property needed by the repair objective. It will be
instantiated by Hamming distance from the state's preliminary rounding. -/
def ExchangeCost {r : S → ℕ} (c : Outcome (I := I) r → ℝ) : Prop :=
  ∀ (x : Outcome (I := I) r) (i j : I) (hi : i ∈ subset x) (hj : j ∉ subset x),
    c (afterExchange x i j hi hj) - c x ≤ 2

lemma one_exchange_improves {r : S → ℕ} {p₀ p c : Outcome (I := I) r → ℝ} {f : I → ℝ}
    (hp : Feasible p₀ p) (hc : ExchangeCost c)
    {i j : I} (hi : f i < Marginal p i) (hj : Marginal p j < f j)
    (x : Outcome (I := I) r) (hx : 0 < p x) (hxi : i ∈ subset x) (hxj : j ∉ subset x) :
    ∃ q, Feasible p₀ q ∧ Objective c f q < Objective c f p := by
  have hij : i ≠ j := by intro he; subst j; linarith
  let ε := min (p x) (min (Marginal p i - f i) (f j - Marginal p j))
  have hε : 0 < ε := lt_min hx (lt_min (sub_pos.mpr hi) (sub_pos.mpr hj))
  have hεx : ε ≤ p x := min_le_left _ _
  have hεi : ε ≤ Marginal p i - f i := (min_le_right _ _).trans (min_le_left _ _)
  have hεj : ε ≤ f j - Marginal p j := (min_le_right _ _).trans (min_le_right _ _)
  let y := afterExchange x i j hxi hxj
  let q := move p x y ε
  refine ⟨q, move_feasible (x := x) (y := y) hp rfl hε.le hεx, ?_⟩
  have hd : (∑ a, |Marginal q a - f a|) = (∑ a, |Marginal p a - f a|) - 2 * ε := by
    simp only [q, y, move_exchange_marginal]
    exact deviation_descent _ _ hij hε.le hεi hεj
  have hcost : (∑ z, q z * c z) ≤ (∑ z, p z * c z) + 2 * ε := by
    dsimp only [q]
    rw [move_sum]
    have hh := mul_le_mul_of_nonneg_left (hc x i j hxi hxj) hε.le
    dsimp [y]
    linarith
  unfold Objective
  rw [hd]
  linarith

lemma two_exchanges_improve {r : S → ℕ} {p₀ p c : Outcome (I := I) r → ℝ} {f : I → ℝ}
    (hp : Feasible p₀ p) (hc : ExchangeCost c)
    {i j : I} (hi : f i < Marginal p i) (hj : Marginal p j < f j)
    (x y : Outcome (I := I) r) (hx : 0 < p x) (hy : 0 < p y)
    (hxi : i ∈ subset x) (hxj : j ∈ subset x)
    (hyi : i ∉ subset y) (hyj : j ∉ subset y)
    (h : I) (hyh : h ∈ subset y) (hxh : h ∉ subset x) :
    ∃ q, Feasible p₀ q ∧ Objective c f q < Objective c f p := by
  have hij : i ≠ j := by intro he; subst j; linarith
  have hyx : y ≠ x := by intro he; subst y; contradiction
  let ε := min (min (p x) (p y)) (min (Marginal p i - f i) (f j - Marginal p j))
  have hε : 0 < ε := lt_min (lt_min hx hy) (lt_min (sub_pos.mpr hi) (sub_pos.mpr hj))
  have hεx : ε ≤ p x := (min_le_left _ _).trans (min_le_left _ _)
  have hεy : ε ≤ p y := (min_le_left _ _).trans (min_le_right _ _)
  have hεi : ε ≤ Marginal p i - f i := (min_le_right _ _).trans (min_le_left _ _)
  have hεj : ε ≤ f j - Marginal p j := (min_le_right _ _).trans (min_le_right _ _)
  let x' := afterExchange x i h hxi hxh
  let y' := afterExchange y h j hyh hyj
  let mid := move p x x' ε
  let q := move mid y y' ε
  have hmid : Feasible p₀ mid := move_feasible (x := x) (y := x') hp rfl hε.le hεx
  have hq : Feasible p₀ q := move_feasible (x := y) (y := y') hmid rfl hε.le
    (hεy.trans (move_coordinate p hε.le hyx))
  refine ⟨q, hq, ?_⟩
  have hm (a : I) : Marginal q a = Marginal p a +
      ε * ((if a = j then 1 else 0) - (if a = i then 1 else 0)) := by
    dsimp only [q, mid, x', y']
    rw [move_exchange_marginal, move_exchange_marginal]
    ring
  have hd : (∑ a, |Marginal q a - f a|) = (∑ a, |Marginal p a - f a|) - 2 * ε := by
    simp only [hm]
    exact deviation_descent _ _ hij hε.le hεi hεj
  have hcost : (∑ z, q z * c z) ≤ (∑ z, p z * c z) + 4 * ε := by
    dsimp only [q, mid]
    rw [move_sum, move_sum]
    have hhx := mul_le_mul_of_nonneg_left (hc x i h hxi hxh) hε.le
    have hhy := mul_le_mul_of_nonneg_left (hc y h j hyh hyj) hε.le
    dsimp only [x', y']
    linarith
  unfold Objective
  rw [hd]
  linarith

/-- A minimizer has the prescribed unconditional marginals, even when different
fibers have different adjacent totals. This is the source's essential
correlation-tolerant two-state exchange argument. -/
lemma minimizer_marginals {r : S → ℕ} {p₀ p c : Outcome (I := I) r → ℝ} {f : I → ℝ}
    (hr : ∀ ω ν, r ω ≤ r ν + 1) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hfSum : ∑ i, f i = ∑ ω, Mass p₀ ω * r ω)
    (hp : Feasible p₀ p) (h₀ : ∑ x, p₀ x = 1) (hc : ExchangeCost c)
    (hmin : IsMinOn (Objective c f) {p | Feasible p₀ p} p) :
    ∀ i, Marginal p i = f i := by
  by_contra hne
  have hsum : ∑ i, Marginal p i = ∑ i, f i := by
    rw [marginal_total, hfSum]
    exact sum_congr rfl fun ω _ => by rw [hp.2 ω]
  obtain ⟨i, j, hi, hj⟩ := discrepancy_pair (Marginal p) f hsum hne
  have hij : i ≠ j := by intro he; subst j; linarith
  by_cases hex : ∃ x, 0 < p x ∧ i ∈ subset x ∧ j ∉ subset x
  · obtain ⟨x, hx, hxi, hxj⟩ := hex
    obtain ⟨q, hq, hqCost⟩ := one_exchange_improves hp hc hi hj x hx hxi hxj
    exact (not_lt_of_ge (hmin hq)) hqCost
  · obtain ⟨x, hx, hxi⟩ := support_mem hp.1 ((hf i).1.trans_lt hi)
    have hxj : j ∈ subset x := by
      by_contra hh
      exact hex ⟨x, hx, hxi, hh⟩
    obtain ⟨y, hy, hyj⟩ := support_notMem hp.1 ((feasible_mass hp).trans h₀) (hj.trans_le (hf j).2)
    have hyi : i ∉ subset y := fun hh => hex ⟨y, hy, hh, hyj⟩
    have hcard : (subset x).card ≤ (subset y).card + 1 := by
      rw [show (subset x).card = r (state x) from x.property,
          show (subset y).card = r (state y) from y.property]
      exact hr _ _
    obtain ⟨h, hyh, hxh⟩ := exists_bridge hij hxi hxj hyi hyj hcard
    obtain ⟨q, hq, hqCost⟩ := two_exchanges_improve hp hc hi hj x y hx hy hxi hxj hyi hyj h hyh hxh
    exact (not_lt_of_ge (hmin hq)) hqCost

/-- The compact finite-law repair step, including its quantitative cost bound. -/
theorem finite_repair {r : S → ℕ} (p₀ c : Outcome (I := I) r → ℝ) (f : I → ℝ)
    (hr : ∀ ω ν, r ω ≤ r ν + 1) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hfSum : ∑ i, f i = ∑ ω, Mass p₀ ω * r ω)
    (hp₀ : ∀ x, 0 ≤ p₀ x) (h₀ : ∑ x, p₀ x = 1) (hc : ExchangeCost c) :
    ∃ p, Feasible p₀ p ∧ (∀ i, Marginal p i = f i) ∧
      (∑ x, p x * c x) ≤ (∑ x, p₀ x * c x) + 10 * ∑ i, |Marginal p₀ i - f i| := by
  obtain ⟨p, hp, hm⟩ := exists_minimizer p₀ c f hp₀ h₀
  have hmar := minimizer_marginals hr hf hfSum hp h₀ hc hm
  refine ⟨p, hp, hmar, ?_⟩
  have hh := hm (show Feasible p₀ p₀ from ⟨hp₀, fun _ => rfl⟩)
  simpa [Objective, hmar] using hh

def hamming (A B : Finset I) : ℝ :=
  ∑ i, |(if i ∈ A then (1 : ℝ) else 0) - (if i ∈ B then 1 else 0)|

lemma hamming_self (A : Finset I) : hamming A A = 0 := by simp [hamming]

lemma hamming_triangle (A B C : Finset I) : hamming A C ≤ hamming A B + hamming B C := by
  rw [hamming, hamming, hamming, ← sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le _ _ _

lemma hamming_exchange {A : Finset I} {i j : I} (hi : i ∈ A) (hj : j ∉ A) :
    hamming (exchange A i j) A = 2 := by
  have hij : i ≠ j := by intro he; subst j; contradiction
  have he (a : I) :
      |(if a ∈ exchange A i j then (1 : ℝ) else 0) - (if a ∈ A then 1 else 0)| =
      (if a = j then 1 else 0) + (if a = i then 1 else 0) := by
    rw [exchange_indicator hi hj]
    by_cases ha : a = i
    · subst a; simp [hij]
    · by_cases hb : a = j
      · subst a; simp [Ne.symm hij]
      · simp [ha, hb]
  simp only [hamming, he, sum_add_distrib]
  norm_num

def HammingCost {r : S → ℕ} (A₀ : S → Finset I) (x : Outcome (I := I) r) : ℝ :=
  hamming (subset x) (A₀ (state x))

omit [Fintype S] [DecidableEq S] in
lemma hamming_exchangeCost {r : S → ℕ} (A₀ : S → Finset I) :
    ExchangeCost (HammingCost (r := r) A₀) := by
  intro x i j hi hj
  have hh := hamming_triangle (exchange (subset x) i j) (subset x) (A₀ (state x))
  rw [hamming_exchange hi hj] at hh
  change hamming (exchange (subset x) i j) (A₀ (state x)) - _ ≤ 2
  unfold HammingCost
  linarith

def seed {r : S → ℕ} (w : S → ℝ) (e : S → Outcome (I := I) r) : Outcome (I := I) r → ℝ :=
  fun x => ∑ ω, if x = e ω then w ω else 0

omit [Fintype I] in
lemma seed_nonneg {r : S → ℕ} {w : S → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (e : S → Outcome (I := I) r) : ∀ x, 0 ≤ seed w e x := by
  intro x
  exact sum_nonneg fun ω _ => by split_ifs; exact hw ω; rfl

lemma seed_sum {r : S → ℕ} (w : S → ℝ) (e : S → Outcome (I := I) r)
    (g : Outcome (I := I) r → ℝ) :
    (∑ x, seed w e x * g x) = ∑ ω, w ω * g (e ω) := by
  simp only [seed, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  simp [ite_mul]

lemma seed_total {r : S → ℕ} (w : S → ℝ) (e : S → Outcome (I := I) r) :
    (∑ x, seed w e x) = ∑ ω, w ω := by
  simpa using seed_sum w e (fun _ => 1)

lemma seed_mass {r : S → ℕ} (w : S → ℝ) (e : S → Outcome (I := I) r)
    (he : ∀ ω, state (e ω) = ω) (ω : S) : Mass (seed w e) ω = w ω := by
  rw [Mass, seed_sum]
  simp [he]

lemma seed_marginal {r : S → ℕ} (w : S → ℝ) (e : S → Outcome (I := I) r) (i : I) :
    Marginal (seed w e) i = ∑ ω, w ω * (if i ∈ subset (e ω) then 1 else 0) := by
  exact seed_sum _ _ _

/-- Joint-law repair in the exact Hamming metric of the manuscript. All
correlation is retained by preserving every original state probability. -/
theorem hamming_repair (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) (h₁ : ∑ ω, w ω = 1)
    (r : S → ℕ) (hr : ∀ ω ν, r ω ≤ r ν + 1) (A₀ : S → Finset I)
    (hA : ∀ ω, (A₀ ω).card = r ω) (f : I → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hs : ∑ i, f i = ∑ ω, w ω * r ω) :
    ∃ p : Outcome (I := I) r → ℝ, (∀ x, 0 ≤ p x) ∧ (∀ ω, Mass p ω = w ω) ∧
      (∀ i, Marginal p i = f i) ∧
      (∑ x, p x * HammingCost A₀ x) ≤
        10 * ∑ i, |(∑ ω, w ω * (if i ∈ A₀ ω then 1 else 0)) - f i| := by
  let e : S → Outcome (I := I) r := fun ω => ⟨(ω, A₀ ω), hA ω⟩
  have he (ω : S) : state (e ω) = ω := rfl
  have hsubset (ω : S) : subset (e ω) = A₀ ω := rfl
  have hmass := seed_mass w e he
  have hfs : ∑ i, f i = ∑ ω, Mass (seed w e) ω * r ω := by simpa [hmass] using hs
  obtain ⟨p, hp, hmar, hcost⟩ := finite_repair (seed w e) (HammingCost A₀) f hr hf hfs
    (seed_nonneg hw e) ((seed_total w e).trans h₁) (hamming_exchangeCost A₀)
  refine ⟨p, hp.1, fun ω => (hp.2 ω).trans (hmass ω), hmar, ?_⟩
  have hzero : (∑ x, seed w e x * HammingCost A₀ x) = 0 := by
    rw [seed_sum]
    simp [HammingCost, he, hsubset, hamming_self]
  simpa [hzero, seed_marginal, hsubset] using hcost

lemma hamming_comm (A B : Finset I) : hamming A B = hamming B A := by
  apply sum_congr rfl
  intro i _
  exact abs_sub_comm _ _

lemma hamming_subset {A B : Finset I} (h : B ⊆ A) :
    hamming A B = (A.card : ℝ) - B.card := by
  have hn (i : I) : (0 : ℝ) ≤ (if i ∈ A then 1 else 0) - (if i ∈ B then 1 else 0) := by
    by_cases hi : i ∈ B
    · simp [hi, h hi]
    · simp [hi]; split_ifs <;> norm_num
  simp only [hamming, abs_of_nonneg (hn _)]
  rw [sum_sub_distrib]
  simp

/-- Deterministic adjustment to any attainable integer total, with optimal
Hamming cost. The permitted coordinates H may omit all integral targets. -/
lemma adjust_subset (H A : Finset I) (hAH : A ⊆ H) {r : ℕ} (hr : r ≤ H.card) :
    ∃ B : Finset I, B ⊆ H ∧ B.card = r ∧ hamming B A = |(r : ℝ) - A.card| := by
  by_cases hsmall : r ≤ A.card
  · obtain ⟨B, hBA, hBr⟩ := exists_subset_card_eq hsmall
    refine ⟨B, hBA.trans hAH, hBr, ?_⟩
    rw [hamming_comm, hamming_subset hBA, hBr, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hsmall : (r : ℝ) ≤ A.card))]
    ring
  · have hbig : A.card ≤ r := le_of_not_ge hsmall
    have hc : r - A.card ≤ (H \ A).card := by
      rw [card_sdiff, inter_eq_left.mpr hAH]
      omega
    obtain ⟨C, hCH, hCr⟩ := exists_subset_card_eq hc
    have hdis : Disjoint A C := by
      apply disjoint_left.mpr
      intro a ha hca
      exact (mem_sdiff.mp (hCH hca)).2 ha
    let B := A ∪ C
    have hAB : A ⊆ B := subset_union_left
    have hBH : B ⊆ H := union_subset hAH (hCH.trans sdiff_subset)
    have hBr : B.card = r := by
      dsimp [B]
      rw [card_union_of_disjoint hdis, hCr]
      omega
    refine ⟨B, hBH, hBr, ?_⟩
    rw [hamming_subset hAB, hBr, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hbig : (A.card : ℝ) ≤ r))]

/-- The literal scalar interval used by the source's preliminary clipping. -/
def clip (b : ℝ) (x : ℤ) : ℤ := max ⌊b⌋ (min ⌈b⌉ x)

def Balanced (b : ℝ) (x : ℤ) : Prop := x = ⌊b⌋ ∨ x = ⌈b⌉

lemma balanced_iff_bounds (b : ℝ) (x : ℤ) :
    Balanced b x ↔ ⌊b⌋ ≤ x ∧ x ≤ ⌈b⌉ := by
  have hl := Int.floor_le_ceil b
  have hu := Int.ceil_le_floor_add_one b
  unfold Balanced
  omega

lemma clip_balanced (b : ℝ) (x : ℤ) : Balanced b (clip b x) := by
  rw [balanced_iff_bounds]
  exact ⟨le_max_left _ _, max_le (Int.floor_le_ceil b) (min_le_left _ _)⟩

lemma balanced_bounds {b : ℝ} {x : ℤ} (h : Balanced b x) :
    ⌊b⌋ ≤ x ∧ x ≤ ⌈b⌉ := (balanced_iff_bounds b x).mp h

lemma clip_up {a b : ℝ} (hab : a ≤ b) {x : ℤ} (hx : Balanced a x) :
    clip b x = max ⌊b⌋ x := by
  unfold clip
  rw [min_eq_right ((balanced_bounds hx).2.trans (Int.ceil_mono hab))]

lemma clip_down {a b : ℝ} (hab : b ≤ a) {x : ℤ} (hx : Balanced a x) :
    clip b x = min ⌈b⌉ x := by
  unfold clip
  rw [max_eq_right (le_min (Int.floor_le_ceil b) ((Int.floor_mono hab).trans (balanced_bounds hx).1))]

omit [DecidableEq S] in
/-- Exact source clipping estimate, with arbitrary finite weights and no
independence assumptions. -/
lemma clipping_bound (w : S → ℝ) (_hw : ∀ ω, 0 ≤ w ω) (h₁ : ∑ ω, w ω = 1)
    {a b : ℝ} (X : S → ℤ) (hX : ∀ ω, Balanced a (X ω))
    (hmean : ∑ ω, w ω * (X ω : ℝ) = a) :
    (∑ ω, w ω * |(clip b (X ω) : ℝ) - X ω|) ≤ |a - b| := by
  rcases le_total a b with hab | hba
  · simp_rw [clip_up hab (hX _)]
    by_cases hf : ⌊b⌋ ≤ ⌊a⌋
    · have hh (ω : S) : max ⌊b⌋ (X ω) = X ω := max_eq_right (hf.trans (balanced_bounds (hX ω)).1)
      simp [hh]
    · have hl : ⌈a⌉ ≤ ⌊b⌋ := by have := Int.ceil_le_floor_add_one a; omega
      have hh (ω : S) : max ⌊b⌋ (X ω) = ⌊b⌋ := max_eq_left ((balanced_bounds (hX ω)).2.trans hl)
      have hn (ω : S) : (0 : ℝ) ≤ (⌊b⌋ : ℝ) - X ω := by
        exact_mod_cast sub_nonneg.mpr ((balanced_bounds (hX ω)).2.trans hl)
      simp_rw [hh, abs_of_nonneg (hn _), mul_sub]
      rw [sum_sub_distrib, ← sum_mul, h₁, one_mul, hmean, abs_of_nonpos (sub_nonpos.mpr hab)]
      linarith [Int.floor_le b]
  · simp_rw [clip_down hba (hX _)]
    by_cases hc : ⌈a⌉ ≤ ⌈b⌉
    · have hh (ω : S) : min ⌈b⌉ (X ω) = X ω := min_eq_right ((balanced_bounds (hX ω)).2.trans hc)
      simp [hh]
    · have hu : ⌈b⌉ ≤ ⌊a⌋ := by have := Int.ceil_le_floor_add_one a; omega
      have hh (ω : S) : min ⌈b⌉ (X ω) = ⌈b⌉ := min_eq_left (hu.trans (balanced_bounds (hX ω)).1)
      have hn (ω : S) : (⌈b⌉ : ℝ) - X ω ≤ 0 := by
        exact_mod_cast sub_nonpos.mpr (hu.trans (balanced_bounds (hX ω)).1)
      simp_rw [hh, abs_of_nonpos (hn _), mul_neg, mul_sub]
      rw [sum_neg_distrib, sum_sub_distrib, ← sum_mul, h₁, one_mul, hmean, abs_of_nonneg (sub_nonneg.mpr hba)]
      linarith [Int.le_ceil b]

def fraction (b : ℝ) : ℝ := b - ⌊b⌋

def fractionalSet (b : I → ℝ) : Finset I := univ.filter fun i => ⌊b i⌋ < ⌈b i⌉

def liftSet (b : I → ℝ) (A : Finset I) (i : I) : ℤ :=
  ⌊b i⌋ + if i ∈ A then 1 else 0

lemma fraction_range (b : ℝ) : 0 ≤ fraction b ∧ fraction b < 1 := by
  unfold fraction
  constructor <;> linarith [Int.floor_le b, Int.lt_floor_add_one b]

lemma ceil_formula (b : ℝ) : ⌈b⌉ = ⌊b⌋ + if ⌊b⌋ < ⌈b⌉ then 1 else 0 := by
  have := Int.ceil_le_floor_add_one b
  have := Int.floor_le_ceil b
  split_ifs <;> omega

lemma not_fractional {b : ℝ} (h : ¬⌊b⌋ < ⌈b⌉) : (⌊b⌋ : ℝ) = b := by
  have he : ⌊b⌋ = ⌈b⌉ := by have := Int.floor_le_ceil b; omega
  apply le_antisymm (Int.floor_le b)
  rw [he]
  exact Int.le_ceil b

lemma fraction_zero_iff (b : ℝ) : fraction b = 0 ↔ ¬⌊b⌋ < ⌈b⌉ := by
  constructor
  · intro h
    have he : b = (⌊b⌋ : ℝ) := by unfold fraction at h; linarith
    have hc := Int.ceil_le.mpr he.le
    omega
  · intro h
    simp [fraction, not_fractional h]

lemma liftSet_sum (b : I → ℝ) (A : Finset I) :
    (∑ i, liftSet b A i) = (∑ i, ⌊b i⌋) + A.card := by
  simp [liftSet, sum_add_distrib]

lemma liftSet_balanced (b : I → ℝ) {A : Finset I} (hA : A ⊆ fractionalSet b) (i : I) :
    Balanced (b i) (liftSet b A i) := by
  unfold liftSet
  by_cases hi : i ∈ A
  · simp only [ite_eq_left hi]
    right
    have hbi : ⌊b i⌋ < ⌈b i⌉ := (mem_filter.mp (hA hi)).2
    rw [ceil_formula, ite_eq_left hbi]
  · left
    simp [hi]

lemma balanced_liftSet (b : I → ℝ) (Y : I → ℤ) (hY : ∀ i, Balanced (b i) (Y i)) :
    ∃ A : Finset I, A ⊆ fractionalSet b ∧ ∀ i, Y i = liftSet b A i := by
  let A := univ.filter fun i => ⌊b i⌋ < Y i
  have hA : A ⊆ fractionalSet b := by
    intro i hi
    have hi' : ⌊b i⌋ < Y i := (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_univ _, hi'.trans_le (balanced_bounds (hY i)).2⟩
  refine ⟨A, hA, ?_⟩
  intro i
  have hu := Int.ceil_le_floor_add_one (b i)
  have := balanced_bounds (hY i)
  by_cases hi : i ∈ A
  · unfold liftSet
    rw [ite_eq_left hi]
    have hh : ⌊b i⌋ < Y i := (mem_filter.mp hi).2
    omega
  · unfold liftSet
    rw [ite_eq_right hi]
    have hh : ¬⌊b i⌋ < Y i := by simpa [A] using hi
    omega

lemma liftSet_distance (b : I → ℝ) (A B : Finset I) :
    (∑ i, |(liftSet b A i : ℝ) - liftSet b B i|) = hamming A B := by
  apply sum_congr rfl
  intro i _
  unfold liftSet
  push_cast
  congr 1
  ring

omit [DecidableEq I] in
lemma total_endpoints (b : I → ℝ) :
    (∑ i, ⌊b i⌋) ≤ ⌊∑ i, b i⌋ ∧ ⌈∑ i, b i⌉ ≤ (∑ i, ⌊b i⌋) + (fractionalSet b).card := by
  constructor
  · apply Int.le_floor.mpr
    push_cast
    exact sum_le_sum fun i _ => Int.floor_le _
  · apply Int.ceil_le.mpr
    have he : (∑ i, ⌈b i⌉) = (∑ i, ⌊b i⌋) + (fractionalSet b).card := by
      calc
        (∑ i, ⌈b i⌉) = ∑ i, (⌊b i⌋ + if ⌊b i⌋ < ⌈b i⌉ then (1 : ℤ) else 0) :=
          sum_congr rfl (fun i _ => ceil_formula (b i))
        _ = _ := ?_
      rw [sum_add_distrib]
      congr 1
      simp [fractionalSet]
    rw [← he]
    push_cast
    exact sum_le_sum fun i _ => Int.le_ceil _

def residual (b : I → ℝ) (N : ℤ) : ℕ := (N - ∑ i, ⌊b i⌋).toNat

omit [DecidableEq I] in
lemma residual_cast (b : I → ℝ) {N : ℤ} (hN : Balanced (∑ i, b i) N) :
    (residual b N : ℤ) = N - ∑ i, ⌊b i⌋ := by
  unfold residual
  apply Int.toNat_of_nonneg
  exact sub_nonneg.mpr ((total_endpoints b).1.trans (balanced_bounds hN).1)

omit [DecidableEq I] in
lemma residual_bound (b : I → ℝ) {N : ℤ} (hN : Balanced (∑ i, b i) N) :
    residual b N ≤ (fractionalSet b).card := by
  have hcast := residual_cast b hN
  have hu := (balanced_bounds hN).2.trans (total_endpoints b).2
  omega

omit [DecidableEq I] in
lemma residual_adjacent (b : I → ℝ) {N M : ℤ}
    (hN : Balanced (∑ i, b i) N) (hM : Balanced (∑ i, b i) M) :
    residual b N ≤ residual b M + 1 := by
  have hcastN := residual_cast b hN
  have hcastM := residual_cast b hM
  have hN' := balanced_bounds hN
  have hM' := balanced_bounds hM
  have := Int.ceil_le_floor_add_one (∑ i, b i)
  omega

omit [DecidableEq I] in
lemma residual_cast_real (b : I → ℝ) {N : ℤ} (hN : Balanced (∑ i, b i) N) :
    (residual b N : ℝ) = N - ∑ i, (⌊b i⌋ : ℝ) := by
  have he := congrArg (fun z : ℤ => (z : ℝ)) (residual_cast b hN)
  simpa using he

omit [DecidableEq I] [DecidableEq S] in
lemma residual_mean (w : S → ℝ) (h₁ : ∑ ω, w ω = 1) (b : I → ℝ) (N : S → ℤ)
    (hN : ∀ ω, Balanced (∑ i, b i) (N ω)) (hm : ∑ ω, w ω * (N ω : ℝ) = ∑ i, b i) :
    (∑ i, fraction (b i)) = ∑ ω, w ω * residual b (N ω) := by
  simp_rw [residual_cast_real b (hN _), mul_sub, fraction]
  rw [sum_sub_distrib, sum_sub_distrib, ← sum_mul, h₁, one_mul, hm]

/-- The statewise preliminary adjustment has exactly the source's cost. -/
lemma preliminary_state (b : I → ℝ) (X : I → ℤ) {N : ℤ}
    (hN : Balanced (∑ i, b i) N) :
    ∃ A : Finset I, A ⊆ fractionalSet b ∧ A.card = residual b N ∧
      (∑ i, |(liftSet b A i : ℝ) - clip (b i) (X i)|) =
        |(N : ℝ) - ∑ i, (clip (b i) (X i) : ℝ)| := by
  obtain ⟨Y, hY, he⟩ := balanced_liftSet b (fun i => clip (b i) (X i))
    (fun i => clip_balanced _ _)
  obtain ⟨A, hA, hcard, hcost⟩ := adjust_subset (fractionalSet b) Y hY (residual_bound b hN)
  refine ⟨A, hA, hcard, ?_⟩
  simp_rw [he]
  rw [liftSet_distance, hcost, residual_cast_real b hN]
  congr 1
  have hy := congrArg (fun z : ℤ => (z : ℝ)) (liftSet_sum b Y)
  push_cast at hy
  rw [hy]
  ring

def mean (w : S → ℝ) (X : S → ℝ) : ℝ := ∑ ω, w ω * X ω

def dist₁ (X Y : I → ℝ) : ℝ := ∑ i, |X i - Y i|

omit [DecidableEq I] in
lemma dist₁_triangle (X Y Z : I → ℝ) : dist₁ X Z ≤ dist₁ X Y + dist₁ Y Z := by
  unfold dist₁
  rw [← sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le _ _ _

omit [DecidableEq I] in
lemma abs_total_le (X Y : I → ℝ) : |(∑ i, X i) - ∑ i, Y i| ≤ dist₁ X Y := by
  rw [← sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

omit [DecidableEq S] in
lemma mean_mono (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) {X Y : S → ℝ}
    (h : ∀ ω, X ω ≤ Y ω) : mean w X ≤ mean w Y :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hw ω)

omit [DecidableEq S] in
lemma mean_add (w : S → ℝ) (X Y : S → ℝ) :
    mean w (fun ω => X ω + Y ω) = mean w X + mean w Y := by
  simp [mean, mul_add, sum_add_distrib]

omit [DecidableEq S] in
lemma mean_abs_sub (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) (X Y : S → ℝ) :
    |mean w X - mean w Y| ≤ mean w (fun ω => |X ω - Y ω|) := by
  calc
    |mean w X - mean w Y| = |∑ ω, w ω * (X ω - Y ω)| := by
      simp [mean, mul_sub, sum_sub_distrib]
    _ ≤ ∑ ω, |w ω * (X ω - Y ω)| := abs_sum_le_sum_abs _ _
    _ = _ := by simp [mean, abs_mul, abs_of_nonneg (hw _)]

omit [DecidableEq I] [DecidableEq S] in
lemma dist₁_mean (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) (X Y : S → I → ℝ) :
    dist₁ (fun i => mean w (fun ω => X ω i)) (fun i => mean w (fun ω => Y ω i)) ≤
      mean w (fun ω => dist₁ (X ω) (Y ω)) := by
  calc
    _ ≤ ∑ i, mean w (fun ω => |X ω i - Y ω i|) :=
      sum_le_sum fun i _ => mean_abs_sub w hw _ _
    _ = _ := by unfold mean dist₁; rw [sum_comm]; simp_rw [mul_sum]

omit [DecidableEq S] in
lemma preliminary_bounds (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) (h₁ : ∑ ω, w ω = 1)
    (a b : I → ℝ) (X : S → I → ℤ) (N : S → ℤ)
    (hX : ∀ ω i, Balanced (a i) (X ω i))
    (hm : ∀ i, mean w (fun ω => (X ω i : ℝ)) = a i)
    (A : S → Finset I)
    (hadj : ∀ ω, (∑ i, |(liftSet b (A ω) i : ℝ) - clip (b i) (X ω i)|) =
      |(N ω : ℝ) - ∑ i, (clip (b i) (X ω i) : ℝ)|) :
    let L := mean w (fun ω => dist₁ (fun i => (liftSet b (A ω) i : ℝ)) (fun i => (X ω i : ℝ)))
    let T := dist₁ a b
    let U := mean w (fun ω => |(N ω : ℝ) - ∑ i, (X ω i : ℝ)|)
    let D := dist₁ (fun i => mean w (fun ω => (liftSet b (A ω) i : ℝ))) b
    L ≤ 2*T + U ∧ D ≤ 3*T + U := by
  dsimp only
  let Y : S → I → ℝ := fun ω i => clip (b i) (X ω i)
  let Z : S → I → ℝ := fun ω i => liftSet b (A ω) i
  let V : S → I → ℝ := fun ω i => X ω i
  have hclip : mean w (fun ω => dist₁ (Y ω) (V ω)) ≤ dist₁ a b := by
    unfold mean dist₁
    simp_rw [mul_sum]
    rw [sum_comm]
    exact sum_le_sum fun i _ => clipping_bound w hw h₁ (fun ω => X ω i) (fun ω => hX ω i) (hm i)
  have hadjust : mean w (fun ω => dist₁ (Z ω) (Y ω)) ≤
      mean w (fun ω => |(N ω : ℝ) - ∑ i, (X ω i : ℝ)|) + mean w (fun ω => dist₁ (Y ω) (V ω)) := by
    rw [← mean_add]
    apply mean_mono w hw
    intro ω
    change (∑ i, |(liftSet b (A ω) i : ℝ) - clip (b i) (X ω i)|) ≤ _
    rw [hadj ω]
    have hsum : |(∑ i, (X ω i : ℝ)) - ∑ i, (clip (b i) (X ω i) : ℝ)| ≤ dist₁ (Y ω) (V ω) := by
      change |(∑ i, V ω i) - ∑ i, Y ω i| ≤ dist₁ (Y ω) (V ω)
      rw [abs_sub_comm (∑ i, V ω i) (∑ i, Y ω i)]
      exact abs_total_le (Y ω) (V ω)
    calc
      _ ≤ |(N ω : ℝ) - ∑ i, (X ω i : ℝ)| + |(∑ i, (X ω i : ℝ)) - ∑ i, (clip (b i) (X ω i) : ℝ)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add le_rfl hsum
  have hL : mean w (fun ω => dist₁ (Z ω) (V ω)) ≤ 2 * dist₁ a b +
      mean w (fun ω => |(N ω : ℝ) - ∑ i, (X ω i : ℝ)|) := by
    have htri := mean_mono w hw (fun ω => dist₁_triangle (Z ω) (Y ω) (V ω))
    rw [mean_add] at htri
    linarith
  refine ⟨hL, ?_⟩
  have htri := dist₁_triangle (fun i => mean w (fun ω => Z ω i)) a b
  have hmean := dist₁_mean w hw Z V
  have hmeans : (fun i => mean w (fun ω => V ω i)) = a := funext hm
  rw [hmeans] at hmean
  linarith
omit [DecidableEq I] in
lemma weighted_state {r : S → ℕ} (p : Outcome (I := I) r → ℝ) (f : S → ℝ) :
    (∑ x, p x * f (state x)) = ∑ ω, Mass p ω * f ω := by
  simp only [Mass, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [mul_assoc, ← mul_sum]
  simp

omit [Fintype I] [DecidableEq S] in
lemma liftSet_mean (w : S → ℝ) (h₁ : ∑ ω, w ω = 1) (b : I → ℝ)
    (A : S → Finset I) (i : I) :
    mean w (fun ω => (liftSet b (A ω) i : ℝ)) =
      (⌊b i⌋ : ℝ) + ∑ ω, w ω * (if i ∈ A ω then 1 else 0) := by
  unfold mean liftSet
  push_cast
  simp_rw [mul_add]
  rw [sum_add_distrib, ← sum_mul, h₁, one_mul]

omit [DecidableEq S] in
lemma marginal_support {r : S → ℕ} {p : Outcome (I := I) r → ℝ}
    (hp : ∀ x, 0 ≤ p x) (b : I → ℝ) (hm : ∀ i, Marginal p i = fraction (b i))
    {x : Outcome (I := I) r} (hx : 0 < p x) : subset x ⊆ fractionalSet b := by
  intro i hi
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  by_contra h
  have he : Marginal p i = 0 := (hm i).trans ((fraction_zero_iff _).mpr h)
  have hpos : p x ≤ Marginal p i := by
    calc
      p x = p x * (if i ∈ subset x then 1 else 0) := by simp [hi]
      _ ≤ _ := single_le_sum (f := fun y => p y * (if i ∈ subset y then 1 else 0))
        (fun y _ => mul_nonneg (hp y) (by split_ifs <;> norm_num)) (mem_univ x)
  linarith

/-- Full finite joint-law formulation of Section 09's star lemma. The first
coordinate retains the original state and hence all its correlations. A kernel
is obtained by finite disintegration below. Nonnegativity of a,b is needed only
to deduce nonnegative integer output, not for this stronger signed statement. -/
theorem rounding_star_joint (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) (h₁ : ∑ ω, w ω = 1)
    (a b : I → ℝ) (X : S → I → ℤ) (N : S → ℤ)
    (hX : ∀ ω i, Balanced (a i) (X ω i))
    (hmX : ∀ i, mean w (fun ω => (X ω i : ℝ)) = a i)
    (hN : ∀ ω, Balanced (∑ i, b i) (N ω))
    (hmN : mean w (fun ω => (N ω : ℝ)) = ∑ i, b i) :
    ∃ (p : Outcome (I := I) (fun ω => residual b (N ω)) → ℝ)
      (X' : Outcome (I := I) (fun ω => residual b (N ω)) → I → ℤ),
      (∀ x, 0 ≤ p x) ∧ (∀ ω, Mass p ω = w ω) ∧
      (∀ x i, Balanced (b i) (X' x i)) ∧
      (∀ x, (∑ i, X' x i) = N (state x)) ∧
      (∀ i, (∑ x, p x * (X' x i : ℝ)) = b i) ∧
      (∑ x, p x * dist₁ (fun i => (X' x i : ℝ)) (fun i => (X (state x) i : ℝ))) ≤
        32 * dist₁ a b + 11 * mean w (fun ω => |(N ω : ℝ) - ∑ i, (X ω i : ℝ)|) := by
  choose A hAH hAr hcost using fun ω => preliminary_state b (X ω) (hN ω)
  let r : S → ℕ := fun ω => residual b (N ω)
  have hr : ∀ ω ν, r ω ≤ r ν + 1 := fun ω ν => residual_adjacent b (hN ω) (hN ν)
  have hf (i : I) : 0 ≤ fraction (b i) ∧ fraction (b i) ≤ 1 :=
    ⟨(fraction_range _).1, (fraction_range _).2.le⟩
  obtain ⟨p, hp, hmass, hmar, hrepair⟩ := hamming_repair w hw h₁ r hr A hAr
    (fun i => fraction (b i)) hf (residual_mean w h₁ b N hN hmN)
  let A' : Outcome (I := I) r → Finset I :=
    fun x => if subset x ⊆ fractionalSet b then subset x else A (state x)
  have hA'H (x : Outcome (I := I) r) : A' x ⊆ fractionalSet b := by
    dsimp [A']; split_ifs with h
    · exact h
    · exact hAH _
  have hA'r (x : Outcome (I := I) r) : (A' x).card = r (state x) := by
    dsimp [A']; split_ifs
    · exact x.property
    · exact hAr _
  let X' : Outcome (I := I) r → I → ℤ := fun x => liftSet b (A' x)
  have hpos (x : Outcome (I := I) r) (hx : 0 < p x) : A' x = subset x :=
    ite_eq_left (marginal_support hp b hmar hx)
  have htotal : ∑ x, p x = 1 := by rw [← mass_total, show (fun ω => Mass p ω) = w from funext hmass]; exact h₁
  have hmean (i : I) : (∑ x, p x * (X' x i : ℝ)) = b i := by
    have he : (∑ x, p x * (X' x i : ℝ)) =
        mean p (fun x => (liftSet b (subset x) i : ℝ)) := by
      apply sum_congr rfl
      intro x _
      by_cases hx : 0 < p x
      · simp only [X', hpos x hx]
      · simp [le_antisymm (le_of_not_gt hx) (hp x)]
    rw [he, liftSet_mean p htotal b subset i]
    change (⌊b i⌋ : ℝ) + Marginal p i = b i
    rw [hmar]
    unfold fraction
    ring
  refine ⟨p, X', hp, hmass, fun x i => liftSet_balanced b (hA'H x) i, ?_, hmean, ?_⟩
  · intro x
    rw [show (∑ i, X' x i) = (∑ i, ⌊b i⌋) + (A' x).card from liftSet_sum b (A' x), hA'r]
    rw [show r (state x) = residual b (N (state x)) from rfl, residual_cast b (hN _)]
    ring
  · let L := mean w (fun ω => dist₁ (fun i => (liftSet b (A ω) i : ℝ)) (fun i => (X ω i : ℝ)))
    let D := dist₁ (fun i => mean w (fun ω => (liftSet b (A ω) i : ℝ))) b
    have hD : (∑ i, |(∑ ω, w ω * (if i ∈ A ω then 1 else 0)) - fraction (b i)|) = D := by
      apply sum_congr rfl
      intro i _
      dsimp only
      rw [liftSet_mean w h₁ b A i]
      unfold fraction
      congr 1
      ring
    rw [hD] at hrepair
    have hbound : (∑ x, p x * dist₁ (fun i => (X' x i : ℝ)) (fun i => (X (state x) i : ℝ))) ≤
        (∑ x, p x * HammingCost A x) + L := by
      calc
        _ ≤ ∑ x, p x * (HammingCost A x +
            dist₁ (fun i => (liftSet b (A (state x)) i : ℝ)) (fun i => (X (state x) i : ℝ))) := by
          apply sum_le_sum
          intro x _
          by_cases hx : 0 < p x
          · apply mul_le_mul_of_nonneg_left _ (hp x)
            have ht := dist₁_triangle (fun i => (X' x i : ℝ))
              (fun i => (liftSet b (A (state x)) i : ℝ)) (fun i => (X (state x) i : ℝ))
            simpa only [X', hpos x hx, dist₁, liftSet_distance, HammingCost] using ht
          · simp [le_antisymm (le_of_not_gt hx) (hp x)]
        _ = _ := by
          simp_rw [mul_add]
          rw [sum_add_distrib, weighted_state p (fun ω =>
            dist₁ (fun i => (liftSet b (A ω) i : ℝ)) (fun i => (X ω i : ℝ)))]
          simp only [hmass]
          rfl
    have hb := preliminary_bounds w hw h₁ a b X N hX hmX A hcost
    change L ≤ _ ∧ D ≤ _ at hb
    linarith
/-- Finite disintegration, including genuinely zero-probability input states. -/
def conditionalKernel (w : S → ℝ) (p : J → ℝ) (st : J → S) (e : S → J)
    (ω : S) (j : J) : ℝ :=
  if w ω = 0 then (if j = e ω then 1 else 0)
  else p j * (if st j = ω then 1 else 0) / w ω

omit [Fintype J] [Fintype S] in
lemma conditionalKernel_nonneg (w : S → ℝ) (p : J → ℝ) (st : J → S) (e : S → J)
    (hw : ∀ ω, 0 ≤ w ω) (hp : ∀ j, 0 ≤ p j) (ω : S) (j : J) :
    0 ≤ conditionalKernel w p st e ω j := by
  unfold conditionalKernel
  split_ifs
  · norm_num
  · norm_num
  · exact div_nonneg (mul_nonneg (hp j) zero_le_one) (hw ω)
  · simp

omit [Fintype S] in
lemma conditionalKernel_sum (w : S → ℝ) (p : J → ℝ) (st : J → S) (e : S → J)
    (hm : ∀ ω, (∑ j, p j * (if st j = ω then 1 else 0)) = w ω) (ω : S) :
    (∑ j, conditionalKernel w p st e ω j) = 1 := by
  by_cases hw : w ω = 0
  · simp [conditionalKernel, hw]
  · simp only [conditionalKernel, ite_eq_right hw, ← sum_div, hm ω, div_self hw]

omit [Fintype S] in
lemma conditionalKernel_identity (w : S → ℝ) (p : J → ℝ) (st : J → S) (e : S → J)
    (hp : ∀ j, 0 ≤ p j)
    (hm : ∀ ω, (∑ j, p j * (if st j = ω then 1 else 0)) = w ω) (ω : S) (j : J) :
    w ω * conditionalKernel w p st e ω j = p j * (if st j = ω then 1 else 0) := by
  by_cases hw : w ω = 0
  · have hsmall : p j * (if st j = ω then 1 else 0) ≤ 0 := by
      calc
        _ ≤ ∑ j, p j * (if st j = ω then 1 else 0) :=
          single_le_sum (fun j _ => mul_nonneg (hp j) (by split_ifs <;> norm_num)) (mem_univ j)
        _ = 0 := (hm ω).trans hw
    have hz : p j * (if st j = ω then 1 else 0) = 0 :=
      le_antisymm hsmall (mul_nonneg (hp j) (by split_ifs <;> norm_num))
    simp [hw, hz]
  · simp only [conditionalKernel, ite_eq_right hw]
    field_simp

lemma conditionalKernel_average (w : S → ℝ) (p : J → ℝ) (st : J → S) (e : S → J)
    (hp : ∀ j, 0 ≤ p j)
    (hm : ∀ ω, (∑ j, p j * (if st j = ω then 1 else 0)) = w ω) (F : S → J → ℝ) :
    (∑ ω, w ω * ∑ j, conditionalKernel w p st e ω j * F ω j) =
      ∑ j, p j * F (st j) j := by
  simp_rw [mul_sum, ← mul_assoc, conditionalKernel_identity w p st e hp hm]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp only [mul_assoc, ← mul_sum]
  simp [eq_comm]

/-- The source's exact finite randomized kernel, with the constants 32 and 11,
all correlations preserved, and valid outputs even at null input states. -/
theorem rounding_star (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) (h₁ : ∑ ω, w ω = 1)
    (a b : I → ℝ) (_ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (X : S → I → ℤ) (N : S → ℤ)
    (hX : ∀ ω i, Balanced (a i) (X ω i))
    (hmX : ∀ i, mean w (fun ω => (X ω i : ℝ)) = a i)
    (hN : ∀ ω, Balanced (∑ i, b i) (N ω))
    (hmN : mean w (fun ω => (N ω : ℝ)) = ∑ i, b i) :
    ∃ (κ : S → Outcome (I := I) (fun ω => residual b (N ω)) → ℝ)
      (X' : S → Outcome (I := I) (fun ω => residual b (N ω)) → I → ℤ),
      (∀ ω x, 0 ≤ κ ω x) ∧ (∀ ω, (∑ x, κ ω x) = 1) ∧
      (∀ ω x i, 0 ≤ X' ω x i ∧ Balanced (b i) (X' ω x i)) ∧
      (∀ ω x, (∑ i, X' ω x i) = N ω) ∧
      (∀ i, (∑ ω, w ω * ∑ x, κ ω x * (X' ω x i : ℝ)) = b i) ∧
      (∑ ω, w ω * ∑ x, κ ω x * dist₁ (fun i => (X' ω x i : ℝ)) (fun i => (X ω i : ℝ))) ≤
        32 * dist₁ a b + 11 * mean w (fun ω => |(N ω : ℝ) - ∑ i, (X ω i : ℝ)|) := by
  obtain ⟨p, Z, hp, hmass, hZ, htotal, hmean, hcost⟩ :=
    rounding_star_joint w hw h₁ a b X N hX hmX hN hmN
  choose A hAH hAr hAcost using fun ω => preliminary_state b (X ω) (hN ω)
  let r : S → ℕ := fun ω => residual b (N ω)
  let e : S → Outcome (I := I) r := fun ω => ⟨(ω, A ω), hAr ω⟩
  let κ := conditionalKernel w p state e
  let Z' : S → Outcome (I := I) r → I → ℤ :=
    fun ω x => if state x = ω then Z x else liftSet b (A ω)
  have hZ' (ω : S) (x : Outcome (I := I) r) (i : I) : Balanced (b i) (Z' ω x i) := by
    dsimp [Z']; split_ifs
    · exact hZ x i
    · exact liftSet_balanced b (hAH ω) i
  refine ⟨κ, Z', conditionalKernel_nonneg w p state e hw hp,
    conditionalKernel_sum w p state e hmass, ?_, ?_, ?_, ?_⟩
  · intro ω x i
    exact ⟨(Int.floor_nonneg.mpr (hb i)).trans (balanced_bounds (hZ' ω x i)).1, hZ' ω x i⟩
  · intro ω x
    dsimp [Z']
    split_ifs with hx
    · exact (htotal x).trans (congrArg N hx)
    · rw [liftSet_sum, hAr, residual_cast b (hN ω)]
      ring
  · intro i
    rw [conditionalKernel_average w p state e hp hmass]
    simp only [Z', ite_true]
    exact hmean i
  · rw [conditionalKernel_average w p state e hp hmass]
    simpa only [Z', ite_true] using hcost

end KServer.Rounding

/-! Continuation of Section09: finite top-down tree coupling.  The sampled
ancestors are retained as part of the joint state; no conditional means given
those ancestors are assumed. -/
namespace KServer.TreeRounding
open KServer.Rounding

structure Law (α : Type) where
  Ω : Type
  finite : Fintype Ω
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω=1
  point : Ω → α
attribute [instance] Law.finite

def Law.avg {α : Type} (L : Law α) (f : α → ℝ) : ℝ :=
  ∑ ω, L.weight ω*f (L.point ω)

lemma Law.avg_const {α : Type} (L : Law α) (c : ℝ) : L.avg (fun _ => c)=c := by
  simp [Law.avg, ← sum_mul, L.total]

lemma Law.avg_add {α : Type} (L : Law α) (f g : α → ℝ) :
    L.avg (fun x => f x+g x)=L.avg f+L.avg g := by
  simp [Law.avg, mul_add, sum_add_distrib]

lemma Law.avg_sub {α : Type} (L : Law α) (f g : α → ℝ) :
    L.avg (fun x => f x-g x)=L.avg f-L.avg g := by
  simp [Law.avg, mul_sub, sum_sub_distrib]

lemma Law.avg_sum {α I : Type} [Fintype I] (L : Law α) (f : I → α → ℝ) :
    L.avg (fun x => ∑ i, f i x)=∑ i, L.avg (f i) := by
  simp only [Law.avg, mul_sum]; rw [sum_comm]

lemma Law.avg_mono {α : Type} (L : Law α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    L.avg f ≤ L.avg g := sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h _) (L.nonneg ω)

lemma Law.avg_nonneg {α : Type} (L : Law α) {f : α → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ L.avg f := sum_nonneg fun ω _ => mul_nonneg (L.nonneg ω) (h _)

lemma Law.avg_congr {α : Type} (L : Law α) {f g : α → ℝ}
    (h : ∀ ω, f (L.point ω)=g (L.point ω)) : L.avg f=L.avg g :=
  sum_congr rfl fun ω _ => congrArg (L.weight ω * ·) (h ω)

/-- A finite extension with a normalized kernel retains the entire old state. -/
def Law.extend {α β J : Type} [Fintype J] (L : Law α) (κ : L.Ω → J → ℝ)
    (hκ : ∀ ω j, 0 ≤ κ ω j) (hκ1 : ∀ ω, ∑ j, κ ω j=1)
    (z : L.Ω → J → β) : Law (α × β) where
  Ω := L.Ω × J
  finite := inferInstance
  weight p := L.weight p.1*κ p.1 p.2
  nonneg p := mul_nonneg (L.nonneg p.1) (hκ p.1 p.2)
  total := by simp [Fintype.sum_prod_type, ← mul_sum, hκ1, L.total]
  point p := (L.point p.1, z p.1 p.2)

lemma Law.extend_avg {α β J : Type} [Fintype J] (L : Law α) (κ : L.Ω → J → ℝ)
    (hκ : ∀ ω j, 0 ≤ κ ω j) (hκ1 : ∀ ω, ∑ j, κ ω j=1)
    (z : L.Ω → J → β) (f : α × β → ℝ) :
    (L.extend κ hκ hκ1 z).avg f =
      ∑ ω, L.weight ω*∑ j, κ ω j*f (L.point ω, z ω j) := by
  change (∑ p : L.Ω × J, (L.weight p.1*κ p.1 p.2)*f (L.point p.1,z p.1 p.2)) = _
  rw [Fintype.sum_prod_type]
  simp only [mul_sum, mul_assoc]

lemma Law.extend_old {α β J : Type} [Fintype J] (L : Law α) (κ : L.Ω → J → ℝ)
    (hκ : ∀ ω j, 0 ≤ κ ω j) (hκ1 : ∀ ω, ∑ j, κ ω j=1)
    (z : L.Ω → J → β) (f : α → ℝ) :
    (L.extend κ hκ hκ1 z).avg (fun p => f p.1) = L.avg f := by
  rw [Law.extend_avg]
  simp [← sum_mul, hκ1, Law.avg]

def Law.map {α β : Type} (L : Law α) (f : α → β) : Law β :=
  { L with point := f ∘ L.point }

@[simp] lemma Law.map_avg {α β : Type} (L : Law α) (f : α → β) (g : β → ℝ) :
    (L.map f).avg g=L.avg (g ∘ f) := rfl

structure Tree (n : ℕ) [NeZero n] where
  parent : Fin n → Fin n
  root : parent 0=0
  lower : ∀ v : Fin n, v≠0 → (parent v).val<v.val

variable {n : ℕ} [NeZero n]

abbrev Tree.Child (T : Tree n) (v : Fin n) := {u : Fin n // u≠0 ∧ T.parent u=v}
instance (T : Tree n) (v : Fin n) : Fintype (T.Child v) := by
  classical
  unfold Tree.Child
  infer_instance
instance (T : Tree n) (v : Fin n) : DecidableEq (T.Child v) := Classical.decEq _

lemma Tree.child_gt (T : Tree n) (v : Fin n) (u : T.Child v) : v.val<u.val.val := by
  simpa [u.property.2] using T.lower u.val u.property.1

def Tree.park (T : Tree n) (q : Fin n → ℝ) (v : Fin n) : ℝ :=
  q v-∑ u : T.Child v, q u.val

def Tree.star (T : Tree n) (q : Fin n → ℝ) (v : Fin n) : Option (T.Child v) → ℝ
  | none => T.park q v
  | some u => q u.val

lemma Tree.star_sum (T : Tree n) (q : Fin n → ℝ) (v : Fin n) :
    ∑ i, T.star q v i=q v := by
  simp [Fintype.sum_option, Tree.star, Tree.park]

structure Counts (n : ℕ) where
  subtree : Fin n → ℤ
  park : Fin n → ℤ

structure PairState (n : ℕ) where
  old : Counts n
  new : Counts n

def Tree.intStar (T : Tree n) (c : Counts n) (v : Fin n) : Option (T.Child v) → ℤ
  | none => c.park v
  | some u => c.subtree u.val

def Tree.Consistent (T : Tree n) (c : Counts n) : Prop :=
  ∀ v, c.park v+∑ u : T.Child v, c.subtree u.val=c.subtree v

lemma Tree.intStar_sum (T : Tree n) {c : Counts n} (hc : T.Consistent c) (v : Fin n) :
    ∑ i, T.intStar c v i=c.subtree v := by
  simpa [Fintype.sum_option, Tree.intStar] using hc v

def Tree.Valid (T : Tree n) (q : Fin n → ℝ) (c : Counts n) : Prop :=
  (∀ v, 0 ≤ c.subtree v ∧ Balanced (q v) (c.subtree v)) ∧
  (∀ v, 0 ≤ c.park v ∧ Balanced (T.park q v) (c.park v)) ∧ T.Consistent c

def Tree.Means (T : Tree n) (q : Fin n → ℝ) (L : Law (Counts n)) : Prop :=
  (∀ v, L.avg (fun c => (c.subtree v:ℝ))=q v) ∧
  (∀ v, L.avg (fun c => (c.park v:ℝ))=T.park q v)

/-- Set just the new children and the new park of one star. -/
def Tree.setStar (T : Tree n) (c : Counts n) (v : Fin n)
    (z : Option (T.Child v) → ℤ) : Counts n where
  subtree u := if h : u≠0 ∧ T.parent u=v then z (some ⟨u,h⟩) else c.subtree u
  park u := if u=v then z none else c.park u

lemma Tree.setStar_old (T : Tree n) (c : Counts n) (v u : Fin n)
    (z : Option (T.Child v) → ℤ) (h : ¬(u≠0 ∧ T.parent u=v)) :
    (T.setStar c v z).subtree u=c.subtree u := by simp [Tree.setStar, h]

lemma Tree.setStar_child (T : Tree n) (c : Counts n) (v : Fin n)
    (z : Option (T.Child v) → ℤ) (u : T.Child v) :
    (T.setStar c v z).subtree u.val=z (some u) := by
  simp only [Tree.setStar, dite_eq_left u.property]

lemma Tree.setStar_root (T : Tree n) (c : Counts n) (v : Fin n)
    (z : Option (T.Child v) → ℤ) : (T.setStar c v z).subtree 0=c.subtree 0 := by
  simp [Tree.setStar]

lemma Tree.setStar_self (T : Tree n) (c : Counts n) (v : Fin n)
    (z : Option (T.Child v) → ℤ) : (T.setStar c v z).subtree v=c.subtree v := by
  apply T.setStar_old
  rintro ⟨hv,hp⟩
  have h := T.lower v hv
  rw [hp] at h
  exact (lt_irrefl _) h

lemma Tree.setStar_intStar (T : Tree n) (c : Counts n) (v : Fin n)
    (z : Option (T.Child v) → ℤ) : T.intStar (T.setStar c v z) v=z := by
  funext i
  cases i with
  | none => simp [Tree.intStar, Tree.setStar]
  | some u => exact T.setStar_child c v z u


lemma Tree.setStar_other (T : Tree n) (c : Counts n) (v w : Fin n)
    (z : Option (T.Child v) → ℤ) (hw : w≠v) :
    T.intStar (T.setStar c v z) w=T.intStar c w := by
  funext i
  cases i with
  | none => simp [Tree.intStar, Tree.setStar, hw]
  | some u =>
    apply T.setStar_old
    rintro ⟨_,hp⟩
    exact hw (u.property.2.symm.trans hp)

lemma Tree.setStar_before (T : Tree n) (c : Counts n) (v w : Fin n)
    (z : Option (T.Child v) → ℤ) (hw : w.val ≤ v.val) :
    (T.setStar c v z).subtree w=c.subtree w := by
  apply T.setStar_old
  rintro ⟨h0,hp⟩
  have h := T.lower w h0
  rw [hp] at h
  omega

def Tree.Assigned (T : Tree n) (m : ℕ) (v : Fin n) : Prop :=
  v=0 ∨ (T.parent v).val < m

lemma Tree.assigned_self (T : Tree n) (v : Fin n) : T.Assigned v.val v := by
  by_cases h : v=0
  · exact Or.inl h
  · exact Or.inr (T.lower v h)

lemma Tree.assigned_next (T : Tree n) (v u : Fin n) (h : T.Assigned (v.val+1) u) :
    T.Assigned v.val u ∨ (u≠0 ∧ T.parent u=v) := by
  by_cases h0 : u=0
  · exact Or.inl (Or.inl h0)
  rcases h with h | h
  · exact (h0 h).elim
  by_cases hp : (T.parent u).val<v.val
  · exact Or.inl (Or.inr hp)
  · right
    exact ⟨h0, Fin.ext (by omega)⟩

lemma Tree.assigned_not_child (T : Tree n) (v u : Fin n) (h : T.Assigned v.val u) :
    ¬(u≠0 ∧ T.parent u=v) := by
  rintro ⟨h0,hp⟩
  rcases h with h | h
  · exact h0 h
  · rw [hp] at h; exact lt_irrefl _ h

/-- The induction stores the original joint law and every already rounded
ancestor, so all conditional correlations are retained. -/
structure Stage (T : Tree n) (a b : Fin n → ℝ) (k : ℤ)
    (L₀ : Law (Counts n)) (m : ℕ) where
  law : Law (PairState n)
  oldLaw : ∀ f : Counts n → ℝ, law.avg (fun s => f s.old)=L₀.avg f
  oldValid : ∀ ω, T.Valid a (law.point ω).old
  root : ∀ ω, (law.point ω).new.subtree 0=k
  balanced : ∀ u, T.Assigned m u → ∀ ω,
    0 ≤ (law.point ω).new.subtree u ∧ Balanced (b u) ((law.point ω).new.subtree u)
  means : ∀ u, T.Assigned m u → law.avg (fun s => (s.new.subtree u:ℝ))=b u
  parkBalanced : ∀ u, u.val < m → ∀ ω,
    0 ≤ (law.point ω).new.park u ∧ Balanced (T.park b u) ((law.point ω).new.park u)
  parkMeans : ∀ u, u.val < m → law.avg (fun s => (s.new.park u:ℝ))=T.park b u
  consistent : ∀ u, u.val < m → ∀ ω,
    (law.point ω).new.park u+∑ c : T.Child u, (law.point ω).new.subtree c.val=
      (law.point ω).new.subtree u
  cost : ∀ u, u.val < m →
    law.avg (fun s => dist₁ (fun i => (T.intStar s.new u i:ℝ))
                              (fun i => (T.intStar s.old u i:ℝ))) ≤
      32*dist₁ (T.star a u) (T.star b u)+
        11*law.avg (fun s => |(s.new.subtree u:ℝ)-(s.old.subtree u:ℝ)|)

/-- The saved old law's means are valid at every intermediate refinement. -/
lemma Stage.oldMean {T : Tree n} {a b : Fin n → ℝ} {k : ℤ} {L₀ : Law (Counts n)}
    {m : ℕ} (S : Stage T a b k L₀ m) (hmean : T.Means a L₀) (v : Fin n)
    (i : Option (T.Child v)) :
    mean S.law.weight (fun ω => (T.intStar (S.law.point ω).old v i:ℝ))=T.star a v i := by
  change S.law.avg (fun s => (T.intStar s.old v i:ℝ)) = _
  rw [S.oldLaw (fun c => (T.intStar c v i:ℝ))]
  cases i with
  | none => exact hmean.2 v
  | some u => exact hmean.1 u.val

/-- A finite kernel is extended and its output written into one star. -/
def stepLaw {T : Tree n} (L : Law (PairState n)) (v : Fin n) {J : Type} [Fintype J]
    (κ : L.Ω → J → ℝ) (hκ : ∀ ω j, 0 ≤ κ ω j) (hκ1 : ∀ ω, ∑ j, κ ω j=1)
    (z : L.Ω → J → Option (T.Child v) → ℤ) : Law (PairState n) :=
  (L.extend κ hκ hκ1 z).map fun p => ⟨p.1.old,T.setStar p.1.new v p.2⟩

lemma stepLaw_avg {T : Tree n} (L : Law (PairState n)) (v : Fin n) {J : Type} [Fintype J]
    (κ : L.Ω → J → ℝ) (hκ : ∀ ω j, 0 ≤ κ ω j) (hκ1 : ∀ ω, ∑ j, κ ω j=1)
    (z : L.Ω → J → Option (T.Child v) → ℤ) (f : PairState n → ℝ) :
    (stepLaw L v κ hκ hκ1 z).avg f=
      ∑ ω, L.weight ω*∑ j, κ ω j*f ⟨(L.point ω).old,T.setStar (L.point ω).new v (z ω j)⟩ := by
  unfold stepLaw
  rw [Law.map_avg, Law.extend_avg]
  rfl

lemma stepLaw_preserve {T : Tree n} (L : Law (PairState n)) (v : Fin n) {J : Type} [Fintype J]
    (κ : L.Ω → J → ℝ) (hκ : ∀ ω j, 0 ≤ κ ω j) (hκ1 : ∀ ω, ∑ j, κ ω j=1)
    (z : L.Ω → J → Option (T.Child v) → ℤ) (f : PairState n → ℝ)
    (hf : ∀ s Z, f ⟨s.old,T.setStar s.new v Z⟩=f s) :
    (stepLaw L v κ hκ hκ1 z).avg f=L.avg f := by
  rw [stepLaw_avg]
  simp only [hf, ← sum_mul, hκ1, one_mul]
  rfl


/-- One complete top-down update. The only existence input is the proved
finite star kernel, not a policy or a tree-rounding interface. -/
theorem Stage.next {T : Tree n} {a b : Fin n → ℝ} {k : ℤ} {L₀ : Law (Counts n)}
    (ha : ∀ v, 0 ≤ a v) (hpa : ∀ v, 0 ≤ T.park a v)
    (hb : ∀ v, 0 ≤ b v) (hpb : ∀ v, 0 ≤ T.park b v)
    (hmean : T.Means a L₀) (v : Fin n) (S : Stage T a b k L₀ v.val) :
    Nonempty (Stage T a b k L₀ (v.val+1)) := by
  classical
  let L := S.law
  let old : L.Ω → Option (T.Child v) → ℤ := fun ω => T.intStar (L.point ω).old v
  let N : L.Ω → ℤ := fun ω => (L.point ω).new.subtree v
  have hsa : ∀ i, 0 ≤ T.star a v i := by
    intro i; cases i with
    | none => exact hpa v
    | some u => exact ha u.val
  have hsb : ∀ i, 0 ≤ T.star b v i := by
    intro i; cases i with
    | none => exact hpb v
    | some u => exact hb u.val
  have hX : ∀ ω i, Balanced (T.star a v i) (old ω i) := by
    intro ω i; cases i with
    | none => exact (S.oldValid ω).2.1 v |>.2
    | some u => exact (S.oldValid ω).1 u.val |>.2
  have hmX : ∀ i, mean L.weight (fun ω => (old ω i:ℝ))=T.star a v i := S.oldMean hmean v
  have hN : ∀ ω, Balanced (∑ i, T.star b v i) (N ω) := by
    rw [T.star_sum]
    exact fun ω => (S.balanced v (T.assigned_self v) ω).2
  have hmN : mean L.weight (fun ω => (N ω:ℝ))=∑ i, T.star b v i := by
    rw [T.star_sum]
    exact S.means v (T.assigned_self v)
  obtain ⟨κ,z,hκ,hκ1,hz,hztot,hzmean,hcost⟩ :=
    rounding_star L.weight L.nonneg L.total (T.star a v) (T.star b v)
      hsa hsb old N hX hmX hN hmN
  let R := stepLaw L v κ hκ hκ1 z
  have hpres (f : PairState n → ℝ)
      (hf : ∀ s Z, f ⟨s.old,T.setStar s.new v Z⟩=f s) : R.avg f=L.avg f :=
    stepLaw_preserve L v κ hκ hκ1 z f hf
  have hcount (u : Fin n) (hu : ¬(u≠0 ∧ T.parent u=v)) :
      R.avg (fun s => (s.new.subtree u:ℝ))=L.avg (fun s => (s.new.subtree u:ℝ)) := by
    apply hpres
    intro s Z
    rw [T.setStar_old _ _ _ _ hu]
  have hchild (u : T.Child v) : R.avg (fun s => (s.new.subtree u.val:ℝ))=b u.val := by
    rw [stepLaw_avg]
    simpa only [Tree.setStar_child, Tree.star] using hzmean (some u)
  have hpark : R.avg (fun s => (s.new.park v:ℝ))=T.park b v := by
    rw [stepLaw_avg]
    simpa only [Tree.setStar, ite_true, Tree.star] using hzmean none
  refine ⟨{
    law := R
    oldLaw := ?_
    oldValid := ?_
    root := ?_
    balanced := ?_
    means := ?_
    parkBalanced := ?_
    parkMeans := ?_
    consistent := ?_
    cost := ?_ }⟩
  · intro f
    exact (hpres _ (fun _ _ => rfl)).trans (S.oldLaw f)
  · intro ω
    exact S.oldValid ω.1
  · intro ω
    change (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree 0=k
    rw [T.setStar_root]
    exact S.root ω.1
  · intro u hu ω
    rcases T.assigned_next v u hu with hu | hu
    · change 0 ≤ (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree u ∧
        Balanced (b u) ((T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree u)
      rw [T.setStar_old _ _ _ _ (T.assigned_not_child v u hu)]
      exact S.balanced u hu ω.1
    · change 0 ≤ (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree u ∧
        Balanced (b u) ((T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree u)
      have he := T.setStar_child (L.point ω.1).new v (z ω.1 ω.2) ⟨u,hu⟩
      change (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree u=z ω.1 ω.2 (some ⟨u,hu⟩) at he
      rw [he]
      exact hz ω.1 ω.2 (some ⟨u,hu⟩)
  · intro u hu
    rcases T.assigned_next v u hu with hu | hu
    · exact (hcount u (T.assigned_not_child v u hu)).trans (S.means u hu)
    · exact hchild ⟨u,hu⟩
  · intro u hu ω
    change 0 ≤ (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).park u ∧
      Balanced (T.park b u) ((T.setStar (L.point ω.1).new v (z ω.1 ω.2)).park u)
    by_cases huv : u=v
    · subst u
      simpa only [Tree.setStar, ite_true, Tree.star] using hz ω.1 ω.2 none
    · have hul : u.val<v.val := by have hne := Fin.val_ne_of_ne huv; omega
      simpa only [Tree.setStar, ite_eq_right huv] using S.parkBalanced u hul ω.1
  · intro u hu
    by_cases huv : u=v
    · subst u; exact hpark
    · have hul : u.val<v.val := by have hne := Fin.val_ne_of_ne huv; omega
      have he : R.avg (fun s => (s.new.park u:ℝ))=L.avg (fun s => (s.new.park u:ℝ)) := by
        apply hpres
        intro s Z
        simp only [Tree.setStar, ite_eq_right huv]
      exact he.trans (S.parkMeans u hul)
  · intro u hu ω
    change (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).park u+
      ∑ c : T.Child u, (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree c.val=
      (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree u
    by_cases huv : u=v
    · subst u
      rw [T.setStar_self]
      have he := hztot ω.1 ω.2
      rw [Fintype.sum_option] at he
      simp only [Tree.setStar_child]
      simpa only [Tree.setStar, ite_true] using he
    · have hul : u.val<v.val := by have hne := Fin.val_ne_of_ne huv; omega
      rw [T.setStar_before _ _ _ _ hul.le]
      have he := congrArg (fun f => ∑ i, f i) (T.setStar_other (L.point ω.1).new v u (z ω.1 ω.2) huv)
      simp only [Fintype.sum_option, Tree.intStar] at he
      rw [he]
      exact S.consistent u hul ω.1
  · intro u hu
    by_cases huv : u=v
    · subst u
      have hleft : R.avg (fun s => dist₁ (fun i => (T.intStar s.new v i:ℝ))
            (fun i => (T.intStar s.old v i:ℝ)))=
          ∑ ω, L.weight ω*∑ j, κ ω j*dist₁ (fun i => (z ω j i:ℝ)) (fun i => (old ω i:ℝ)) := by
        rw [stepLaw_avg]
        simp only [Tree.setStar_intStar]
        rfl
      rw [hleft]
      have hright : R.avg (fun s => |(s.new.subtree v:ℝ)-(s.old.subtree v:ℝ)|)=
          mean L.weight (fun ω => |(N ω:ℝ)-∑ i, (old ω i:ℝ)|) := by
        rw [hpres _ (by intro s Z; rw [T.setStar_self])]
        unfold Law.avg mean
        apply sum_congr rfl
        intro ω _
        congr 1
        change |((L.point ω).new.subtree v:ℝ)-((L.point ω).old.subtree v:ℝ)| =
          |((L.point ω).new.subtree v:ℝ)-∑ i, (T.intStar (L.point ω).old v i:ℝ)|
        rw [← Int.cast_sum, T.intStar_sum (S.oldValid ω).2.2]
      rw [hright]
      exact hcost
    · have hul : u.val<v.val := by have hne := Fin.val_ne_of_ne huv; omega
      rw [hpres _ (by intro s Z; rw [T.setStar_other _ _ _ _ huv])]
      rw [hpres _ (by intro s Z; rw [T.setStar_before _ _ _ _ hul.le])]
      exact S.cost u hul


def initialCounts (k : ℤ) : Counts n where
  subtree v := if v=0 then k else 0
  park _ := 0

lemma stage_zero {T : Tree n} {a b : Fin n → ℝ} {k : ℤ} (hk : 0 ≤ k) (hb0 : b 0=(k:ℝ))
    (L₀ : Law (Counts n)) (hvalid : ∀ ω, T.Valid a (L₀.point ω)) :
    Nonempty (Stage T a b k L₀ 0) := by
  classical
  let L := L₀.map fun c => (⟨c,initialCounts k⟩ : PairState n)
  have hroot : ∀ ω, (L.point ω).new.subtree 0=k := by
    intro ω
    change (if (0 : Fin n)=0 then k else 0)=k
    simp
  refine ⟨{
    law := L
    oldLaw := fun _ => rfl
    oldValid := hvalid
    root := hroot
    balanced := ?_
    means := ?_
    parkBalanced := by intro u hu; omega
    parkMeans := by intro u hu; omega
    consistent := by intro u hu; omega
    cost := by intro u hu; omega }⟩
  · intro u hu ω
    have hu0 : u=0 := hu.resolve_right (by omega)
    subst u
    rw [hroot ω, hb0]
    exact ⟨hk, Or.inl (by simp)⟩
  · intro u hu
    have hu0 : u=0 := hu.resolve_right (by omega)
    subst u
    rw [hb0]
    calc _ = L.avg (fun _ => (k:ℝ)) := L.avg_congr fun ω => by rw [hroot ω]
         _ = _ := L.avg_const _

/-- All vertices are processed in increasing order; the parent order is the
only tree-shape assumption used by the constructive correlated coupling. -/
theorem tree_coupling {T : Tree n} {a b : Fin n → ℝ} {k : ℤ}
    (ha : ∀ v, 0 ≤ a v) (hpa : ∀ v, 0 ≤ T.park a v)
    (hb : ∀ v, 0 ≤ b v) (hpb : ∀ v, 0 ≤ T.park b v)
    (hk : 0 ≤ k) (hb0 : b 0=(k:ℝ)) (L₀ : Law (Counts n))
    (hvalid : ∀ ω, T.Valid a (L₀.point ω)) (hmean : T.Means a L₀) :
    ∃ L : Law (PairState n),
      (∀ f : Counts n → ℝ, L.avg (fun s => f s.old)=L₀.avg f) ∧
      (∀ ω, T.Valid a (L.point ω).old ∧ T.Valid b (L.point ω).new ∧ (L.point ω).new.subtree 0=k) ∧
      (∀ v, L.avg (fun s => (s.new.subtree v:ℝ))=b v) ∧
      (∀ v, L.avg (fun s => (s.new.park v:ℝ))=T.park b v) ∧
      (∀ v, L.avg (fun s => dist₁ (fun i => (T.intStar s.new v i:ℝ))
                                  (fun i => (T.intStar s.old v i:ℝ))) ≤
        32*dist₁ (T.star a v) (T.star b v)+
          11*L.avg (fun s => |(s.new.subtree v:ℝ)-(s.old.subtree v:ℝ)|)) := by
  have hstage : ∀ m, m ≤ n → Nonempty (Stage T a b k L₀ m) := by
    intro m
    induction m with
    | zero => intro _; exact stage_zero hk hb0 L₀ hvalid
    | succ m ih =>
      intro hm
      obtain ⟨S⟩ := ih (by omega)
      exact S.next ha hpa hb hpb hmean ⟨m,by omega⟩
  obtain ⟨S⟩ := hstage n le_rfl
  have hassigned (v : Fin n) : T.Assigned n v := Or.inr (T.parent v).isLt
  refine ⟨S.law,S.oldLaw,?_,?_,?_,?_⟩
  · intro ω
    exact ⟨S.oldValid ω, ⟨fun v => S.balanced v (hassigned v) ω,
      fun v => S.parkBalanced v v.isLt ω, fun v => S.consistent v v.isLt ω⟩,S.root ω⟩
  · intro v; exact S.means v (hassigned v)
  · intro v; exact S.parkMeans v v.isLt
  · intro v; exact S.cost v v.isLt


lemma Law.avg_mul {α : Type} (L : Law α) (c : ℝ) (f : α → ℝ) :
    L.avg (fun x => c*f x)=c*L.avg f := by
  simp only [Law.avg, mul_sum, mul_left_comm (L.weight _) c]

lemma Law.avg_le_of_support {α : Type} (L : Law α) {f g : α → ℝ}
    (h : ∀ ω, f (L.point ω) ≤ g (L.point ω)) : L.avg f ≤ L.avg g :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (L.nonneg ω)

/-- Every nonroot vertex occurs in exactly one child list. -/
def Tree.childEquiv (T : Tree n) : (Σ v : Fin n, T.Child v) ≃ {v : Fin n // v≠0} where
  toFun p := ⟨p.2.val,p.2.property.1⟩
  invFun u := ⟨T.parent u.val,⟨u.val,u.property,rfl⟩⟩
  left_inv := by
    rintro ⟨v,u,hu,hp⟩
    dsimp
    subst v
    rfl
  right_inv := by intro u; rfl

lemma Tree.weighted_children (T : Tree n) (w f : Fin n → ℝ) (h0 : f 0=0) :
    (∑ v, w v*∑ u : T.Child v, f u.val)=∑ u, w (T.parent u)*f u := by
  classical
  simp_rw [mul_sum]
  rw [← Fintype.sum_sigma (fun p : Σ v : Fin n, T.Child v => w p.1*f p.2.val)]
  have he := Fintype.sum_equiv (T.childEquiv)
    (fun p : Σ v : Fin n, T.Child v => w p.1*f p.2.val)
    (fun u : {v : Fin n // v≠0} => w (T.parent u.val)*f u.val)
    (by intro p; change w p.1*f p.2.val=w (T.parent p.2.val)*f p.2.val
        rw [p.2.property.2])
  rw [he]
  have hsub := Fintype.sum_subtype_add_sum_subtype (fun v : Fin n => v≠0)
    (fun u => w (T.parent u)*f u)
  have hz : (∑ u : {v : Fin n // ¬v≠0}, w (T.parent u.val)*f u.val)=0 := by
    apply sum_eq_zero
    intro u _
    have hu : u.val=0 := not_ne_iff.mp u.property
    simp [hu,h0]
  simpa only [hz, add_zero] using hsub

lemma Tree.star_distance (T : Tree n) (a b : Fin n → ℝ) (v : Fin n) :
    dist₁ (T.star a v) (T.star b v) ≤
      |a v-b v|+2*∑ u : T.Child v, |a u.val-b u.val| := by
  have hp : |T.park a v-T.park b v| ≤
      |a v-b v|+∑ u : T.Child v, |a u.val-b u.val| := by
    calc _ = |(a v-b v)-∑ u : T.Child v, (a u.val-b u.val)| := by
          unfold Tree.park
          rw [sum_sub_distrib]
          congr 1; ring
         _ ≤ |a v-b v|+|∑ u : T.Child v, (a u.val-b u.val)| := abs_sub _ _
         _ ≤ _ := add_le_add_right (abs_sum_le_sum_abs (fun u : T.Child v => a u.val-b u.val) Finset.univ) _
  simpa only [dist₁, Fintype.sum_option, Tree.star] using
    (show |T.park a v-T.park b v|+(∑ u : T.Child v, |a u.val-b u.val|) ≤
      |a v-b v|+2*∑ u : T.Child v, |a u.val-b u.val| by linarith)

lemma Tree.children_distance_le (T : Tree n) (c d : Counts n) (v : Fin n) :
    (∑ u : T.Child v, |(c.subtree u.val:ℝ)-(d.subtree u.val:ℝ)|) ≤
      dist₁ (fun i => (T.intStar c v i:ℝ)) (fun i => (T.intStar d v i:ℝ)) := by
  simp only [dist₁, Fintype.sum_option, Tree.intStar]
  linarith [abs_nonneg ((c.park v:ℝ)-(d.park v:ℝ))]

/-- The radius at a nonroot node is one tau-th of its parent radius. -/
lemma Tree.parent_weight (T : Tree n) {τ : ℝ} (hτ : 0 < τ) (w f : Fin n → ℝ)
    (hscale : ∀ u, u≠0 → w (T.parent u)=τ*w u) (h0 : f 0=0) :
    (∑ u, w u*f u)=(1/τ)*(∑ u, w (T.parent u)*f u) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro u _
  by_cases hu : u=0
  · simp [hu,h0]
  · rw [hscale u hu]
    field_simp

lemma Tree.star_weight_bound (T : Tree n) {τ : ℝ} (hτ : 0 < τ)
    (w a b : Fin n → ℝ) (hw : ∀ u, 0 ≤ w u)
    (hscale : ∀ u, u≠0 → w (T.parent u)=τ*w u) (h0 : a 0=b 0) :
    (∑ v, w v*dist₁ (T.star a v) (T.star b v)) ≤
      (2+1/τ)*(∑ u, w (T.parent u)*|a u-b u|) := by
  calc _ ≤ ∑ v, w v*(|a v-b v|+2*∑ u : T.Child v, |a u.val-b u.val|) :=
        sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (T.star_distance a b v) (hw v)
       _ = (∑ v, w v*|a v-b v|)+2*(∑ v, w v*∑ u : T.Child v, |a u.val-b u.val|) := by
        simp only [mul_add,mul_left_comm (w _) (2:ℝ),sum_add_distrib,mul_sum]
       _ = _ := by
        rw [T.weighted_children w (fun u => |a u-b u|) (by simp [h0]), T.parent_weight hτ w _ hscale (by simp [h0])]
        ring

/-- Finite, exact absorption of the local 32/11 bounds. No tree depth or
initialization cost enters the coefficient. -/
theorem Tree.rounding_absorption (T : Tree n) {τ : ℝ} (hτ : 22 ≤ τ)
    (w a b : Fin n → ℝ) (hw : ∀ u, 0 ≤ w u)
    (hscale : ∀ u, u≠0 → w (T.parent u)=τ*w u) (h0 : a 0=b 0)
    (L : Law (PairState n)) (hroot : ∀ ω, (L.point ω).new.subtree 0=(L.point ω).old.subtree 0)
    (hcost : ∀ v, L.avg (fun s => dist₁ (fun i => (T.intStar s.new v i:ℝ))
                                  (fun i => (T.intStar s.old v i:ℝ))) ≤
      32*dist₁ (T.star a v) (T.star b v)+
        11*L.avg (fun s => |(s.new.subtree v:ℝ)-(s.old.subtree v:ℝ)|)) :
    L.avg (fun s => ∑ u, w (T.parent u)*|(s.new.subtree u:ℝ)-(s.old.subtree u:ℝ)|) ≤
      132*(∑ u, w (T.parent u)*|a u-b u|) := by
  have ht : 0 < τ := by linarith
  let F : Fin n → PairState n → ℝ := fun u s => |(s.new.subtree u:ℝ)-(s.old.subtree u:ℝ)|
  let V := ∑ u, w (T.parent u)*|a u-b u|
  let N := L.avg (fun s => ∑ u, w (T.parent u)*F u s)
  have hV : 0 ≤ V := sum_nonneg fun u _ => mul_nonneg (hw _) (abs_nonneg _)
  have hN : 0 ≤ N := L.avg_nonneg fun s => sum_nonneg fun u _ => mul_nonneg (hw _) (abs_nonneg _)
  have hF0 : ∀ ω, F 0 (L.point ω)=0 := by intro ω; simp [F,hroot ω]
  have havg0 : L.avg (F 0)=0 := by
    calc _ = L.avg (fun _ => 0) := L.avg_congr hF0
         _ = 0 := L.avg_const _
  have hNavg : N=∑ u, w (T.parent u)*L.avg (F u) := by
    dsimp [N]
    rw [L.avg_sum]
    simp_rw [L.avg_mul]
  have hparent : (∑ v, w v*L.avg (F v))=(1/τ)*N := by
    rw [T.parent_weight ht w _ hscale havg0, hNavg]
  have hchildren : (∑ v, w v*L.avg (fun s => ∑ u : T.Child v, F u.val s))=N := by
    simp_rw [L.avg_sum]
    rw [T.weighted_children w (fun u => L.avg (F u)) havg0, hNavg]
  have hrec : N ≤ (64+32/τ)*V+(11/τ)*N := by
    calc N = ∑ v, w v*L.avg (fun s => ∑ u : T.Child v, F u.val s) := hchildren.symm
         _ ≤ ∑ v, w v*L.avg (fun s => dist₁ (fun i => (T.intStar s.new v i:ℝ))
              (fun i => (T.intStar s.old v i:ℝ))) := by
          apply sum_le_sum
          intro v _
          exact mul_le_mul_of_nonneg_left (L.avg_mono (fun s => T.children_distance_le s.new s.old v)) (hw v)
         _ ≤ ∑ v, w v*(32*dist₁ (T.star a v) (T.star b v)+11*L.avg (F v)) :=
          sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hcost v) (hw v)
         _ = 32*(∑ v, w v*dist₁ (T.star a v) (T.star b v))+11*(∑ v, w v*L.avg (F v)) := by
          simp only [mul_add,mul_left_comm (w _) (32:ℝ),mul_left_comm (w _) (11:ℝ),sum_add_distrib,mul_sum]
         _ ≤ 32*((2+1/τ)*V)+11*((1/τ)*N) := by
          rw [hparent]
          exact add_le_add_left (mul_le_mul_of_nonneg_left (T.star_weight_bound ht w a b hw hscale h0) (by norm_num : (0:ℝ) ≤32)) _
         _ = _ := by ring
  have h11 : 11/τ ≤ 1/2 := (div_le_iff₀ ht).mpr (by linarith)
  have h32 : 32/τ ≤ 2 := (div_le_iff₀ ht).mpr (by linarith)
  have hrec' : N ≤ 66*V+(1/2)*N := hrec.trans (add_le_add
    (mul_le_mul_of_nonneg_right (by linarith : 64+32/τ ≤66) hV)
    (mul_le_mul_of_nonneg_right h11 hN))
  change N ≤ 132*V
  linarith


def Law.pure {α : Type} (x : α) : Law α where
  Ω := Unit
  finite := inferInstance
  weight _ := 1
  nonneg _ := by norm_num
  total := by simp
  point _ := x

@[simp] lemma Law.avg_pure {α : Type} (x : α) (f : α → ℝ) : (Law.pure x).avg f=f x := by
  change (∑ ω : Unit, (1:ℝ)*f x)=f x
  simp

lemma balanced_integer {r : ℝ} {j k : ℤ} (hr : r=(k:ℝ)) (hj : Balanced r j) : j=k := by
  simpa [hr,KServer.Rounding.Balanced] using hj

/-- Deterministic park of all k units at the root, solely for initialization. -/
def stock (k : ℤ) : Counts n where
  subtree v := if v=0 then k else 0
  park v := if v=0 then k else 0

def stockMass (k : ℤ) (v : Fin n) : ℝ := if v=0 then (k:ℝ) else 0

lemma stockMass_park (T : Tree n) (k : ℤ) (v : Fin n) :
    T.park (stockMass k) v=stockMass k v := by
  have hs : (∑ u : T.Child v, stockMass k u.val)=0 :=
    sum_eq_zero fun u _ => by simp [stockMass,u.property.1]
  simp [Tree.park,hs]

lemma stock_valid (T : Tree n) {k : ℤ} (hk : 0 ≤ k) : T.Valid (stockMass k) (stock k) := by
  have hb (v : Fin n) : 0 ≤ (stock k : Counts n).subtree v ∧
      KServer.Rounding.Balanced (stockMass k v) ((stock k : Counts n).subtree v) := by
    by_cases hv : v=0
    · simp [stock,stockMass,hv,KServer.Rounding.Balanced,hk]
    · simp [stock,stockMass,hv,KServer.Rounding.Balanced]
  refine ⟨hb,?_,?_⟩
  · intro v
    rw [stockMass_park]
    exact hb v
  · intro v
    have hs : (∑ u : T.Child v, (stock k : Counts n).subtree u.val)=0 :=
      sum_eq_zero fun u _ => by simp [stock,u.property.1]
    change (stock k : Counts n).subtree v+_=(stock k).subtree v
    rw [hs,add_zero]

lemma stock_means (T : Tree n) (k : ℤ) : T.Means (stockMass k) (Law.pure (stock k)) := by
  constructor <;> intro v <;> simp [Law.avg_pure,stock,stockMass,stockMass_park]

/-- Actual balanced law at the initial fractional configuration. This is not
an assumed rounding interface: it is obtained by the finite star construction. -/
theorem tree_initialization (T : Tree n) (b : Fin n → ℝ) {k : ℤ} (hk : 0 ≤ k)
    (hb : ∀ v, 0 ≤ b v) (hpb : ∀ v, 0 ≤ T.park b v) (hb0 : b 0=(k:ℝ)) :
    ∃ L : Law (Counts n), (∀ ω, T.Valid b (L.point ω) ∧ (L.point ω).subtree 0=k) ∧
      T.Means b L := by
  have ha (v : Fin n) : 0 ≤ stockMass k v := by
    dsimp [stockMass]; split_ifs <;> positivity
  obtain ⟨R,hRold,hRv,hRs,hRp,hRc⟩ := tree_coupling ha
    (fun v => by rw [stockMass_park]; exact ha v) hb hpb hk hb0
      (Law.pure (stock k)) (fun _ => stock_valid T hk) (stock_means T k)
  refine ⟨R.map PairState.new,?_,?_,?_⟩
  · intro ω; exact (hRv ω).2
  · intro v; exact hRs v
  · intro v; exact hRp v

/-- Section09's one-step top-down rounding, including the uniform constant132.
The old marginal is kept exactly, and the new root and all parks are balanced. -/
theorem rounded_step (T : Tree n) {τ : ℝ} (hτ : 22 ≤ τ)
    (w a b : Fin n → ℝ) (hw : ∀ u, 0 ≤ w u)
    (hscale : ∀ u, u≠0 → w (T.parent u)=τ*w u) {k : ℤ} (hk : 0 ≤ k)
    (ha0 : a 0=(k:ℝ)) (hb0 : b 0=(k:ℝ))
    (ha : ∀ v, 0 ≤ a v) (hpa : ∀ v, 0 ≤ T.park a v)
    (hb : ∀ v, 0 ≤ b v) (hpb : ∀ v, 0 ≤ T.park b v)
    (L₀ : Law (Counts n)) (hvalid : ∀ ω, T.Valid a (L₀.point ω)) (hmean : T.Means a L₀) :
    ∃ L : Law (PairState n),
      (∀ f : Counts n → ℝ, L.avg (fun s => f s.old)=L₀.avg f) ∧
      (∀ ω, T.Valid a (L.point ω).old ∧ T.Valid b (L.point ω).new ∧ (L.point ω).new.subtree 0=k) ∧
      T.Means b (L.map PairState.new) ∧
      L.avg (fun s => ∑ u, w (T.parent u)*|(s.new.subtree u:ℝ)-(s.old.subtree u:ℝ)|) ≤
        132*(∑ u, w (T.parent u)*|a u-b u|) := by
  obtain ⟨L,hLold,hLv,hLs,hLp,hLc⟩ := tree_coupling ha hpa hb hpb hk hb0 L₀ hvalid hmean
  refine ⟨L,hLold,hLv,⟨hLs,hLp⟩,?_⟩
  apply T.rounding_absorption hτ w a b hw hscale (ha0.trans hb0.symm) L _ hLc
  intro ω
  rw [(hLv ω).2.2, balanced_integer ha0 ((hLv ω).1.1 0).2]

end KServer.TreeRounding

end

/- Finite-tree park conservation and geometric subcapacity. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Rounding

structure Tree (n : ℕ) [NeZero n] where
  parent : Fin n → Fin n
  root : parent 0=0
  lower : ∀ v : Fin n, v≠0 → (parent v).val<v.val

variable {n : ℕ} [NeZero n]

abbrev Tree.Child (T : Tree n) (v : Fin n) := {u : Fin n // u≠0 ∧ T.parent u=v}
instance (T : Tree n) (v : Fin n) : Fintype (T.Child v) := by
  classical
  unfold Tree.Child
  infer_instance
instance (T : Tree n) (v : Fin n) : DecidableEq (T.Child v) := Classical.decEq _

def Tree.park (T : Tree n) (q : Fin n → ℝ) (v : Fin n) : ℝ :=
  q v-∑ u : T.Child v, q u.val

def Tree.childEquiv (T : Tree n) : (Σ v : Fin n, T.Child v) ≃ {v : Fin n // v≠0} where
  toFun p := ⟨p.2.val,p.2.property.1⟩
  invFun u := ⟨T.parent u.val,⟨u.val,u.property,rfl⟩⟩
  left_inv := by
    rintro ⟨v,u,hu,hp⟩
    dsimp
    subst v
    rfl
  right_inv := by intro u; rfl

lemma Tree.weighted_children (T : Tree n) (w f : Fin n → ℝ) (h0 : f 0=0) :
    (∑ v, w v*∑ u : T.Child v, f u.val)=∑ u, w (T.parent u)*f u := by
  classical
  simp_rw [mul_sum]
  rw [← Fintype.sum_sigma (fun p : Σ v : Fin n, T.Child v => w p.1*f p.2.val)]
  have he := Fintype.sum_equiv (T.childEquiv)
    (fun p : Σ v : Fin n, T.Child v => w p.1*f p.2.val)
    (fun u : {v : Fin n // v≠0} => w (T.parent u.val)*f u.val)
    (by intro p; change w p.1*f p.2.val=w (T.parent p.2.val)*f p.2.val
        rw [p.2.property.2])
  rw [he]
  have hsub := Fintype.sum_subtype_add_sum_subtype (fun v : Fin n => v≠0)
    (fun u => w (T.parent u)*f u)
  have hz : (∑ u : {v : Fin n // ¬v≠0}, w (T.parent u.val)*f u.val)=0 := by
    apply sum_eq_zero
    intro u _
    have hu : u.val=0 := not_ne_iff.mp u.property
    simp [hu,h0]
  simpa only [hz, add_zero] using hsub

/-- True precisely on a vertex's descendants (including the vertex itself). -/
def Tree.under (T : Tree n) (v w : Fin n) : Bool :=
  if w=v then true else if _hw : w=0 then false else T.under v (T.parent w)
termination_by w.val
decreasing_by exact T.lower w _hw

lemma Tree.under_self (T : Tree n) (v : Fin n) : T.under v v=true := by
  rw [Tree.under,ite_eq_left rfl]

lemma Tree.under_le (T : Tree n) (v w : Fin n) (h : T.under v w=true) : v.val ≤ w.val := by
  by_cases hwv : w=v
  · subst w; exact le_rfl
  · by_cases hw0 : w=0
    · rw [Tree.under,ite_eq_right hwv,dite_eq_left hw0] at h
      contradiction
    · have hp : T.under v (T.parent w)=true := by
        rw [Tree.under,ite_eq_right hwv,dite_eq_right hw0] at h
        exact h
      exact (T.under_le v (T.parent w) hp).trans (T.lower w hw0).le
termination_by w.val
decreasing_by exact T.lower w hw0

lemma Tree.under_parent_self (T : Tree n) (v : Fin n) (hv : v≠0) :
    T.under v (T.parent v)=false := by
  cases hh : T.under v (T.parent v)
  · rfl
  · have h := T.under_le v (T.parent v) hh
    have := T.lower v hv
    omega

lemma Tree.under_zero (T : Tree n) (v : Fin n) : T.under v 0=(v==0) := by
  rw [Tree.under]
  by_cases h : v=0
  · subst v; simp
  · simp [h,Ne.symm h]

def Tree.indicator (T : Tree n) (v w : Fin n) : ℝ := if T.under v w then 1 else 0

lemma Tree.indicator_parent (T : Tree n) (v w : Fin n) (hw : w≠0) :
    T.indicator v w-T.indicator v (T.parent w) = if w=v then 1 else 0 := by
  by_cases h : w=v
  · subst w
    simp [Tree.indicator,T.under_self,T.under_parent_self v hw]
  · have he : T.under v w=T.under v (T.parent w) := by
      rw [Tree.under,ite_eq_right h,dite_eq_right hw]
    simp [Tree.indicator,he,h]

/-- Literal telescoping over one subtree of the concrete parent tree. -/
theorem Tree.park_subtree_total (T : Tree n) (q : Fin n → ℝ) (v : Fin n) :
    (∑ w, T.indicator v w*T.park q w)=q v := by
  classical
  let q0 : Fin n → ℝ := fun w => if w=0 then 0 else q w
  have hq0 : q0 0=0 := by simp [q0]
  have he : ∀ w, (∑ u : T.Child w, q u.val) = ∑ u : T.Child w, q0 u.val := by
    intro w
    apply sum_congr rfl
    intro u _
    simp [q0,u.property.1]
  have hs := T.weighted_children (T.indicator v) q0 hq0
  simp_rw [Tree.park,mul_sub,he]
  rw [sum_sub_distrib,hs,←sum_sub_distrib]
  have hpoint : ∀ w : Fin n,
      T.indicator v w*q w-T.indicator v (T.parent w)*q0 w = if w=v then q w else 0 := by
    intro w
    by_cases hw : w=0
    · subst w
      by_cases hv : v=0
      · subst v; simp [q0,Tree.indicator,T.under_zero]
      · simp [q0,Tree.indicator,T.under_zero,hv,Ne.symm hv]
    · simp only [q0,ite_eq_right hw]
      rw [←sub_mul,T.indicator_parent v w hw]
      split_ifs <;> simp
  simp_rw [hpoint]
  simp

lemma Tree.indicator_nonneg (T : Tree n) (v w : Fin n) : 0 ≤ T.indicator v w := by
  unfold Tree.indicator
  split <;> norm_num

lemma Tree.park_nonneg (T : Tree n) {q : Fin n → ℝ}
    (h : ∀ v, (∑ u : T.Child v, q u.val) ≤ q v) (v : Fin n) : 0 ≤ T.park q v :=
  sub_nonneg.mpr (h v)

/-- The mass of any finite collection of descendant parks is bounded by its
root allocation; overlapping depths do not introduce a height factor. -/
theorem Tree.selected_park_capacity (T : Tree n) (q : Fin n → ℝ) (v : Fin n)
    (hp : ∀ w, 0 ≤ T.park q w) (S : Finset (Fin n))
    (hS : ∀ w ∈ S, T.under v w=true) :
    (∑ w ∈ S, T.park q w) ≤ q v := by
  have hbound : (∑ w ∈ S, T.park q w) ≤ ∑ w, T.indicator v w*T.park q w := by
    calc _ = ∑ w ∈ S, T.indicator v w*T.park q w := by
          apply sum_congr rfl
          intro w hw
          simp [Tree.indicator,hS w hw]
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun w _ _ =>
          mul_nonneg (T.indicator_nonneg v w) (hp w))
  simpa [T.park_subtree_total] using hbound

/-- Several descendant collections may be charged simultaneously to a fixed
cut. The hypotheses are explicit incidence data, not an assumed mass bound. -/
theorem Tree.cut_park_capacity (T : Tree n) (q : Fin n → ℝ)
    (hp : ∀ w, 0 ≤ T.park q w) (S F : Finset (Fin n))
    (hcover : ∀ w ∈ S, ∃ v ∈ F, T.under v w=true) :
    (∑ w ∈ S, T.park q w) ≤ ∑ v ∈ F, q v := by
  classical
  have hpoint : ∀ w ∈ S, T.park q w ≤ ∑ v ∈ F, T.indicator v w*T.park q w := by
    intro w hw
    obtain ⟨v,hv,hu⟩ := hcover w hw
    calc _ = T.indicator v w*T.park q w := by simp [Tree.indicator,hu]
         _ ≤ _ := single_le_sum (fun z _ => mul_nonneg (T.indicator_nonneg z w) (hp w)) hv
  calc _ ≤ ∑ w ∈ S, ∑ v ∈ F, T.indicator v w*T.park q w := sum_le_sum hpoint
       _ = ∑ v ∈ F, ∑ w ∈ S, T.indicator v w*T.park q w := sum_comm
       _ ≤ ∑ v ∈ F, ∑ w, T.indicator v w*T.park q w := by
        apply sum_le_sum
        intro v _
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun w _ _ =>
          mul_nonneg (T.indicator_nonneg v w) (hp w))
       _ = _ := by simp_rw [T.park_subtree_total]

section Geometry
variable {Y : Type*} [MetricSpace Y] [Fintype Y] [DecidableEq Y]

/-- Finite posterior counting mass; repeated hidden locations contribute their
full weight and do not require an injective posterior support. -/
def countingMass (μ : Y → ℝ) (R : Finset Y) : ℝ := ∑ y ∈ R, μ y

omit [DecidableEq Y] in
/-- A cell with a nearby validity witness lies in the source's 67r ball. -/
lemma witness_ball_inclusion {R : Finset Y} {y z : Y} {r : ℝ}
    (hz : z ∈ R) (hnear : dist y z ≤ 27*r)
    (hdiam : ∀ a ∈ R, ∀ b ∈ R, dist a b ≤ 40*r) :
    R ⊆ univ.filter (fun a => dist y a ≤ 67*r) := by
  intro a ha
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  have ht := dist_triangle y z a
  have hd := hdiam z hz a ha
  linarith

omit [NeZero n] [MetricSpace Y] [Fintype Y] in
lemma disjoint_counting_mass {μ : Y → ℝ} (hμ : ∀ y, 0 ≤ μ y)
    {R : Fin n → Finset Y} {F : Finset (Fin n)} {B : Finset Y}
    (hdisj : Set.PairwiseDisjoint (↑F) R) (hsub : ∀ v ∈ F, R v ⊆ B) :
    (∑ v ∈ F, countingMass μ (R v)) ≤ countingMass μ B := by
  unfold countingMass
  rw [←sum_biUnion hdisj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro y hy
    obtain ⟨v,hv,hy⟩ := mem_biUnion.mp hy
    exact hsub v hv hy
  · intro y _ _
    exact hμ y

/-- Cumulative park capacity with the exact geometric radius 67. Grouping is by
actual tree ancestors; posterior regions are those fixed-prefix cells. The cut
F may contain unoccupied roots too, and can be the full depth-j cut. -/
theorem Tree.geometric_park_capacity (T : Tree n) (q : Fin n → ℝ)
    (hp : ∀ w, 0 ≤ T.park q w) (S F : Finset (Fin n))
    (hcover : ∀ w ∈ S, ∃ v ∈ F, T.under v w=true)
    (R : Fin n → Finset Y) (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y)
    {C r : ℝ} (hC : 0 ≤ C) (y : Y)
    (hq : ∀ v ∈ F, q v ≤ C*countingMass μ (R v))
    (hdisj : Set.PairwiseDisjoint (↑F) R)
    (hwitness : ∀ v ∈ F, ∃ z ∈ R v, dist y z ≤ 27*r)
    (hdiam : ∀ v ∈ F, ∀ a ∈ R v, ∀ b ∈ R v, dist a b ≤ 40*r) :
    (∑ w ∈ S, T.park q w) ≤
      C*countingMass μ (univ.filter (fun z => dist y z ≤ 67*r)) := by
  have hsub : ∀ v ∈ F, R v ⊆ univ.filter (fun z => dist y z ≤ 67*r) := by
    intro v hv
    obtain ⟨z,hz,hn⟩ := hwitness v hv
    exact witness_ball_inclusion hz hn (hdiam v hv)
  calc _ ≤ ∑ v ∈ F, q v := T.cut_park_capacity q hp S F hcover
       _ ≤ ∑ v ∈ F, C*countingMass μ (R v) := sum_le_sum hq
       _ = C*(∑ v ∈ F, countingMass μ (R v)) := (mul_sum _ _ _).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left (disjoint_counting_mass hμ hdisj hsub) hC

end Geometry

end KServer.Rounding

end

end OAI
