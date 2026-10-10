import OAI.Geometry.LatticeCovering.Rounding

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology

namespace SingleLatticeCovering.Folded
open Real Filter Topology Asymptotics

lemma eventually_rpow_ratio_bound {s t c : ℝ} (hst : s < t) (hc : 0 < c) :
    ∀ᶠ b : ℝ in atTop, b^s ≤ c*b^t := by
  have ht := tendsto_rpow_neg_atTop (sub_pos.mpr hst)
  filter_upwards [ht.eventually (gt_mem_nhds hc), eventually_gt_atTop (0 : ℝ)] with b hb hb0
  have he : b^(-(t-s)) = b^s/b^t := by
    rw [←Real.rpow_sub hb0]
    congr 1
    ring
  rw [he] at hb
  exact (div_lt_iff₀ (Real.rpow_pos_of_pos hb0 t)).mp hb |>.le

lemma eventually_prime_power (k : ℝ) (hk : 0 < k) :
    ∀ᶠ b : ℝ in atTop, ∀ p : ℝ, 0 < p →
      b*logMean (heightR b)-4*b^(56/100 : ℝ) ≤ Real.log p → b^k ≤ p := by
  filter_upwards [(logMean_tendsto.comp heightR_tendsto).eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_rpow_ratio_bound (by norm_num : (56/100 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1/4),
    eventually_logpow_bound (1 : ℝ) (by norm_num : (0 : ℝ) < 1) (inv_pos.mpr hk),
    eventually_gt_atTop (1 : ℝ)] with b hμ hr hl hb1
  intro p hp hlp
  have hb0 : 0 < b := by linarith
  rw [Real.rpow_one] at hr
  rw [Real.rpow_one, Real.rpow_one] at hl
  have hbl : b ≤ Real.log p := by
    dsimp only [Function.comp_apply] at hμ
    nlinarith [mul_le_mul_of_nonneg_left hμ hb0.le]
  have hkl : Real.log b*k ≤ b := by
    calc
      _ ≤ (k⁻¹*b)*k := mul_le_mul_of_nonneg_right hl hk.le
      _ = b := by field_simp
  rw [Real.rpow_def_of_pos hb0]
  exact (Real.exp_le_exp.mpr (hkl.trans hbl)).trans_eq (Real.exp_log hp)

lemma grid_slack_of_fourth {b h p : ℝ} (hb : 2 ≤ b) (hh : 0 < h)
    (hsq : h^2 ≤ b) (hp : b^4 ≤ p) :
    b*h^2/p ≤ b^(-(2 : ℝ)) ∧ p⁻¹ ≤ 1/(2*h^2) := by
  have hb0 : 0 < b := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have he : b^(-(2 : ℝ)) = 1/b^2 := by rw [Real.rpow_neg hb0.le, Real.rpow_two, one_div]
  constructor
  · rw [he, div_le_div_iff₀ hp0 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ b^3 by positivity)]
  · rw [inv_eq_one_div, div_le_div_iff₀ hp0 (by positivity)]
    nlinarith [sq_nonneg (b-2),sq_nonneg (b^2-2)]

lemma eventually_rounding_slack : ∀ᶠ b : ℝ in atTop, ∀ p : ℝ, 0 < p →
    b*logMean (heightR b)-4*b^(56/100 : ℝ) ≤ Real.log p →
      b*heightR b^2/p ≤ b^(-(1/20 : ℝ)) ∧
      b*heightR b^2/p ≤ (1/2 : ℝ)*b^(56/100 : ℝ) ∧
      p⁻¹ ≤ 1/(2*heightR b^2) := by
  filter_upwards [eventually_prime_power (4 : ℝ) (by norm_num), eventually_height_square_le,
    eventually_rpow_ratio_bound (by norm_num : (-2 : ℝ) < 56/100) (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (2 : ℝ)] with b hp hs hr hb
  intro p hp0 hlp
  have hp4 : b^4 ≤ p := by
    have ht := hp p hp0 hlp
    change b^((4 : ℕ) : ℝ) ≤ p at ht
    rwa [Real.rpow_natCast] at ht
  have hg := grid_slack_of_fourth hb (heightR_pos (by linarith)) hs hp4
  exact ⟨hg.1.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)), hg.1.trans hr,hg.2⟩


end SingleLatticeCovering.Folded


namespace SingleLatticeCovering.Folded
open Real Filter Topology MeasureTheory ConstructionA

lemma numerical_count_tail {b m : ℝ} (hb : 1 ≤ b)
    (hm : 2*b^(70/100 : ℝ) ≤ m) : 4/m ≤ 2*b^(-(1/20 : ℝ)) := by
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hp : 0 < b^(70/100 : ℝ) := Real.rpow_pos_of_pos hb0 _
  have hm0 : 0 < m := by linarith
  calc
    4/m ≤ 4/(2*b^(70/100 : ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hm
    _ = 2*b^(-(70/100 : ℝ)) := by rw [Real.rpow_neg hb0.le]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb (by norm_num)) (by norm_num)




lemma eventually_grid_mass : ∀ᶠ b : ℕ in atTop, ∀ (p : ℕ) [NeZero p], 0 < p →
    (b : ℝ)*logMean (height b)-4*(b : ℝ)^(56/100 : ℝ) ≤ Real.log p →
    |gridMass (ι := Fin b) (height b) p Finset.univ-1| ≤ 7*(b : ℝ)^(-(1/20 : ℝ)) ∧
    |gridMass (height b) p (gridEligible (ι := Fin b) (height b) (logMean (height b))
      ((b : ℝ)^(56/100 : ℝ)) ((b : ℝ)^(70/100 : ℝ)) p)-1| ≤ 7*(b : ℝ)^(-(1/20 : ℝ)) := by
  have hε : ∀ᶠ b : ℝ in atTop, b^(-(1/20 : ℝ)) ≤ 1/2 :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/20)).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [height_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_natCast_atTop_atTop.eventually eventually_central_mean,
    tendsto_natCast_atTop_atTop.eventually eventually_log_variance_tail,
    tendsto_natCast_atTop_atTop.eventually eventually_rounding_slack,
    tendsto_natCast_atTop_atTop.eventually hε, eventually_ge_atTop (2 : ℕ)]
    with b hh hm hv hs he hb
  intro p inst hp hlp
  have hb0 : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hb1 : 1 ≤ (b : ℝ) := by exact_mod_cast (show 1 ≤ b by omega)
  have hh0 : 0 < height b := by linarith
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp
  let e := (b : ℝ)^(-(1/20 : ℝ))
  let c := (1/2 : ℝ)*(b : ℝ)^(56/100 : ℝ)
  let r := (b : ℝ)^(70/100 : ℝ)
  let E := gridEligible (ι := Fin b) (height b) (logMean (height b)) (2*c) r p
  have he0 : 0 ≤ e := Real.rpow_nonneg hb0.le _
  have hc : 0 < c := mul_pos (by norm_num) (Real.rpow_pos_of_pos hb0 _)
  have hslack := hs (p : ℝ) hp0 hlp
  have hη : (b : ℝ)*height b^2*(p : ℝ)⁻¹ ≤ e := by simpa only [div_eq_mul_inv, height, heightR, e] using hslack.1
  have hηc : (b : ℝ)*height b^2*(p : ℝ)⁻¹ ≤ c := by simpa only [div_eq_mul_inv, height, heightR, c] using hslack.2.1
  have ha : 1-totalMass (height b)^b ≤ 2*e := by
    apply (height_totalMass_power_loss hb).2.trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)) (by norm_num)
  have hg : 1-3*e ≤ (cubeLaw (height b) : Measure (Fin b → ℝ)).real
      (continuousGood (height b) c r) := by
    have ht := continuous_good_mass (ι := Fin b) hh (by simpa using (show 0 < b by omega)) hc
      (by simpa only [Fintype.card_fin, height, heightR, r] using hm)
    have hct := numerical_count_tail hb1 hm
    have ht' : 1-(b : ℝ)*((Real.log 2+height b^2/8)/2)^2/c^2 -
        4/((b : ℝ)*Real.exp (-(height b^2)/8)/(height b*Real.sqrt (2*Real.pi))) ≤
        (cubeLaw (height b) : Measure (Fin b → ℝ)).real (continuousGood (height b) c r) := by
      simpa only [continuousGood, Fintype.card_fin] using ht
    change (b : ℝ)*((Real.log 2+height b^2/8)/2)^2/c^2 ≤ e at hv
    change 4/((b : ℝ)*Real.exp (-(height b^2)/8)/(height b*Real.sqrt (2*Real.pi))) ≤ 2*e at hct
    linarith
  have hout := grid_from_continuous (ι := Fin b) hh0 (show 0 ≤ 2*e by positivity)
    (show 0 ≤ 3*e by positivity) p hp E (continuousGood (height b) c r)
    (continuousGood_measurable hh0)
    (fun t ht htc => round_into_eligible hh0 p hp
      (by simpa only [Fintype.card_fin] using hηc) hslack.2.2 htc ht)
    (by simpa only [Fintype.card_fin] using ha) hg
    (by simpa only [Fintype.card_fin] using hη.trans he)
  have htwo : 2*c = (b : ℝ)^(56/100 : ℝ) := by dsimp [c]; ring
  simp only [Fintype.card_fin, E, htwo] at hout
  exact ⟨hout.1.trans (by linarith), hout.2.trans (by linarith)⟩


end SingleLatticeCovering.Folded





noncomputable section
open scoped BigOperators

namespace SingleLatticeCovering.Sampler

universe u v

section FiniteAverages
variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]

lemma expect_prod (f : α × β → ℝ) :
    (𝔼 z, f z) = 𝔼 a, 𝔼 b, f (a, b) := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div, Fintype.sum_prod_type, div_div]
  rw [mul_comm]


def consEquiv (k : ℕ) (α : Type u) : (Fin (k + 1) → α) ≃ α × (Fin k → α) where
  toFun w := (w 0, Fin.tail w)
  invFun z := Fin.cons z.1 z.2
  left_inv w := Fin.cons_self_tail w
  right_inv z := by simp

lemma expect_cons (k : ℕ) (f : (Fin (k + 1) → α) → ℝ) :
    (𝔼 w, f w) = 𝔼 a, 𝔼 w, f (Fin.cons a w) := by
  calc
    (𝔼 w, f w) = 𝔼 z : α × (Fin k → α), f (Fin.cons z.1 z.2) :=
      Fintype.expect_equiv (consEquiv k α) _ _ (fun w => by simp [consEquiv])
    _ = _ := expect_prod _

lemma expect_append (k j : ℕ) (f : (Fin (k+j) → α) → ℝ) :
    (𝔼 w, f w) = 𝔼 u : Fin k → α, 𝔼 v : Fin j → α, f (Fin.append u v) := by
  calc
    (𝔼 w, f w) = 𝔼 z : (Fin k → α) × (Fin j → α), f (Fin.append z.1 z.2) :=
      (Fintype.expect_equiv (Fin.appendEquiv k j) _ _ (fun _ => rfl)).symm
    _ = _ := expect_prod _


lemma expect_mono {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    (𝔼 a, f a) ≤ 𝔼 a, g a := Finset.expect_le_expect (fun a _ => h a)

lemma expect_nonneg {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ 𝔼 a, f a :=
  Finset.expect_nonneg (fun a _ => h a)

end FiniteAverages

section FiniteProbability
variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]


def probability (p : α → Prop) : ℝ := by
  classical
  exact 𝔼 x, if p x then 1 else 0

lemma probability_nonneg (p : α → Prop) : 0 ≤ probability p := by
  classical
  exact expect_nonneg (fun _ => by split_ifs <;> norm_num)

lemma probability_le_one [Nonempty α] (p : α → Prop) : probability p ≤ 1 := by
  classical
  exact Finset.expect_le Finset.univ_nonempty (fun _ _ => by split_ifs <;> norm_num)

lemma probability_mono {p q : α → Prop} (h : ∀ x, p x → q x) :
    probability p ≤ probability q := by
  classical
  apply expect_mono
  intro x
  by_cases hp : p x
  · simp [hp, h x hp]
  · by_cases hq : q x <;> simp [hp, hq]

lemma probability_union_le (p q : α → Prop) :
    probability (fun x => p x ∨ q x) ≤ probability p + probability q := by
  classical
  unfold probability
  rw [← Finset.expect_add_distrib]
  apply expect_mono
  intro x
  by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq]

lemma probability_false : probability (fun _ : α => False) = 0 := by
  simp [probability]

lemma probability_true [Nonempty α] : probability (fun _ : α => True) = 1 := by
  simp [probability]

lemma probability_compl [Nonempty α] (p : α → Prop) :
    probability (fun x => ¬ p x) = 1 - probability p := by
  classical
  unfold probability
  rw [← Fintype.expect_const (ι := α) (1 : ℝ), ← Finset.expect_sub_distrib]
  apply Finset.expect_congr rfl
  intro x _
  by_cases h : p x <;> simp [h]

lemma probability_prod (p : α × β → Prop) :
    probability p = 𝔼 a, probability (fun b => p (a,b)) := expect_prod _

lemma probability_fst [Nonempty β] (p : α → Prop) :
    probability (fun x : α × β => p x.1) = probability p := by
  rw [probability_prod]
  classical
  unfold probability
  apply Finset.expect_congr rfl
  intro x _
  by_cases h : p x <;> simp [h]

lemma probability_cons (k : ℕ) (p : (Fin (k+1) → α) → Prop) :
    probability p = 𝔼 a, probability (fun w : Fin k → α => p (Fin.cons a w)) := by
  classical
  exact expect_cons k _

lemma probability_cons_tail (k : ℕ) (p : (Fin (k+1) → α) → Prop) :
    probability p = 𝔼 w : Fin k → α, probability (fun a => p (Fin.cons a w)) := by
  classical
  rw [probability_cons]
  unfold probability
  rw [Finset.expect_comm]

lemma probability_append (k j : ℕ) (p : (Fin (k+j) → α) → Prop) :
    probability p = probability (fun z : (Fin k → α) × (Fin j → α) => p (Fin.append z.1 z.2)) := by
  classical
  unfold probability
  exact (Fintype.expect_equiv (Fin.appendEquiv k j) _ _ (fun _ => rfl)).symm


lemma probability_snd [Nonempty α] (p : β → Prop) :
    probability (fun x : α × β => p x.2) = probability p := by
  rw [probability_prod]
  exact Fintype.expect_const (ι := α) (probability p)


lemma probability_gt_le {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 < t) :
    probability (fun x => t < f x) ≤ (𝔼 x, f x) / t := by
  classical
  rw [le_div_iff₀ ht]
  unfold probability
  rw [Finset.expect_mul]
  apply expect_mono
  intro x
  by_cases h : t < f x
  · simpa [h] using h.le
  · simpa [h] using hf x

lemma probability_le_of_pointwise [Nonempty α] {p : α → Prop} [DecidablePred p] {f : α → ℝ} {a : ℝ}
    (h : ∀ x, (if p x then (1 : ℝ) else 0) ≤ f x) (hf : (𝔼 x, f x) ≤ a) :
    probability p ≤ a := by
  classical
  unfold probability
  apply (expect_mono (g := f) ?_).trans hf
  intro x
  by_cases hp : p x <;> simpa [hp] using h x

end FiniteProbability

section GroupAverages
variable {G : Type u} [AddCommGroup G] [Fintype G]

lemma expect_sub_right (f : G → ℝ) (a : G) :
    (𝔼 x, f (x - a)) = 𝔼 x, f x :=
  Fintype.expect_equiv (Equiv.subRight a) _ _ (fun _ => rfl)

lemma expect_sub_left (f : G → ℝ) (a : G) :
    (𝔼 x, f (a - x)) = 𝔼 x, f x :=
  Fintype.expect_equiv (Equiv.subLeft a) _ _ (fun _ => rfl)

lemma expect_correlation (f g : G → ℝ) :
    (𝔼 w, 𝔼 x, f x * g (x - w)) = (𝔼 x, f x) * 𝔼 x, g x := by
  rw [Finset.expect_comm]
  simp_rw [← Finset.mul_expect, expect_sub_left, ← Finset.expect_mul]


def step (w : G) (f : G → ℝ) (x : G) : ℝ := (f x + f (x - w)) / 2

lemma step_nonneg {G : Type u} [AddCommGroup G] [Fintype G] (w : G) {f : G → ℝ} (hf : ∀ x, 0 ≤ f x) (x : G) :
    0 ≤ step w f x := by exact div_nonneg (add_nonneg (hf x) (hf _)) (by norm_num)

lemma step_mean (w : G) (f : G → ℝ) : (𝔼 x, step w f x) = 𝔼 x, f x := by
  simp only [step, ← Finset.expect_div, Finset.expect_add_distrib, expect_sub_right]
  ring



lemma step_second_moment (f : G → ℝ) :
    (𝔼 w, 𝔼 x, (step w f x) ^ 2) =
      ((𝔼 x, (f x) ^ 2) + (𝔼 x, f x) ^ 2) / 2 := by
  have h (w x : G) : (step w f x) ^ 2 =
      ((f x) ^ 2 + (f (x-w)) ^ 2 + 2 * (f x * f (x-w))) / 4 := by
    unfold step
    ring
  have hs (w : G) : (𝔼 x, (f (x-w))^2) = 𝔼 x, (f x)^2 :=
    expect_sub_right (fun x => (f x)^2) w
  simp_rw [h, ← Finset.expect_div, Finset.expect_add_distrib,
    ← Finset.mul_expect, hs, Fintype.expect_const]
  rw [expect_correlation]
  ring


def binaryAverage : {k : ℕ} → (Fin k → G) → (G → ℝ) → G → ℝ
  | 0, _, f => f
  | _ + 1, w, f => step (w 0) (binaryAverage (Fin.tail w) f)

@[simp] lemma binaryAverage_zero {G : Type u} [AddCommGroup G] [Fintype G] (w : Fin 0 → G) (f : G → ℝ) :
    binaryAverage w f = f := rfl

@[simp] lemma binaryAverage_cons {G : Type u} [AddCommGroup G] [Fintype G] {k : ℕ} (a : G) (w : Fin k → G) (f : G → ℝ) :
    binaryAverage (Fin.cons a w) f = step a (binaryAverage w f) := rfl

lemma binaryAverage_mean {k : ℕ} (w : Fin k → G) (f : G → ℝ) :
    (𝔼 x, binaryAverage w f x) = 𝔼 x, f x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (𝔼 x, step (w 0) (binaryAverage (Fin.tail w) f) x) = _
    rw [step_mean, ih]

lemma binaryAverage_nonneg {k : ℕ} (w : Fin k → G) {f : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (x : G) : 0 ≤ binaryAverage w f x := by
  induction k generalizing x with
  | zero => exact hf x
  | succ k ih => exact step_nonneg _ (fun x => ih (Fin.tail w) x) x

lemma binaryAverage_sub_const {G : Type u} [AddCommGroup G] [Fintype G] {k : ℕ} (w : Fin k → G) (f : G → ℝ) (c : ℝ) (x : G) :
    binaryAverage w (fun y => f y - c) x = binaryAverage w f x - c := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change ((binaryAverage (Fin.tail w) (fun y => f y-c) x +
      binaryAverage (Fin.tail w) (fun y => f y-c) (x-w 0)) / 2) = _
    rw [ih, ih]
    change _ = (binaryAverage (Fin.tail w) f x + binaryAverage (Fin.tail w) f (x-w 0)) / 2-c
    ring



lemma binaryAverage_centered_second_moment (k : ℕ) (f : G → ℝ)
    (hf : (𝔼 x, f x) = 0) :
    (𝔼 w : Fin k → G, 𝔼 x, (binaryAverage w f x)^2) =
      (𝔼 x, (f x)^2) / (2 : ℝ)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [expect_cons, Finset.expect_comm]
    simp_rw [binaryAverage_cons, step_second_moment, binaryAverage_mean, hf,
      zero_pow (by decide : 2 ≠ 0), add_zero, ← Finset.expect_div]
    rw [ih, pow_succ]
    ring

lemma binaryAverage_variance (k : ℕ) (f : G → ℝ) :
    (𝔼 w : Fin k → G, 𝔼 x, (binaryAverage w f x - (𝔼 y, f y))^2) =
      (𝔼 x, (f x - (𝔼 y, f y))^2) / (2 : ℝ)^k := by
  simpa only [binaryAverage_sub_const] using
    binaryAverage_centered_second_moment k (fun x => f x - (𝔼 y, f y)) (by
      rw [Finset.expect_sub_distrib, Fintype.expect_const, sub_self])


lemma variance_eq (f : G → ℝ) :
    (𝔼 x, (f x - (𝔼 y, f y))^2) = (𝔼 x, (f x)^2) - (𝔼 x, f x)^2 := by
  have h (x : G) : (f x - (𝔼 y, f y))^2 =
      (f x)^2 - 2 * (𝔼 y, f y) * f x + (𝔼 y, f y)^2 := by ring
  simp_rw [h, Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect, Fintype.expect_const]
  ring

lemma lower_tail_le_variance {G : Type u} [AddCommGroup G] [Fintype G] (f : G → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hμ : 0 < 𝔼 x, f x) :
    probability (fun x => f x < (1-δ) * (𝔼 y, f y)) ≤
      (𝔼 x, (f x - (𝔼 y, f y))^2) / (δ * (𝔼 x, f x))^2 := by
  have ht : 0 < δ * (𝔼 y, f y) := mul_pos hδ hμ
  apply (probability_mono (q := fun x => (δ*(𝔼 y, f y))^2 <
    (f x - (𝔼 y, f y))^2) ?_).trans
      (probability_gt_le (fun x => sq_nonneg _) (sq_pos_of_pos ht))
  intro x hx
  nlinarith


lemma expected_bad_fraction_le (k : ℕ) (f : G → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hμ : 0 < 𝔼 x, f x) :
    (𝔼 w : Fin k → G,
      probability (fun x => binaryAverage w f x < (1-δ) * (𝔼 y, f y))) ≤
      (𝔼 x, (f x - (𝔼 y, f y))^2) / ((2 : ℝ)^k * (δ * (𝔼 x, f x))^2) := by
  have h (w : Fin k → G) := lower_tail_le_variance (binaryAverage w f) hδ
    (by simpa only [binaryAverage_mean] using hμ)
  simp only [binaryAverage_mean] at h
  have he := expect_mono h
  rw [← Finset.expect_div, binaryAverage_variance, div_div] at he
  exact he


def subsetShift {k : ℕ} (w : Fin k → G) (e : Fin k → Bool) : G :=
  ∑ i, if e i then w i else 0

lemma subsetShift_cons {G : Type u} [AddCommGroup G] [Fintype G] {k : ℕ} (w : Fin (k+1) → G) (b : Bool) (e : Fin k → Bool) :
    subsetShift w (Fin.cons b e) = (if b then w 0 else 0) + subsetShift (Fin.tail w) e := by
  simp [subsetShift, Fin.sum_univ_succ, Fin.tail]

lemma subsetShift_append {G : Type u} [AddCommGroup G] [Fintype G] {k j : ℕ} (u : Fin k → G) (v : Fin j → G)
    (a : Fin k → Bool) (b : Fin j → Bool) :
    subsetShift (Fin.append u v) (Fin.append a b) = subsetShift u a + subsetShift v b := by
  simp [subsetShift, Fin.sum_univ_add]


lemma expect_bool (f : Bool → ℝ) : (𝔼 b, f b) = (f false + f true)/2 := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.sum_bool]
  simp [add_comm]



lemma binaryAverage_eq_expect {k : ℕ} (w : Fin k → G) (f : G → ℝ) (x : G) :
    binaryAverage w f x = 𝔼 e : Fin k → Bool, f (x-subsetShift w e) := by
  induction k generalizing x with
  | zero => simp [subsetShift]
  | succ k ih =>
    rw [expect_cons, expect_bool]
    simp only [subsetShift_cons, Bool.false_eq_true, ↓reduceIte, zero_add,
      sub_add_eq_sub_sub]
    rw [← ih (Fin.tail w) x, ← ih (Fin.tail w) (x-w 0)]
    rfl

lemma binaryAverage_eq_sum {k : ℕ} (w : Fin k → G) (f : G → ℝ) (x : G) :
    binaryAverage w f x = (∑ e : Fin k → Bool, f (x-subsetShift w e)) / (2 : ℝ)^k := by
  rw [binaryAverage_eq_expect, Fintype.expect_eq_sum_div_card]
  simp



lemma binaryAverage_append {k j : ℕ} (u : Fin k → G) (v : Fin j → G) (f : G → ℝ) (x : G) :
    binaryAverage (Fin.append u v) f x = binaryAverage v (binaryAverage u f) x := by
  rw [binaryAverage_eq_expect, expect_append, Finset.expect_comm]
  simp_rw [subsetShift_append, binaryAverage_eq_expect]
  apply Finset.expect_congr rfl
  intro b _
  apply Finset.expect_congr rfl
  intro a _
  congr 1
  abel


lemma binaryAverage_mono {G : Type u} [AddCommGroup G] [Fintype G] {k : ℕ} (w : Fin k → G) {f g : G → ℝ}
    (h : ∀ x, f x ≤ g x) (x : G) : binaryAverage w f x ≤ binaryAverage w g x := by
  induction k generalizing x with
  | zero => exact h x
  | succ k ih =>
    change (binaryAverage (Fin.tail w) f x + binaryAverage (Fin.tail w) f (x-w 0))/2 ≤
      (binaryAverage (Fin.tail w) g x + binaryAverage (Fin.tail w) g (x-w 0))/2
    exact div_le_div_of_nonneg_right (add_le_add (ih _ x) (ih _ (x-w 0))) (by norm_num)

lemma binaryAverage_mul_const {G : Type u} [AddCommGroup G] [Fintype G] {k : ℕ} (w : Fin k → G) (f : G → ℝ) (c : ℝ) (x : G) :
    binaryAverage w (fun y => c * f y) x = c * binaryAverage w f x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change (binaryAverage (Fin.tail w) (fun y => c*f y) x +
      binaryAverage (Fin.tail w) (fun y => c*f y) (x-w 0))/2 = _
    rw [ih, ih]
    change _ = c * ((binaryAverage (Fin.tail w) f x + binaryAverage (Fin.tail w) f (x-w 0))/2)
    ring



def binarySum {k : ℕ} (w : Fin k → G) (f : G → ℝ) (x : G) : ℝ :=
  (2 : ℝ)^k * binaryAverage w f x

@[simp] lemma binarySum_zero {G : Type u} [AddCommGroup G] [Fintype G] (w : Fin 0 → G) (f : G → ℝ) (x : G) :
    binarySum w f x = f x := by simp [binarySum]

@[simp] lemma binarySum_cons {G : Type u} [AddCommGroup G] [Fintype G] {k : ℕ} (a : G) (w : Fin k → G) (f : G → ℝ) (x : G) :
    binarySum (Fin.cons a w) f x = binarySum w f x + binarySum w f (x-a) := by
  simp only [binarySum, binaryAverage_cons, step, pow_succ]
  ring


def potential (θ : ℝ) (f : G → ℝ) : ℝ := 𝔼 x, Real.exp (-θ * f x)

lemma potential_pos (θ : ℝ) (f : G → ℝ) : 0 < potential θ f :=
  Finset.expect_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty


lemma potential_square (θ : ℝ) (f : G → ℝ) :
    (𝔼 w, potential θ (fun x => f x + f (x-w))) = (potential θ f)^2 := by
  unfold potential
  simp_rw [mul_add, Real.exp_add]
  rw [expect_correlation (fun x => Real.exp (-θ * f x)) (fun x => Real.exp (-θ * f x)), pow_two]

lemma potential_step_failure (θ ε : ℝ) (f : G → ℝ) :
    probability (fun w => Real.exp ε * (potential θ f)^2 <
      potential θ (fun x => f x + f (x-w))) ≤ Real.exp (-ε) := by
  have hp := potential_pos θ f
  have ht : 0 < Real.exp ε * (potential θ f)^2 := mul_pos (Real.exp_pos _) (sq_pos_of_pos hp)
  have h := probability_gt_le
    (fun w => (potential_pos θ (fun x => f x + f (x-w))).le) ht
  rw [potential_square] at h
  convert h using 1
  rw [Real.exp_neg]
  field_simp



lemma potential_iteration_failure (θ ε a : ℝ) (f : G → ℝ)
    (h₀ : potential θ f ≤ Real.exp a) (k : ℕ) :
    probability (fun w : Fin k → G =>
      Real.exp ((2 : ℝ)^k * a + ((2 : ℝ)^k - 1) * ε) <
        potential θ (binarySum w f)) ≤ (k : ℝ) * Real.exp (-ε) := by
  induction k with
  | zero =>
    have h : (fun w : Fin 0 → G =>
        Real.exp ((2 : ℝ)^0 * a + ((2 : ℝ)^0 - 1)*ε) <
          potential θ (binarySum w f)) = (fun _ => False) := by
      funext w
      simp only [pow_zero, one_mul, sub_self, zero_mul, add_zero]
      simp only [show binarySum w f = f by funext x; simp]
      exact propext (iff_false_intro (not_lt_of_ge h₀))
    rw [h, probability_false]
    simp
  | succ k ih =>
    let T : ℝ := Real.exp ((2 : ℝ)^k * a + ((2 : ℝ)^k-1)*ε)
    have hT : 0 < T := Real.exp_pos _
    have hnext : Real.exp ((2 : ℝ)^(k+1)*a + ((2 : ℝ)^(k+1)-1)*ε) =
        Real.exp ε * T^2 := by
      dsimp [T]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      rw [pow_succ]
      ring
    rw [probability_cons_tail]
    have hcond (w : Fin k → G) :
        probability (fun z =>
          Real.exp ((2 : ℝ)^(k+1)*a+((2 : ℝ)^(k+1)-1)*ε) <
            potential θ (binarySum (Fin.cons z w) f)) ≤
          (if T < potential θ (binarySum w f) then 1 else 0) + Real.exp (-ε) := by
      by_cases hw : T < potential θ (binarySum w f)
      · simp only [hw, ↓reduceIte]
        exact (probability_le_one _).trans (by linarith [Real.exp_pos (-ε)])
      · have hle : potential θ (binarySum w f) ≤ T := le_of_not_gt hw
        simp only [hw, ↓reduceIte, zero_add]
        apply (probability_mono (q := fun z => Real.exp ε * (potential θ (binarySum w f))^2 <
          potential θ (fun x => binarySum w f x + binarySum w f (x-z))) ?_).trans
          (potential_step_failure θ ε (binarySum w f))
        intro z hz
        rw [hnext] at hz
        have hs : (potential θ (binarySum w f))^2 ≤ T^2 :=
          pow_le_pow_left₀ (potential_pos θ _).le hle 2
        have hb : binarySum (Fin.cons z w) f =
            fun x => binarySum w f x + binarySum w f (x-z) := by
          funext x
          exact binarySum_cons z w f x
        rw [hb] at hz
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le) hz
    have he := expect_mono hcond
    rw [Finset.expect_add_distrib, Fintype.expect_const] at he
    change _ ≤ probability (fun w : Fin k → G => T < potential θ (binarySum w f)) +
      Real.exp (-ε) at he
    dsimp [T] at he
    push_cast
    linarith


lemma exp_le_card_mul_potential (θ : ℝ) (f : G → ℝ) (x : G) :
    Real.exp (-θ * f x) ≤ (Fintype.card G : ℝ) * potential θ f := by
  classical
  rw [potential, Fintype.expect_eq_sum_div_card]
  have hc : (Fintype.card G : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hc]
  exact Finset.single_le_sum (f := fun y => Real.exp (-θ*f y))
    (fun y _ => (Real.exp_pos _).le) (Finset.mem_univ x)

lemma potential_bound_pointwise (θ a : ℝ) (f : G → ℝ)
    (h : potential θ f ≤ Real.exp a) (x : G) :
    -θ * f x ≤ Real.log (Fintype.card G) + a := by
  have hc : (0 : ℝ) < Fintype.card G := by positivity
  have he := (exp_le_card_mul_potential θ f x).trans (mul_le_mul_of_nonneg_left h hc.le)
  have heq : (Fintype.card G : ℝ) * Real.exp a =
      Real.exp (Real.log (Fintype.card G) + a) := by rw [Real.exp_add, Real.exp_log hc]
  rw [heq] at he
  exact Real.exp_le_exp.mp he

lemma potential_bound_binaryAverage {k : ℕ} (w : Fin k → G) (f : G → ℝ)
    {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (h : potential θ (binarySum w f) ≤
      Real.exp ((2 : ℝ)^k * (-θ+1) + ((2 : ℝ)^k-1)*(θ*δ))) (x : G) :
    1-δ-1/θ-Real.log (Fintype.card G)/(θ*(2 : ℝ)^k) ≤ binaryAverage w f x := by
  have hh := potential_bound_pointwise θ _ _ h x
  unfold binarySum at hh
  have hp : (0 : ℝ) < 2^k := by positivity
  have he : θ*(2 : ℝ)^k*(1-δ-1/θ-Real.log (Fintype.card G)/(θ*(2 : ℝ)^k)) =
      θ*(2 : ℝ)^k-θ*(2 : ℝ)^k*δ-(2 : ℝ)^k-Real.log (Fintype.card G) := by
    field_simp

  apply le_of_mul_le_mul_left (a := θ*(2 : ℝ)^k) _ (mul_pos hθ hp)
  rw [he]
  nlinarith [mul_nonneg hθ.le hδ]



lemma indicator_initial_potential {p : G → Prop} [DecidablePred p] {θ : ℝ}
    (hθ : 0 ≤ θ) (hp : probability (fun x => ¬p x) ≤ Real.exp (-2*θ)) :
    potential θ (fun x => if p x then 1 else 0) ≤ Real.exp (-θ+1) := by
  classical
  have hi (x : G) : Real.exp (-θ*(if p x then 1 else 0)) =
      (if ¬p x then 1 else 0) + (if p x then 1 else 0) * Real.exp (-θ) := by
    by_cases h : p x <;> simp [h]
  have he : potential θ (fun x => if p x then 1 else 0) =
      probability (fun x => ¬p x) + probability p * Real.exp (-θ) := by
    unfold potential probability
    simp_rw [hi, Finset.expect_add_distrib, ← Finset.expect_mul]
    congr 1
    · apply Finset.expect_congr rfl
      intro x _
      by_cases h : p x <;> simp [h]
    · congr 1
      apply Finset.expect_congr rfl
      intro x _
      by_cases h : p x <;> simp [h]
  rw [he]
  calc
    probability (fun x => ¬p x) + probability p * Real.exp (-θ) ≤
        Real.exp (-2*θ) + Real.exp (-θ) :=
      add_le_add hp (by nlinarith [probability_le_one p, Real.exp_pos (-θ)])
    _ ≤ 2 * Real.exp (-θ) := by
      have : Real.exp (-2*θ) ≤ Real.exp (-θ) := Real.exp_le_exp.mpr (by linarith)
      linarith
    _ ≤ Real.exp 1 * Real.exp (-θ) := by
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      exact mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring


lemma second_stage_failure {p : G → Prop} [DecidablePred p] {θ δ : ℝ}
    (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (hp : probability (fun x => ¬p x) ≤ Real.exp (-2*θ)) (k : ℕ) :
    probability (fun w : Fin k → G => ∃ x,
      binaryAverage w (fun y => if p y then 1 else 0) x <
        1-δ-1/θ-Real.log (Fintype.card G)/(θ*(2 : ℝ)^k)) ≤
      (k : ℝ) * Real.exp (-(θ*δ)) := by
  apply (probability_mono (q := fun w : Fin k → G =>
    Real.exp ((2 : ℝ)^k*(-θ+1)+((2 : ℝ)^k-1)*(θ*δ)) <
      potential θ (binarySum w (fun y => if p y then 1 else 0))) ?_).trans
      (potential_iteration_failure θ (θ*δ) (-θ+1) _ (indicator_initial_potential hθ.le hp) k)
  intro w hw
  by_contra h
  obtain ⟨x, hx⟩ := hw
  exact not_lt_of_ge (potential_bound_binaryAverage w _ hθ hδ (le_of_not_gt h) x) hx



lemma two_stage_failure (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) {δ θ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ < 1) (hθ : 0 < θ) (hμ : 0 < 𝔼 x, f x) (k j : ℕ) :
    probability (fun z : (Fin k → G) × (Fin j → G) => ∃ x,
      binaryAverage z.2 (binaryAverage z.1 f) x <
        (1-δ)*(𝔼 y, f y)*(1-δ-1/θ-Real.log (Fintype.card G)/(θ*(2 : ℝ)^j))) ≤
      ((𝔼 x, (f x-(𝔼 y, f y))^2) /
        ((2 : ℝ)^k*(δ*(𝔼 y, f y))^2)) / Real.exp (-2*θ) +
          (j : ℝ)*Real.exp (-(θ*δ)) := by
  classical
  let μ : ℝ := 𝔼 x, f x
  let β (u : Fin k → G) : ℝ := probability (fun x => binaryAverage u f x < (1-δ)*μ)
  let L : ℝ := 1-δ-1/θ-Real.log (Fintype.card G)/(θ*(2 : ℝ)^j)
  have ht : 0 < (1-δ)*μ := mul_pos (sub_pos.mpr hδ₁) hμ
  have hfirst : probability (fun u => Real.exp (-2*θ) < β u) ≤
      ((𝔼 x, (f x-μ)^2) / ((2 : ℝ)^k*(δ*μ)^2)) / Real.exp (-2*θ) := by
    have hb := probability_gt_le (f := β) (fun u => probability_nonneg _) (Real.exp_pos (-2*θ))
    have hc := expected_bad_fraction_le k f hδ hμ
    exact hb.trans (div_le_div_of_nonneg_right hc (Real.exp_pos _).le)
  rw [probability_prod]
  have hcond (u : Fin k → G) :
      probability (fun v : Fin j → G => ∃ x, binaryAverage v (binaryAverage u f) x <
        (1-δ)*μ*L) ≤
      (if Real.exp (-2*θ) < β u then 1 else 0) + (j : ℝ)*Real.exp (-(θ*δ)) := by
    by_cases hu : Real.exp (-2*θ) < β u
    · simp only [hu, ↓reduceIte]
      exact (probability_le_one _).trans (by
        have : 0 ≤ (j : ℝ)*Real.exp (-(θ*δ)) := by positivity
        linarith)
    · simp only [hu, ↓reduceIte, zero_add]
      let p : G → Prop := fun x => (1-δ)*μ ≤ binaryAverage u f x
      have hp : probability (fun x => ¬p x) ≤ Real.exp (-2*θ) := by
        simpa only [p, not_le] using (le_of_not_gt hu)
      have hpoint (x : G) : (1-δ)*μ*(if p x then 1 else 0) ≤ binaryAverage u f x := by
        by_cases hx : p x
        · rw [ite_eq_left hx, mul_one]
          exact hx
        · simpa [hx] using binaryAverage_nonneg u hf x
      have hsample (v : Fin j → G) (x : G) :
          (1-δ)*μ*binaryAverage v (fun y => if p y then 1 else 0) x ≤
            binaryAverage v (binaryAverage u f) x := by
        simpa only [binaryAverage_mul_const] using binaryAverage_mono v hpoint x
      apply (probability_mono (q := fun v : Fin j → G => ∃ x,
        binaryAverage v (fun y => if p y then 1 else 0) x < L) ?_).trans
        (second_stage_failure hθ hδ.le hp j)
      rintro v ⟨x, hx⟩
      refine ⟨x, ?_⟩
      by_contra hn
      have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hn) ht.le
      exact not_lt_of_ge (hh.trans (hsample v x)) hx
  have he := expect_mono hcond
  rw [Finset.expect_add_distrib, Fintype.expect_const] at he
  have hs : (𝔼 u : Fin k → G, if Real.exp (-2*θ) < β u then (1 : ℝ) else 0) =
      probability (fun u => Real.exp (-2*θ) < β u) := by
    unfold probability
    apply Finset.expect_congr rfl
    intro u _
    by_cases hu : Real.exp (-2*θ) < β u <;> simp
  rw [hs] at he
  exact he.trans (add_le_add hfirst le_rfl)



lemma two_stage_failure_three_delta (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) {δ θ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ < 1) (hθ : 0 < θ) (hμ : 0 < 𝔼 x, f x) (k j : ℕ)
    (hsmall : 1/θ+Real.log (Fintype.card G)/(θ*(2 : ℝ)^j) ≤ δ) :
    probability (fun z : (Fin k → G) × (Fin j → G) => ∃ x,
      binaryAverage z.2 (binaryAverage z.1 f) x < (1-3*δ)*(𝔼 y, f y)) ≤
      ((𝔼 x, (f x-(𝔼 y, f y))^2) /
        ((2 : ℝ)^k*(δ*(𝔼 y, f y))^2)) / Real.exp (-2*θ) +
          (j : ℝ)*Real.exp (-(θ*δ)) := by
  have ht : 0 ≤ (1-δ)*(𝔼 y, f y) := mul_nonneg (by linarith) hμ.le
  have hl : (1-3*δ)*(𝔼 y, f y) ≤
      (1-δ)*(𝔼 y, f y)*(1-δ-1/θ-Real.log (Fintype.card G)/(θ*(2 : ℝ)^j)) := by
    calc
      _ ≤ (1-δ)*(𝔼 y, f y)*(1-2*δ) := by
        nlinarith [mul_nonneg (sq_nonneg δ) hμ.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) ht
  exact (probability_mono (fun z hz => by
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, hx.trans_le hl⟩)).trans (two_stage_failure f hf hδ hδ₁ hθ hμ k j)


lemma sampler_explicit_parameters (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) {δ θ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ < 1) (hθ : 0 < θ) (hμ : 0 < 𝔼 x, f x) (k j : ℕ)
    (hsmall : 1/θ+Real.log (Fintype.card G)/(θ*(2 : ℝ)^j) ≤ δ) :
    probability (fun w : Fin (k+j) → G => ∃ x,
      (∑ e : Fin (k+j) → Bool, f (x-subsetShift w e)) / (2 : ℝ)^(k+j) <
        (1-3*δ)*(𝔼 y, f y)) ≤
      ((𝔼 x, (f x-(𝔼 y, f y))^2) /
        ((2 : ℝ)^k*(δ*(𝔼 y, f y))^2)) / Real.exp (-2*θ) +
          (j : ℝ)*Real.exp (-(θ*δ)) := by
  simp_rw [← binaryAverage_eq_sum]
  rw [probability_append]
  simp_rw [binaryAverage_append]
  exact two_stage_failure_three_delta f hf hδ hδ₁ hθ hμ k j hsmall

end GroupAverages
end SingleLatticeCovering.Sampler




noncomputable section
open Filter Topology Asymptotics


end
end
end
end
end
end
end
end
end

end OAI
