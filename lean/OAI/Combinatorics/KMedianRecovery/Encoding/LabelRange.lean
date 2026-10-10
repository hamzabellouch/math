import Mathlib

namespace OAI

namespace MetricKMedianRecovery.ColorLabel

noncomputable def labelRange (b : ℕ) : ℕ := 2 ^ Nat.clog 2 b

def label (b : ℕ) (hb : 0 < b) (x : Fin (labelRange b)) : Fin b :=
  ⟨x.val % b, Nat.mod_lt _ hb⟩

lemma labelRange_bounds (b : ℕ) (hb : 0 < b) : b ≤ labelRange b ∧ labelRange b < 2*b := by
  refine ⟨Nat.le_pow_clog (by decide) b, ?_⟩
  by_cases h : 1 < b
  · have he : Nat.clog 2 b = (Nat.clog 2 b-1)+1 := by
      have := Nat.clog_pos (by decide : 1 < 2) h
      omega
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) h
    have hp' : 2^(Nat.clog 2 b-1) < b := by simpa only [Nat.pred_eq_sub_one] using hp
    unfold labelRange
    rw [he, pow_succ]
    omega
  · have he : b=1 := by omega
    simp [he, labelRange]

noncomputable def labelMass (b : ℕ) (hb : 0 < b) (j : Fin b) : ℝ :=
  ∑ x : Fin (labelRange b), if label b hb x = j then 1/(labelRange b : ℝ) else 0

lemma labelMass_nonneg (b : ℕ) (hb : 0 < b) (j : Fin b) : 0 ≤ labelMass b hb j := by
  unfold labelMass
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

lemma labelMass_total (b : ℕ) (hb : 0 < b) : ∑ j : Fin b, labelMass b hb j = 1 := by
  unfold labelMass
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (labelRange b : ℝ) ≠ 0 := by
    have := (labelRange_bounds b hb).1
    exact_mod_cast (by omega : labelRange b ≠ 0)
  field_simp

lemma labelMass_lower (b : ℕ) (hb : 0 < b) (j : Fin b) :
    1/(2*(b:ℝ)) ≤ labelMass b hb j := by
  have hbound := labelRange_bounds b hb
  let x : Fin (labelRange b) := ⟨j.val, j.isLt.trans_le hbound.1⟩
  have hj : label b hb x = j := by apply Fin.ext; exact Nat.mod_eq_of_lt j.isLt
  have hs : 1/(labelRange b : ℝ) ≤ labelMass b hb j := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (labelRange b))))
      (f := fun x => if label b hb x = j then 1/(labelRange b:ℝ) else 0)
      (fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ x)
    simpa only [hj, ↓reduceIte, labelMass] using hh
  apply le_trans ?_ hs
  apply one_div_le_one_div_of_le
  · exact_mod_cast (lt_of_lt_of_le hb hbound.1)
  · exact_mod_cast hbound.2.le

lemma factorial_probability (b : ℕ) (hb : 0 < b) :
    (1/(2*Real.exp 1))^b ≤ (b.factorial : ℝ)*(1/(2*(b:ℝ)))^b := by
  have hbR : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hf : (0:ℝ) < b.factorial := Nat.cast_pos.mpr (Nat.factorial_pos b)
  have he := Real.pow_div_factorial_le_exp (b:ℝ) (Nat.cast_nonneg (α := ℝ) b) b
  have hexp : Real.exp (b:ℝ) = (Real.exp 1)^b := by
    simpa only [mul_one] using Real.exp_nat_mul 1 b
  rw [hexp, div_le_iff₀ hf] at he
  rw [div_pow, one_pow, div_pow, one_pow, mul_one_div]
  apply (div_le_div_iff₀ (pow_pos (mul_pos (by norm_num) (Real.exp_pos 1)) b)
    (pow_pos (mul_pos (by norm_num) hbR) b)).mpr
  rw [mul_pow, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ 2^b by positivity)]

noncomputable def distinctMass (b : ℕ) (μ : Fin b → ℝ) : ℝ := by
  classical
  exact ∑ f : Fin b → Fin b, if Function.Injective f then ∏ i, μ (f i) else 0

lemma distinctMass_lower (b : ℕ) (μ : Fin b → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (q : ℝ) (hq : 0 ≤ q) (hlower : ∀ j, q ≤ μ j) :
    (b.factorial : ℝ)*q^b ≤ distinctMass b μ := by
  classical
  let fn : Equiv.Perm (Fin b) → (Fin b → Fin b) := fun e => e
  have hinj : Function.Injective fn := fun _ _ h => Equiv.ext (congrFun h)
  let T := Finset.univ.image fn
  have hc : (T.card : ℝ) = b.factorial := by
    simp only [T, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin]
  have hlo : (b.factorial : ℝ)*q^b ≤
      ∑ f ∈ T, if Function.Injective f then ∏ i, μ (f i) else 0 := by
    rw [← hc]
    calc
      _ = ∑ _f ∈ T, q^b := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun f hf => by
        obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hf
        rw [ite_eq_left e.injective]
        have hh := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin b)))
          (fun _ _ => hq) (fun i _ => hlower (e i))
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh)
  exact hlo.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun f _ _ => by split_ifs; exact Finset.prod_nonneg (fun i _ => hμ (f i)); exact le_rfl))

lemma actual_distinct_probability (b : ℕ) (hb : 0 < b) :
    (1/(2*Real.exp 1))^b ≤ distinctMass b (labelMass b hb) := by
  exact (factorial_probability b hb).trans
    (distinctMass_lower b (labelMass b hb) (labelMass_nonneg b hb) _ (by positivity)
      (labelMass_lower b hb))

lemma distinctMass_zero (μ : Fin 0 → ℝ) : distinctMass 0 μ = 1 := by
  simp [distinctMass, Function.Injective]

lemma product_event {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I]
    (p : I → X → ℝ) (E : I → X → Prop) [∀ i, DecidablePred (E i)] :
    (∑ f : I → X, if ∀ i, E i (f i) then ∏ i, p i (f i) else 0) =
      ∏ i, ∑ x, if E i x then p i x else 0 := by
  classical
  have hh := Finset.sum_prod_piFinset (ι := I) (Finset.univ : Finset X)
    (fun i x => if E i x then p i x else 0)
  simpa only [Fintype.piFinset_univ, Fintype.prod_ite_zero] using hh

def color (x : Fin 4) : Fin 3 :=
  if x.val < 2 then 0 else if x.val = 2 then 1 else 2

noncomputable def colorMass (c : Fin 3) : ℝ :=
  ∑ x : Fin 4, if color x = c then (1/4 : ℝ) else 0

lemma colorMass_values (c : Fin 3) : colorMass c = if c=0 then (1/2 : ℝ) else 1/4 := by
  fin_cases c
  all_goals
    simp only [colorMass, Fin.sum_univ_succ]
    norm_num [color, Fin.ext_iff]

lemma colorMass_lower (c : Fin 3) : (1/4 : ℝ) ≤ colorMass c := by
  rw [colorMass_values]
  split_ifs <;> norm_num

lemma colorMass_total : ∑ c : Fin 3, colorMass c = 1 := by
  norm_num [colorMass_values, Fin.sum_univ_succ]

lemma specified_color_probability {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Finset I) (required : I → Fin 3) :
    (1/4 : ℝ)^Q.card ≤
      ∑ seed : I → Fin 4,
        if ∀ i ∈ Q, color (seed i) = required i then (1/4 : ℝ)^(Fintype.card I) else 0 := by
  classical
  have he : (∑ seed : I → Fin 4,
      if ∀ i ∈ Q, color (seed i) = required i then (1/4 : ℝ)^(Fintype.card I) else 0) =
      ∏ i ∈ Q, colorMass (required i) := by
    have hh := product_event (fun (_ : I) (_ : Fin 4) => (1/4 : ℝ))
      (fun i x => i ∈ Q → color x = required i)
    simp only [Finset.prod_const, Finset.card_univ] at hh
    rw [hh]
    have hsum : ∀ i : I,
        (∑ x : Fin 4, if i ∈ Q → color x = required i then (1/4 : ℝ) else 0) =
          if i ∈ Q then colorMass (required i) else 1 := by
      intro i
      by_cases hi : i ∈ Q
      · simp only [hi, true_implies, ↓reduceIte, colorMass]
      · simp [hi]
    simp_rw [hsum]
    simp only [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.prod_const_one, mul_one]
  rw [he]
  have hh := Finset.prod_le_prod₀ (s := Q) (f := fun _ => (1/4 : ℝ))
    (fun _ _ => by norm_num) (fun i _ => colorMass_lower (required i))
  simpa only [Finset.prod_const] using hh

lemma favorable_color_probability {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Finset I) (required : I → Fin 3) (m : ℕ) (hQ : Q.card ≤ 2*m) :
    (1/4 : ℝ)^(2*m) ≤
      ∑ seed : I → Fin 4,
        if ∀ i ∈ Q, color (seed i) = required i then (1/4 : ℝ)^(Fintype.card I) else 0 := by
  exact (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num) hQ).trans
    (specified_color_probability Q required)

lemma event_pushforward {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (w : X → ℝ) (E : Y → Prop) [DecidablePred E] :
    (∑ y : Y, if E y then ∑ x : X, if f x = y then w x else 0 else 0) =
      ∑ x : X, if E (f x) then w x else 0 := by
  classical
  have hh : ∀ y, (if E y then ∑ x : X, if f x = y then w x else 0 else 0) =
      ∑ x : X, if E y then (if f x = y then w x else 0) else 0 := by
    intro y
    split_ifs <;> simp
  simp_rw [hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have ht : ∀ y, (if E y then (if f x = y then w x else 0) else 0) =
      if f x = y then (if E (f x) then w x else 0) else 0 := by
    intro y
    by_cases h : f x = y
    · subst y; simp
    · simp [h]
  simp_rw [ht]
  simp

noncomputable def binaryDistinctMass (b : ℕ) (hb : 0 < b) : ℝ :=
  ∑ seed : Fin b → Fin (labelRange b),
    if Function.Injective (fun i => label b hb (seed i))
    then (1/(labelRange b : ℝ))^b else 0

lemma binaryDistinctMass_eq (b : ℕ) (hb : 0 < b) :
    binaryDistinctMass b hb = distinctMass b (labelMass b hb) := by
  classical
  symm
  have hprod : ∀ f : Fin b → Fin b,
      (∏ i, labelMass b hb (f i)) =
        ∑ seed : Fin b → Fin (labelRange b),
          if (fun i => label b hb (seed i)) = f then (1/(labelRange b : ℝ))^b else 0 := by
    intro f
    have hh := product_event (fun (_ : Fin b) (_ : Fin (labelRange b)) =>
      (1/(labelRange b : ℝ))) (fun i x => label b hb x = f i)
    simpa only [labelMass, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      funext_iff] using hh.symm
  unfold distinctMass
  simp_rw [hprod]
  exact event_pushforward (fun seed : Fin b → Fin (labelRange b) =>
    fun i => label b hb (seed i)) (fun _ => (1/(labelRange b : ℝ))^b) Function.Injective

lemma binary_distinct_probability (b : ℕ) (hb : 0 < b) :
    (1/(2*Real.exp 1))^b ≤ binaryDistinctMass b hb := by
  rw [binaryDistinctMass_eq]
  exact actual_distinct_probability b hb

end MetricKMedianRecovery.ColorLabel

end OAI
