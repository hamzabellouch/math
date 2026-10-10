import OAI.Probability.SKGap.Model

namespace OAI

/-! Finite heat-bath mixing and positivity of the SK cutoff denominator. -/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SKCutoff
open SKGap

def siteKernel {n : ℕ} (g : Disorder n) (i : Fin n) :
    Matrix (Spin n) (Spin n) ℝ := Matrix.of fun x y =>
  (if y = x then weight g 0 x else 0) /
      (weight g 0 x + weight g 0 (SKGap.flip i x)) +
  (if y = SKGap.flip i x then weight g 0 (SKGap.flip i x) else 0) /
      (weight g 0 x + weight g 0 (SKGap.flip i x))

def transition {n : ℕ} (g : Disorder n) : Matrix (Spin n) (Spin n) ℝ :=
  if n = 0 then 1 else Matrix.of fun x y => (∑ i, siteKernel g i x y) / (n : ℝ)

def totalVariation {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y, |p y - q y|

def discreteDistance {n : ℕ} (g : Disorder n) (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun x => totalVariation ((transition g ^ k) x) (mass g 0))

def mixingTime {n : ℕ} (g : Disorder n) (ε : ℝ) : ℕ :=
  sInf {k : ℕ | discreteDistance g k ≤ ε}

def ratioEvent (n : ℕ) (ε η : ℝ) : Set (Disorder n) :=
  {g | 1 + η < (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ)}

variable {n : ℕ}

@[simp] theorem flip_same (i : Fin n) (x : Spin n) : SKGap.flip i x i = !(x i) := by
  simp [SKGap.flip]

@[simp] theorem flip_other (i j : Fin n) (x : Spin n) (h : j ≠ i) :
    SKGap.flip i x j = x j := by
  simp [SKGap.flip, h]

@[simp] theorem flip_flip (i : Fin n) (x : Spin n) : SKGap.flip i (SKGap.flip i x) = x := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [flip_other, h]

theorem flip_ne (i : Fin n) (x : Spin n) : SKGap.flip i x ≠ x := by
  intro h
  have hi := congrFun h i
  simp only [flip_same] at hi
  cases x i <;> simp_all

theorem weight_pos (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 < weight g h x := Real.exp_pos _

theorem partition_pos (g : Disorder n) (h : Fin n → ℝ) : 0 < partition g h := by
  exact Finset.sum_pos (fun x _ => weight_pos g h x) Finset.univ_nonempty

theorem mass_pos (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 < mass g h x := div_pos (weight_pos g h x) (partition_pos g h)

theorem mass_nonneg (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 ≤ mass g h x := (mass_pos g h x).le

@[simp] theorem sum_mass (g : Disorder n) (h : Fin n → ℝ) : ∑ x, mass g h x = 1 := by
  simp only [mass, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos g h))

theorem mass_le_one (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    mass g h x ≤ 1 := by
  rw [← sum_mass g h]
  exact Finset.single_le_sum (fun y _ => mass_nonneg g h y) (Finset.mem_univ x)

instance disorderLaw_probability (β : ℝ) (n : ℕ) : IsProbabilityMeasure (disorderLaw β n) := by
  unfold disorderLaw
  infer_instance

theorem siteKernel_nonneg (g : Disorder n) (i : Fin n) (x y : Spin n) :
    0 ≤ siteKernel g i x y := by
  have h₁ := (weight_pos g 0 x).le
  have h₂ := (weight_pos g 0 (SKGap.flip i x)).le
  dsimp [siteKernel, Matrix.of_apply]
  positivity

@[simp] theorem sum_siteKernel (g : Disorder n) (i : Fin n) (x : Spin n) :
    ∑ y, siteKernel g i x y = 1 := by
  simp only [siteKernel, Matrix.of_apply, Finset.sum_add_distrib, ← Finset.sum_div]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← add_div]
  exact div_self (ne_of_gt (add_pos (weight_pos g 0 x) (weight_pos g 0 _)))

theorem siteKernel_pos_self (g : Disorder n) (i : Fin n) (x : Spin n) :
    0 < siteKernel g i x x := by
  simp only [siteKernel, Matrix.of_apply, ite_true, (flip_ne i x).symm, ite_false,
    zero_div, add_zero]
  exact div_pos (weight_pos g 0 x) (add_pos (weight_pos g 0 x) (weight_pos g 0 _))

theorem siteKernel_pos_flip (g : Disorder n) (i : Fin n) (x : Spin n) :
    0 < siteKernel g i x (SKGap.flip i x) := by
  simp only [siteKernel, Matrix.of_apply, flip_ne, ite_false, ite_true, zero_div, zero_add]
  exact div_pos (weight_pos g 0 _) (add_pos (weight_pos g 0 x) (weight_pos g 0 _))

theorem siteKernel_detailed_balance (g : Disorder n) (i : Fin n) (x y : Spin n) :
    mass g 0 x * siteKernel g i x y = mass g 0 y * siteKernel g i y x := by
  by_cases h : y = x
  · subst y; rfl
  by_cases hf : y = SKGap.flip i x
  · subst y
    simp only [siteKernel, Matrix.of_apply, flip_flip, flip_ne, (flip_ne i x).symm,
      ite_false, ite_true, zero_div, zero_add]
    simp only [mass]
    rw [add_comm (weight g 0 (SKGap.flip i x)) (weight g 0 x)]
    ring
  · have hxy : x ≠ y := Ne.symm h
    have hxf : x ≠ SKGap.flip i y := by
      intro h'
      apply hf
      simpa only [flip_flip] using (congrArg (SKGap.flip i) h').symm
    simp [siteKernel, Matrix.of_apply, h, hf, hxy, hxf]

theorem transition_eq (g : Disorder n) (hn : n ≠ 0) :
    transition g = Matrix.of fun x y => (∑ i, siteKernel g i x y) / (n : ℝ) := by
  exact ite_eq_right hn

theorem transition_eq_zero (g : Disorder n) (hn : n = 0) :
    transition g = 1 := by
  exact ite_eq_left hn

theorem transition_stochastic (g : Disorder n) :
    transition g ∈ Matrix.rowStochastic ℝ (Spin n) := by
  classical
  by_cases hn : n = 0
  · rw [transition_eq_zero g hn]
    exact (Matrix.rowStochastic ℝ (Spin n)).one_mem
  · rw [transition_eq g hn, Matrix.mem_rowStochastic_iff_sum]
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · exact div_nonneg (Finset.sum_nonneg fun i _ => siteKernel_nonneg g i x y)
        (Nat.cast_nonneg n)
    · simp only [Matrix.of_apply]
      rw [← Finset.sum_div]
      rw [Finset.sum_comm]
      simp only [sum_siteKernel, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact div_self (Nat.cast_ne_zero.mpr hn)

theorem transition_nonneg (g : Disorder n) (x y : Spin n) :
    0 ≤ transition g x y := (transition_stochastic g).1 x y

theorem transition_power_stochastic (g : Disorder n) (k : ℕ) :
    transition g ^ k ∈ Matrix.rowStochastic ℝ (Spin n) :=
  (Matrix.rowStochastic ℝ (Spin n)).pow_mem (transition_stochastic g) k

theorem transition_power_nonneg (g : Disorder n) (k : ℕ) (x y : Spin n) :
    0 ≤ (transition g ^ k) x y := (transition_power_stochastic g k).1 x y

theorem transition_detailed_balance (g : Disorder n) (x y : Spin n) :
    mass g 0 x * transition g x y = mass g 0 y * transition g y x := by
  classical
  by_cases hn : n = 0
  · rw [transition_eq_zero g hn]
    simp only [Matrix.one_apply]
    by_cases h : x = y
    · subst y; rfl
    · simp [h, Ne.symm h]
  · rw [transition_eq g hn]
    simp only [Matrix.of_apply]
    simp only [← mul_div_assoc]
    congr 1
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => siteKernel_detailed_balance g i x y

theorem mass_stationary (g : Disorder n) :
    Matrix.vecMul (mass g 0) (transition g) = mass g 0 := by
  classical
  ext y
  simp only [Matrix.vecMul, dotProduct]
  calc
    _ = ∑ x, mass g 0 y * transition g y x :=
      Finset.sum_congr rfl fun x _ => transition_detailed_balance g x y
    _ = mass g 0 y := by
      rw [← Finset.mul_sum, Matrix.sum_row_of_mem_rowStochastic (transition_stochastic g),
        mul_one]

theorem mass_stationary_power (g : Disorder n) (k : ℕ) :
    Matrix.vecMul (mass g 0) (transition g ^ k) = mass g 0 := by
  classical
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, mass_stationary]

theorem transition_pos_of_fiber (g : Disorder n) (i : Fin n) (x y : Spin n)
    (hy : y = x ∨ y = SKGap.flip i x) : 0 < transition g x y := by
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)
  rw [transition_eq g hn, Matrix.of_apply]
  apply div_pos _ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  apply Finset.sum_pos'
  · exact fun j _ => siteKernel_nonneg g j x y
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    rcases hy with hy | hy
    · rw [hy]; exact siteKernel_pos_self g i x
    · rw [hy]; exact siteKernel_pos_flip g i x

theorem eq_or_eq_flip (i : Fin n) (x y : Spin n)
    (h : ∀ j, j ≠ i → y j = x j) : y = x ∨ y = SKGap.flip i x := by
  by_cases hi : y i = x i
  · left
    ext j
    by_cases hj : j = i
    · simpa [hj] using hi
    · exact h j hj
  · right
    ext j
    by_cases hj : j = i
    · subst j
      simp only [flip_same]
      cases hx : x i <;> cases hy : y i <;> simp_all
    · simpa [flip_other, hj] using h j hj

private def updatePrefix (k : ℕ) (x y : Spin n) : Spin n :=
  fun i => if i.val < k then y i else x i

private theorem updatePrefix_zero (x y : Spin n) : updatePrefix 0 x y = x := by
  ext i
  simp [updatePrefix]

private theorem updatePrefix_all (x y : Spin n) : updatePrefix n x y = y := by
  ext i
  simp [updatePrefix, i.isLt]

private theorem updatePrefix_step (g : Disorder n) (k : ℕ) (hk : k < n) (x y : Spin n) :
    0 < transition g (updatePrefix k x y) (updatePrefix (k + 1) x y) := by
  apply transition_pos_of_fiber g ⟨k, hk⟩
  apply eq_or_eq_flip
  intro j hj
  have hj' : j.val ≠ k := by
    intro he
    apply hj
    exact Fin.ext he
  simp only [updatePrefix]
  have ht : (j.val < k + 1) ↔ (j.val < k) := by omega
  simp only [ht]

theorem transition_power_positive (g : Disorder n) (x y : Spin n) :
    0 < (transition g ^ n) x y := by
  have h : ∀ k, k ≤ n → 0 < (transition g ^ k) x (updatePrefix k x y) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [updatePrefix_zero]
    | succ k ih =>
      intro hk
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_pos'
      · intro z _
        exact mul_nonneg (transition_power_nonneg g k x z)
          (transition_nonneg g z _)
      · refine ⟨updatePrefix k x y, Finset.mem_univ _, ?_⟩
        exact mul_pos (ih (by omega)) (updatePrefix_step g k (by omega) x y)
  simpa only [updatePrefix_all] using h n le_rfl

section FiniteMixing
variable {α : Type*} [Fintype α]

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem totalVariation_le_one (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hp₁ : ∑ x, p x = 1) (hq₁ : ∑ x, q x = 1) :
    totalVariation p q ≤ 1 := by
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ x, (p x + q x) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun x _ => by
        simpa only [abs_of_nonneg (hp x), abs_of_nonneg (hq x)] using abs_sub (p x) (q x)
    _ = 1 := by rw [Finset.sum_add_distrib, hp₁, hq₁]; norm_num

theorem totalVariation_contract [DecidableEq α] (Q : Matrix α α ℝ) (π p : α → ℝ) (δ : ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ α)
    (hs : Matrix.vecMul π Q = π) (hπ : ∑ x, π x = 1) (hp : ∑ x, p x = 1)
    (hminor : ∀ x y, δ * π y ≤ Q x y) :
    totalVariation (Matrix.vecMul p Q) π ≤ (1 - δ) * totalVariation p π := by
  classical
  have hid (y : α) : Matrix.vecMul p Q y - π y =
      ∑ x, (p x - π x) * (Q x y - δ * π y) := by
    calc
      _ = ∑ x, (p x - π x) * Q x y := by
        simp only [sub_mul, Finset.sum_sub_distrib]
        have hsy := congrFun hs y
        simpa only [Matrix.vecMul, dotProduct] using congrArg (fun z => Matrix.vecMul p Q y - z) hsy.symm
      _ = ∑ x, (p x - π x) * (Q x y - δ * π y) := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
        rw [hp, hπ, sub_self, zero_mul, sub_zero]
  have hrow (x : α) : ∑ y, (Q x y - δ * π y) = 1 - δ := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      Matrix.sum_row_of_mem_rowStochastic hQ, hπ, mul_one]
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ y, ∑ x, |p x - π x| * (Q x y - δ * π y) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro y _
      rw [hid]
      calc
        _ ≤ ∑ x, |(p x - π x) * (Q x y - δ * π y)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hminor x y))]
    _ = (1 - δ) * totalVariation p π := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hrow]
      rw [← Finset.sum_mul]
      unfold totalVariation
      ring

theorem totalVariation_power_bound [DecidableEq α]
    (Q : Matrix α α ℝ) (π : α → ℝ) (δ : ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ α)
    (hπ₀ : ∀ x, 0 ≤ π x) (hπ₁ : ∑ x, π x = 1)
    (hs : Matrix.vecMul π Q = π) (hδ : δ ≤ 1)
    (hminor : ∀ x y, δ * π y ≤ Q x y) (k : ℕ) (x : α) :
    totalVariation ((Q ^ k) x) π ≤ (1 - δ) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero]
    apply totalVariation_le_one
    · intro y
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num
    · exact hπ₀
    · simp [Matrix.one_apply]
    · exact hπ₁
  | succ k ih =>
    have hQk := (Matrix.rowStochastic ℝ α).pow_mem hQ k
    rw [pow_succ, pow_succ]
    change totalVariation (Matrix.vecMul ((Q ^ k) x) Q) π ≤ _
    calc
      _ ≤ (1 - δ) * totalVariation ((Q ^ k) x) π :=
        totalVariation_contract Q π _ δ hQ hs hπ₁
          (Matrix.sum_row_of_mem_rowStochastic hQk x) hminor
      _ ≤ (1 - δ) * (1 - δ) ^ k :=
        mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hδ)
      _ = _ := mul_comm _ _

end FiniteMixing

theorem mixing_set_nonempty (g : Disorder n) (ε : ℝ) (hε : 0 < ε) :
    {k : ℕ | discreteDistance g k ≤ ε}.Nonempty := by
  classical
  let Q := transition g ^ n
  let a : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun p : Spin n × Spin n => Q p.1 p.2)
  have ha : 0 < a := by
    apply (Finset.lt_inf'_iff _).mpr
    intro p _
    exact transition_power_positive g p.1 p.2
  have hal (x y : Spin n) : a ≤ Q x y :=
    Finset.inf'_le _ (Finset.mem_univ (x, y))
  let δ : ℝ := min (1 / 2) a
  have hδ₀ : 0 < δ := lt_min (by norm_num) ha
  have hδ₁ : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hminor (x y : Spin n) : δ * mass g 0 y ≤ Q x y := by
    calc
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (mass_le_one g 0 y) hδ₀.le
      _ = δ := mul_one _
      _ ≤ a := min_le_right _ _
      _ ≤ Q x y := hal x y
  have hc : Tendsto (fun k : ℕ => (1 - δ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hδ₁) (by linarith)
  obtain ⟨k, hk⟩ := (hc.eventually_lt_const hε).exists
  refine ⟨n * k, ?_⟩
  change discreteDistance g (n * k) ≤ ε
  apply le_trans _ hk.le
  apply (Finset.sup'_le_iff _ _).mpr
  intro x _
  rw [pow_mul]
  exact totalVariation_power_bound Q (mass g 0) δ (transition_power_stochastic g n)
    (mass_nonneg g 0) (sum_mass g 0) (mass_stationary_power g n) hδ₁ hminor k x

theorem mixingTime_spec (g : Disorder n) (ε : ℝ) (hε : 0 < ε) :
    discreteDistance g (mixingTime g ε) ≤ ε :=
  Nat.sInf_mem (mixing_set_nonempty g ε hε)

theorem mixingTime_le (g : Disorder n) (ε : ℝ) (k : ℕ)
    (hk : discreteDistance g k ≤ ε) : mixingTime g ε ≤ k :=
  Nat.sInf_le hk

theorem totalVariation_dirac {α : Type*} [Fintype α] [DecidableEq α]
    (π : α → ℝ) (hπ₀ : ∀ y, 0 ≤ π y) (hπ₁ : ∑ y, π y = 1) (x : α) :
    totalVariation ((1 : Matrix α α ℝ) x) π = 1 - π x := by
  have hx : π x ≤ 1 := by
    rw [← hπ₁]
    exact Finset.single_le_sum (fun y _ => hπ₀ y) (Finset.mem_univ x)
  have he (y : α) : |(1 : Matrix α α ℝ) x y - π y| =
      π y + if x = y then 1 - 2 * π x else 0 := by
    by_cases hxy : x = y
    · subst y
      simp only [Matrix.one_apply, ite_true, abs_of_nonneg (sub_nonneg.mpr hx)]
      ring
    · simp [hxy, abs_of_nonneg (hπ₀ y)]
  unfold totalVariation
  simp_rw [he]
  rw [Finset.sum_add_distrib, hπ₁]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem discreteDistance_zero (g : Disorder n) :
    discreteDistance g 0 =
      1 - Finset.univ.inf' Finset.univ_nonempty (mass g 0) := by
  classical
  unfold discreteDistance
  simp only [pow_zero, totalVariation_dirac (mass g 0) (mass_nonneg g 0) (sum_mass g 0)]
  apply le_antisymm
  · apply (Finset.sup'_le_iff _ _).mpr
    intro x hx
    exact sub_le_sub_left (Finset.inf'_le _ hx) 1
  · obtain ⟨x, hx, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (mass g 0)
    rw [he]
    exact Finset.le_sup' (fun x => 1 - mass g 0 x) hx

theorem discreteDistance_zero_lower (g : Disorder n) :
    1 - (1 / 2 : ℝ) ^ n ≤ discreteDistance g 0 := by
  classical
  rw [discreteDistance_zero]
  apply sub_le_sub_left
  let m := Finset.univ.inf' Finset.univ_nonempty (mass g 0)
  have hm : (Fintype.card (Spin n) : ℝ) * m ≤ 1 := by
    calc
      _ = ∑ _ : Spin n, m := by simp
      _ ≤ ∑ x, mass g 0 x :=
        Finset.sum_le_sum fun x hx => Finset.inf'_le _ hx
      _ = 1 := sum_mass g 0
  have hc : (Fintype.card (Spin n) : ℝ) * (1 / 2 : ℝ) ^ n = 1 := by
    simp only [Spin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_pow]
    norm_num
  have hcpos : 0 < (Fintype.card (Spin n) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  exact le_of_mul_le_mul_left (hm.trans_eq hc.symm) hcpos

theorem denominator_positive (g : Disorder n) (ε : ℝ) (hε : ε < 1)
    (hn : (1 / 2 : ℝ) ^ n < ε) : 0 < mixingTime g (1 - ε) := by
  apply Nat.pos_of_ne_zero
  intro ht
  have hm := mixingTime_spec g (1 - ε) (sub_pos.mpr hε)
  rw [ht] at hm
  have hd := discreteDistance_zero_lower g
  linarith

theorem denominator_pos_eventually (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1 - ε) := by
  have hc : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hc.eventually_lt_const hε₀] with n hn
  exact fun g => denominator_positive g ε hε₁ hn

theorem discreteDistance_antitone (g : Disorder n) : Antitone (discreteDistance g) := by
  classical
  apply antitone_nat_of_succ_le
  intro k
  apply (Finset.sup'_le_iff _ _).mpr
  intro x hx
  rw [pow_succ]
  change totalVariation (Matrix.vecMul ((transition g ^ k) x) (transition g)) (mass g 0) ≤ _
  calc
    _ ≤ totalVariation ((transition g ^ k) x) (mass g 0) := by
      simpa using totalVariation_contract (transition g) (mass g 0) ((transition g ^ k) x) 0
        (transition_stochastic g) (mass_stationary g) (sum_mass g 0)
        (Matrix.sum_row_of_mem_rowStochastic (transition_power_stochastic g k) x)
        (fun a b => by simpa using transition_nonneg g a b)
    _ ≤ discreteDistance g k :=
      Finset.le_sup' (fun z => totalVariation ((transition g ^ k) z) (mass g 0)) hx

theorem mixingTime_le_iff (g : Disorder n) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    mixingTime g ε ≤ k ↔ discreteDistance g k ≤ ε := by
  constructor
  · intro hk
    exact (discreteDistance_antitone g hk).trans (mixingTime_spec g ε hε)
  · exact mixingTime_le g ε k

theorem discreteDistance_tendsto_zero (g : Disorder n) :
    Tendsto (discreteDistance g) atTop (𝓝 0) := by
  classical
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun k => ha.trans_le <|
      (totalVariation_nonneg ((transition g ^ k) (fun _ => false)) (mass g 0)).trans <|
        Finset.le_sup' (fun z => totalVariation ((transition g ^ k) z) (mass g 0)) (Finset.mem_univ _)
  · intro b hb
    obtain ⟨k, hk⟩ := mixing_set_nonempty g (b / 2) (by linarith)
    filter_upwards [eventually_ge_atTop k] with l hl
    exact lt_of_le_of_lt ((discreteDistance_antitone g hl).trans hk) (by linarith)

@[fun_prop] theorem continuous_coupling (i j : Fin n) :
    Continuous (fun g : Disorder n => coupling g i j) := by
  unfold coupling
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_weight (h : Fin n → ℝ) (x : Spin n) :
    Continuous (fun g : Disorder n => weight g h x) := by
  unfold weight hamiltonian
  fun_prop

@[fun_prop] theorem continuous_partition (h : Fin n → ℝ) :
    Continuous (fun g : Disorder n => partition g h) := by
  unfold partition
  fun_prop

@[fun_prop] theorem continuous_mass (h : Fin n → ℝ) (x : Spin n) :
    Continuous (fun g : Disorder n => mass g h x) :=
  (continuous_weight h x).div (continuous_partition h) (fun g => ne_of_gt (partition_pos g h))

@[fun_prop] theorem continuous_siteKernel (i : Fin n) (x y : Spin n) :
    Continuous (fun g : Disorder n => siteKernel g i x y) := by
  have hc := (continuous_weight (0 : Fin n → ℝ) x).add (continuous_weight 0 (SKGap.flip i x))
  have hn (g : Disorder n) : weight g 0 x + weight g 0 (SKGap.flip i x) ≠ 0 :=
    ne_of_gt (add_pos (weight_pos g 0 x) (weight_pos g 0 _))
  simp only [siteKernel, Matrix.of_apply]
  apply Continuous.add
  all_goals
    apply Continuous.div
    · split_ifs <;> fun_prop
    · exact hc
    · exact hn

@[fun_prop] theorem continuous_transition (x y : Spin n) :
    Continuous (fun g : Disorder n => transition g x y) := by
  by_cases hn : n = 0
  · simp only [transition_eq_zero _ hn]
    exact continuous_const
  · simp only [transition_eq _ hn, Matrix.of_apply]
    fun_prop

@[fun_prop] theorem continuous_transition_power (k : ℕ) (x y : Spin n) :
    Continuous (fun g : Disorder n => (transition g ^ k) x y) := by
  induction k generalizing x y with
  | zero => simpa only [pow_zero] using (continuous_const : Continuous (fun _ : Disorder n => (1 : Matrix (Spin n) (Spin n) ℝ) x y))
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply]
    apply continuous_finsetSum
    intro z _
    exact (ih x z).mul (continuous_transition z y)

@[fun_prop] theorem continuous_discreteDistance (k : ℕ) :
    Continuous (fun g : Disorder n => discreteDistance g k) := by
  classical
  have h (x : Spin n) : Continuous (fun g : Disorder n =>
      totalVariation ((transition g ^ k) x) (mass g 0)) := by
    unfold totalVariation
    fun_prop
  have hc := Continuous.finset_sup' Finset.univ_nonempty
    (fun x (_ : x ∈ (Finset.univ : Finset (Spin n))) => h x)
  convert hc using 1
  ext g
  exact (Finset.sup'_apply Finset.univ_nonempty
    (fun (x : Spin n) (g : Disorder n) => totalVariation ((transition g ^ k) x) (mass g 0)) g).symm

theorem measurable_mixingTime (ε : ℝ) (hε : 0 < ε) :
    Measurable (fun g : Disorder n => mixingTime g ε) := by
  apply measurable_of_Iic
  intro k
  have hs : {g : Disorder n | mixingTime g ε ≤ k} =
      {g : Disorder n | discreteDistance g k ≤ ε} := by
    ext g
    exact mixingTime_le_iff g ε hε k
  change MeasurableSet {g : Disorder n | mixingTime g ε ≤ k}
  rw [hs]
  exact measurableSet_le (continuous_discreteDistance k).measurable measurable_const

theorem measurableSet_ratioEvent (n : ℕ) (ε η : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    MeasurableSet (ratioEvent n ε η) := by
  have he : Measurable (fun g : Disorder n => (mixingTime g ε : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (measurable_mixingTime ε hε₀)
  have hd : Measurable (fun g : Disorder n => (mixingTime g (1 - ε) : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_mixingTime (1 - ε) (sub_pos.mpr hε₁))
  exact measurableSet_lt measurable_const (he.div hd)

end SKCutoff
end

end OAI
