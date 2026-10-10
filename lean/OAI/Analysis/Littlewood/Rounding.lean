import OAI.Analysis.Littlewood.Gaussian

namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- A Boolean encoding of a real sign. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem abs_boolSign (b : Bool) : |boolSign b| = 1 := by
  cases b <;> norm_num [boolSign]

/-- Elementary Rademacher MGF bound for one bounded coefficient. -/
theorem bool_exp_sum_le {a : ℝ} (ha : |a| ≤ 1) (t : ℝ) :
    (∑ b : Bool, Real.exp (t * a * boolSign b)) ≤ 2 * Real.exp (t ^ 2 / 2) := by
  simp only [Fintype.sum_bool, boolSign, ite_true, Bool.false_eq_true,
    ite_false, mul_one, mul_neg_one]
  calc
    Real.exp (t * a) + Real.exp (-(t * a)) = 2 * Real.cosh (t * a) := by
      rw [Real.cosh_eq]; ring
    _ ≤ 2 * Real.exp ((t * a) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq _) (by norm_num)
    _ ≤ 2 * Real.exp (t ^ 2 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_abs a, abs_nonneg a]
      nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ha2)]

/-- MGF bound for all signings of a bounded real row, with counting measure. -/
theorem signing_exp_sum_le {α : Type u} [Fintype α] [DecidableEq α] (a : α → ℝ)
    (ha : ∀ k, |a k| ≤ 1) (t : ℝ) :
    (∑ x : α → Bool, Real.exp (t * ∑ k, a k * boolSign (x k))) ≤
      2 ^ Fintype.card α * Real.exp (t ^ 2 * Fintype.card α / 2) := by
  classical
  calc
    _ = ∏ k : α, ∑ b : Bool, Real.exp (t * a k * boolSign b) := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ∏ _k : α, 2 * Real.exp (t ^ 2 / 2) := by
      apply Finset.prod_le_prod₀
      · intro k hk; positivity
      · intro k hk; exact bool_exp_sum_le (ha k) t
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, mul_pow]
      rw [← Real.exp_nat_mul]
      congr 2
      ring

/-- A pointwise bound for the cost of quantizing a row sum. -/
theorem round_abs_le_exp_pair {x d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t)
    (htd : 4 ≤ t * d) :
    |(round (x / d) : ℝ)| ≤
      Real.exp (t * x - t * d / 4) + Real.exp (-t * x - t * d / 4) := by
  by_cases hq : round (x / d) = 0
  · rw [hq, Int.cast_zero, abs_zero]
    positivity
  have hq1 : (1 : ℝ) ≤ |(round (x / d) : ℝ)| := by
    have hi : (1 : ℤ) ≤ |round (x / d)| := by
      have := abs_pos.mpr hq
      omega
    exact_mod_cast hi
  have hbound : |(round (x / d) : ℝ)| ≤ |x| / d + 1 / 2 := by
    calc
      _ ≤ |x / d| + |x / d - (round (x / d) : ℝ)| := by
        have h := abs_add_le (x / d) (-(x / d - (round (x / d) : ℝ)))
        simp only [abs_neg] at h
        convert h using 1; congr 1; ring
      _ ≤ _ := by
        rw [abs_div, abs_of_pos hd]
        gcongr
        exact abs_sub_round (x / d)
  have hxd : (|(round (x / d) : ℝ)| - 1 / 2) * d ≤ |x| := by
    have := (le_div_iff₀ hd).mp (by linarith :
      |(round (x / d) : ℝ)| - 1 / 2 ≤ |x| / d)
    exact this
  have hcost : |(round (x / d) : ℝ)| ≤ t * |x| - t * d / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hxd ht
    have hprod := mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr htd)
    nlinarith
  have hxexp : |(round (x / d) : ℝ)| ≤ Real.exp (t * |x| - t * d / 4) := by
    nlinarith [Real.add_one_le_exp (t * |x| - t * d / 4)]
  apply hxexp.trans
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg hx, mul_neg, ← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- Counting-measure bound for the average quantization cost of a bounded row. -/
theorem signing_round_sum_le {α : Type u} [Fintype α] [DecidableEq α] (a : α → ℝ)
    (ha : ∀ k, |a k| ≤ 1) {d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t)
    (htd : 4 ≤ t * d) :
    (∑ x : α → Bool, |(round ((∑ k, a k * boolSign (x k)) / d) : ℝ)|) ≤
      2 ^ Fintype.card α * (2 * Real.exp (t ^ 2 * Fintype.card α / 2 - t * d / 4)) := by
  classical
  calc
    _ ≤ ∑ x : α → Bool,
        (Real.exp (t * (∑ k, a k * boolSign (x k)) - t * d / 4) +
        Real.exp (-t * (∑ k, a k * boolSign (x k)) - t * d / 4)) := by
      exact Finset.sum_le_sum fun x hx ↦ round_abs_le_exp_pair hd ht htd
    _ = (Real.exp (-(t * d / 4))) *
        ((∑ x : α → Bool, Real.exp (t * ∑ k, a k * boolSign (x k))) +
        (∑ x : α → Bool, Real.exp (-t * ∑ k, a k * boolSign (x k)))) := by
      simp_rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      ring
    _ ≤ Real.exp (-(t * d / 4)) *
        (2 ^ Fintype.card α * Real.exp (t ^ 2 * Fintype.card α / 2) +
        2 ^ Fintype.card α * Real.exp ((-t) ^ 2 * Fintype.card α / 2)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (signing_exp_sum_le a ha t) (signing_exp_sum_le a ha (-t)))
        (Real.exp_pos _).le
    _ = _ := by
      simp only [neg_sq, Real.exp_sub, div_eq_mul_inv, Real.exp_neg]
      ring

/-- The geometric partition function for integer quantization labels. -/
theorem int_geometric_sum_le (S : Finset ℤ) {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 2) :
    (∑ z ∈ S, q ^ z.natAbs) ≤ Real.exp (4 * q) := by
  have hq1 : q < 1 := by linarith
  have hnat : HasSum (fun n : ℕ ↦ q ^ (n : ℤ).natAbs) (1 - q)⁻¹ := by
    simpa using hasSum_geometric_of_lt_one hq hq1
  have hneg : HasSum (fun n : ℕ ↦ q ^ (-(n : ℤ)).natAbs) (1 - q)⁻¹ := by
    simpa using hasSum_geometric_of_lt_one hq hq1
  have hfull := HasSum.of_nat_of_neg (f := fun z : ℤ ↦ q ^ z.natAbs) hnat hneg
  have hsum : (∑ z ∈ S, q ^ z.natAbs) ≤ (1 - q)⁻¹ + (1 - q)⁻¹ - 1 := by
    simpa using (hfull.summable.sum_le_tsum S (fun z hz ↦ pow_nonneg hq _)).trans_eq
      hfull.tsum_eq
  have hden : 0 < 1 - q := by linarith
  have hinv : (1 - q)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hid : (1 - q)⁻¹ + (1 - q)⁻¹ - 1 = 1 + 2 * q * (1 - q)⁻¹ := by
    field_simp [ne_of_gt hden]
    ring
  have hrat : (1 - q)⁻¹ + (1 - q)⁻¹ - 1 ≤ 1 + 4 * q := by
    rw [hid]
    have := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 2 * q by positivity)
    nlinarith
  exact hsum.trans (hrat.trans (by simpa [add_comm] using Real.add_one_le_exp (4 * q)))

/-- Each integer code has exponentially decaying weight. -/
theorem int_exp_sum_le (S : Finset ℤ) (a : ℝ) (ha : Real.exp (-a) ≤ 1 / 2) :
    (∑ z ∈ S, Real.exp (-a * |(z : ℝ)|)) ≤ Real.exp (4 * Real.exp (-a)) := by
  have heq (z : ℤ) : Real.exp (-a * |(z : ℝ)|) = Real.exp (-a) ^ z.natAbs := by
    have hc : (z.natAbs : ℝ) = |(z : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    rw [← hc, mul_comm, Real.exp_nat_mul]
  simp_rw [heq]
  exact int_geometric_sum_le S (Real.exp_pos _).le ha

/-- Finite families of quantization codes inherit a product partition bound. -/
theorem code_exp_sum_le {β : Type v} [Fintype β] [DecidableEq β]
    (C : Finset (β → ℤ)) (a : ℝ) (ha : Real.exp (-a) ≤ 1 / 2) :
    (∑ c ∈ C, Real.exp (-a * ∑ i, |(c i : ℝ)|)) ≤
      Real.exp (4 * Fintype.card β * Real.exp (-a)) := by
  classical
  let S : β → Finset ℤ := fun i ↦ C.image (fun c ↦ c i)
  have hsub : C ⊆ Fintype.piFinset S := by
    intro c hc
    exact Fintype.mem_piFinset.mpr fun i ↦ Finset.mem_image.mpr ⟨c, hc, rfl⟩
  calc
    _ ≤ ∑ c ∈ Fintype.piFinset S, Real.exp (-a * ∑ i, |(c i : ℝ)|) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ (Real.exp_pos _).le)
    _ = ∏ i : β, ∑ z ∈ S i, Real.exp (-a * |(z : ℝ)|) := by
      simp_rw [Finset.mul_sum, Real.exp_sum]
      exact (Finset.prod_univ_sum S (fun _ z ↦ Real.exp (-a * |(z : ℝ)|))).symm
    _ ≤ ∏ _i : β, Real.exp (4 * Real.exp (-a)) := by
      apply Finset.prod_le_prod₀
      · intro i hi; positivity
      · intro i hi; exact int_exp_sum_le (S i) a ha
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- A cost bound controls the number of possible quantization codes. -/
theorem code_card_le {β : Type v} [Fintype β] [DecidableEq β]
    (C : Finset (β → ℤ)) {a M : ℝ} (ha0 : 0 ≤ a)
    (ha : Real.exp (-a) ≤ 1 / 2) (hM : ∀ c ∈ C, (∑ i, |(c i : ℝ)|) ≤ M) :
    (C.card : ℝ) ≤ Real.exp (a * M + 4 * Fintype.card β * Real.exp (-a)) := by
  have hlow : (C.card : ℝ) * Real.exp (-a * M) ≤
      ∑ c ∈ C, Real.exp (-a * ∑ i, |(c i : ℝ)|) := by
    calc
      _ = ∑ _c ∈ C, Real.exp (-a * M) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro c hc
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hM c hc) (neg_nonpos.mpr ha0))
  have hfull := mul_le_mul_of_nonneg_left (hlow.trans (code_exp_sum_le C a ha))
    (Real.exp_pos (a * M)).le
  rw [← mul_assoc, mul_comm (Real.exp (a * M)) (C.card : ℝ), mul_assoc,
    ← Real.exp_add, show a * M + -a * M = 0 by ring, Real.exp_zero, mul_one,
    ← Real.exp_add] at hfull
  exact hfull

/-- Partition function of Hamming distance on the Boolean cube. -/
theorem hamming_exp_sum {α : Type u} [Fintype α] [DecidableEq α]
    (x : α → Bool) (a : ℝ) :
    (∑ y : α → Bool, Real.exp (-a * hammingDist x y)) =
      (1 + Real.exp (-a)) ^ Fintype.card α := by
  classical
  have hcast (y : α → Bool) : (hammingDist x y : ℝ) =
      ∑ k : α, if x k ≠ y k then (1 : ℝ) else 0 := by
    exact (Finset.sum_boole (fun k ↦ x k ≠ y k) Finset.univ).symm
  simp_rw [hcast, Finset.mul_sum, Real.exp_sum]
  rw [← Fintype.prod_sum (fun k b ↦ Real.exp (-a * if x k ≠ b then (1 : ℝ) else 0))]
  have hstep (k : α) : (∑ b : Bool, Real.exp (-a * if x k ≠ b then (1 : ℝ) else 0)) =
      1 + Real.exp (-a) := by
    cases x k <;> simp [add_comm]
  simp_rw [hstep]
  simp

/-- A small Hamming ball occupies exponentially less than the whole cube. -/
theorem hamming_small_family_card {α : Type u} [Fintype α] [DecidableEq α]
    (G : Finset (α → Bool)) (x : α → Bool)
    (hG : ∀ y ∈ G, (hammingDist x y : ℝ) ≤ (Fintype.card α : ℝ) / 16) :
    (G.card : ℝ) ≤ Real.exp (3 * Fintype.card α / 8) := by
  have he2 : Real.exp (-2) ≤ 1 / 4 := by
    rw [Real.exp_neg]
    apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr
    have h2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; norm_num at this; exact this
    have hh := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) h2
    rw [← Real.exp_add] at hh
    norm_num at hh ⊢
    exact hh
  have hsum : (∑ y : α → Bool, Real.exp (-2 * hammingDist x y)) ≤
      Real.exp (Fintype.card α / 4) := by
    rw [hamming_exp_sum]
    calc
      _ ≤ Real.exp (1 / 4) ^ Fintype.card α := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp (1 / 4)]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hlow : (G.card : ℝ) * Real.exp (-(Fintype.card α : ℝ) / 8) ≤
      ∑ y : α → Bool, Real.exp (-2 * hammingDist x y) := by
    calc
      _ = ∑ _y ∈ G, Real.exp (-(Fintype.card α : ℝ) / 8) := by simp
      _ ≤ ∑ y ∈ G, Real.exp (-2 * hammingDist x y) := by
        apply Finset.sum_le_sum
        intro y hy
        apply Real.exp_le_exp.mpr
        have := hG y hy
        linarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ (Real.exp_pos _).le)
  have h := mul_le_mul_of_nonneg_left (hlow.trans hsum)
    (Real.exp_pos ((Fintype.card α : ℝ) / 8)).le
  have heq : (Fintype.card α : ℝ) / 8 + -(Fintype.card α : ℝ) / 8 = 0 := by ring
  rw [← mul_assoc, mul_comm (Real.exp _) (G.card : ℝ), mul_assoc, ← Real.exp_add,
    heq, Real.exp_zero, mul_one, ← Real.exp_add] at h
  convert h using 1
  congr 1
  ring

/-- A nonnegative cost with small average is small on at least half a finite set. -/
theorem card_good_cost {γ : Type w} [Fintype γ] [DecidableEq γ]
    (f : γ → ℝ) (hf : ∀ x, 0 ≤ f x) {M : ℝ} (hM : 0 < M)
    (hsum : (∑ x, f x) ≤ (Fintype.card γ : ℝ) * M / 2) :
    (Fintype.card γ : ℝ) / 2 ≤ ((Finset.univ.filter fun x ↦ f x ≤ M).card : ℝ) := by
  classical
  let G := Finset.univ.filter fun x ↦ f x ≤ M
  let B := Finset.univ.filter fun x ↦ ¬ f x ≤ M
  have hcard : G.card + B.card = Fintype.card γ := by
    exact Finset.card_filter_add_card_filter_not _
  have hlow : (B.card : ℝ) * M ≤ ∑ x, f x := by
    calc
      _ = ∑ _x ∈ B, M := by simp
      _ ≤ ∑ x ∈ B, f x := by
        apply Finset.sum_le_sum
        intro x hx
        exact (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ ↦ hf x)
  have hc : (G.card : ℝ) + (B.card : ℝ) = Fintype.card γ := by exact_mod_cast hcard
  change _ ≤ (G.card : ℝ)
  nlinarith

/-- A large set of Boolean vectors contains a far pair with the same low-cost code. -/
theorem exists_same_code_far {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (G : Finset (α → Bool))
    (code : (α → Bool) → β → ℤ) {a M : ℝ} (ha0 : 0 ≤ a)
    (ha : Real.exp (-a) ≤ 1 / 2)
    (hcost : ∀ x ∈ G, (∑ i, |(code x i : ℝ)|) ≤ M)
    (hlarge : Real.exp (a * M + 4 * Fintype.card β * Real.exp (-a) +
      3 * Fintype.card α / 8) < (G.card : ℝ)) :
    ∃ x ∈ G, ∃ y ∈ G, code x = code y ∧
      (Fintype.card α : ℝ) / 16 < (hammingDist x y : ℝ) := by
  classical
  by_contra h
  have hnear : ∀ x ∈ G, ∀ y ∈ G, code x = code y →
      (hammingDist x y : ℝ) ≤ (Fintype.card α : ℝ) / 16 := by
    intro x hx y hy hxy
    by_contra! hn
    exact h ⟨x, hx, y, hy, hxy, hn⟩
  let C := G.image code
  have hC : (C.card : ℝ) ≤ Real.exp (a * M + 4 * Fintype.card β * Real.exp (-a)) := by
    apply code_card_le C ha0 ha
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    exact hcost x hx
  have hfiber (c : β → ℤ) (hc : c ∈ C) :
      ((G.filter fun x ↦ code x = c).card : ℝ) ≤ Real.exp (3 * Fintype.card α / 8) := by
    obtain ⟨x, hx, hxc⟩ := Finset.mem_image.mp hc
    apply hamming_small_family_card _ x
    intro y hy
    obtain ⟨hy, hyc⟩ := Finset.mem_filter.mp hy
    exact hnear x hx y hy (hxc.trans hyc.symm)
  have htotal : (G.card : ℝ) ≤ (C.card : ℝ) * Real.exp (3 * Fintype.card α / 8) := by
    calc
      _ = ∑ c ∈ C, ((G.filter fun x ↦ code x = c).card : ℝ) := by
        simpa using (Finset.sum_fiberwise_of_maps_to
          (fun x hx ↦ Finset.mem_image.mpr ⟨x, hx, rfl⟩ : ∀ x ∈ G, code x ∈ C)
          (fun _ ↦ (1 : ℝ))).symm
      _ ≤ ∑ _c ∈ C, Real.exp (3 * Fintype.card α / 8) := Finset.sum_le_sum hfiber
      _ = _ := by simp
  have hbound := htotal.trans (mul_le_mul_of_nonneg_right hC
    (Real.exp_pos (3 * Fintype.card α / 8)).le)
  rw [← Real.exp_add] at hbound
  exact (not_lt_of_ge hbound) hlarge

/-- Numerical entropy estimates, with fixed generous absolute constants. -/
theorem entropy_log_parameters {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R) :
    let L := Real.log (16 * R / s)
    1 / 2 ≤ L ∧ Real.exp (-4 * L) ≤ 1 / 2 ∧
      2 * R * Real.exp (-128 * L) ≤ s / (512 * L) ∧
      4 * R * Real.exp (-4 * L) ≤ s / 64 := by
  dsimp only
  let L := Real.log (16 * R / s)
  change 1 / 2 ≤ L ∧ _
  have hR : 0 < R := hs.trans_le hsR
  have hratio : (16 : ℝ) ≤ 16 * R / s := (le_div_iff₀ hs).mpr (by nlinarith)
  have hratio0 : 0 < 16 * R / s := by positivity
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hL : (1 / 2 : ℝ) ≤ L := hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
  have hL0 : 0 < L := by linarith
  have heq : Real.exp (-L) = s / (16 * R) := by
    dsimp [L]
    rw [Real.exp_neg, Real.exp_log hratio0, inv_div]
  have he : Real.exp (-L) ≤ 1 / 16 := by
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 16 * R)).mpr
    nlinarith
  have hbase : R * Real.exp (-L) = s / 16 := by
    rw [heq]
    field_simp

  have hfour : Real.exp (-4 * L) = Real.exp (-L) ^ 4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hdecay : Real.exp (-4 * L) ≤ 1 / 2 := by
    rw [hfour]
    calc
      _ ≤ (1 / 16 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le he 4
      _ ≤ _ := by norm_num
  have hpart : 4 * R * Real.exp (-4 * L) ≤ s / 64 := by
    have hp : Real.exp (-L) ^ 3 ≤ 1 / 16 := by
      calc
        _ ≤ (1 / 16 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le he 3
        _ ≤ _ := by norm_num
    calc
      _ = 4 * (R * Real.exp (-L)) * Real.exp (-L) ^ 3 := by rw [hfour]; ring
      _ = s / 4 * Real.exp (-L) ^ 3 := by rw [hbase]; ring
      _ ≤ s / 4 * (1 / 16) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hexp : 64 * L ≤ Real.exp (127 * L) := by
    nlinarith [Real.add_one_le_exp (127 * L)]
  have hmul : Real.exp (-128 * L) * (64 * L) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp (-128 * L) * Real.exp (127 * L) :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmean : 2 * R * Real.exp (-128 * L) ≤ s / (512 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 512 * L)).mpr
    calc
      _ = 16 * R * (Real.exp (-128 * L) * (64 * L)) := by ring
      _ ≤ 16 * R * Real.exp (-L) := mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = s := by nlinarith [hbase]
  exact ⟨hL, hdecay, hmean, hpart⟩

/-- The Boolean cube is larger than the entropy bounds used above. -/
theorem exp_small_lt_half_cube {n : ℕ} (hn : 32 ≤ n) :
    Real.exp (13 * n / 32) < (2 : ℝ) ^ n / 2 := by
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hu : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hn' : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hlt : 13 * (n : ℝ) / 32 < n * Real.log 2 - Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  calc
    _ < Real.exp (n * Real.log 2 - Real.log 2) := Real.exp_lt_exp.mpr hlt
    _ = _ := by rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- Entropy supplies two widely separated signings with identical rounded row sums. -/
theorem exists_signings_same_round {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (B : β → α → ℝ)
    (hB : ∀ i k, |B i k| ≤ 1) (hs : 32 ≤ Fintype.card α)
    (hsR : Fintype.card α ≤ Fintype.card β) :
    let d := 64 * Real.sqrt ((Fintype.card α : ℝ) *
      Real.log (16 * Fintype.card β / Fintype.card α))
    ∃ x y : α → Bool, (Fintype.card α : ℝ) / 16 < (hammingDist x y : ℝ) ∧
      ∀ i, round ((∑ k, B i k * boolSign (x k)) / d) =
        round ((∑ k, B i k * boolSign (y k)) / d) := by
  classical
  let s : ℝ := Fintype.card α
  let R : ℝ := Fintype.card β
  let L := Real.log (16 * R / s)
  let d := 64 * Real.sqrt (s * L)
  let t := d / (4 * s)
  let M := s / (256 * L)
  have hs0 : 0 < s := by dsimp [s]; exact_mod_cast (by omega : 0 < Fintype.card α)
  have hsR' : s ≤ R := by dsimp [s, R]; exact_mod_cast hsR
  obtain ⟨hL, hdecay, hmean, hpart⟩ := entropy_log_parameters hs0 hsR'
  change 1 / 2 ≤ L at hL
  have hL0 : 0 < L := by linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hd2 : d ^ 2 = 4096 * s * L := by
    dsimp [d]
    nlinarith [Real.sq_sqrt (show 0 ≤ s * L by positivity)]
  have htd_eq : t * d = 1024 * L := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (show 4 * s ≠ 0 by positivity)).mpr
    nlinarith [hd2]
  have htd : 4 ≤ t * d := by rw [htd_eq]; linarith
  have hexponent : t ^ 2 * s / 2 - t * d / 4 = -128 * L := by
    rw [htd_eq]
    have ht2 : t ^ 2 * s = 256 * L := by
      calc
        _ = d ^ 2 / (16 * s) := by dsimp [t]; field_simp; ring
        _ = 256 * L := by rw [hd2]; field_simp; ring
    rw [ht2]
    ring
  let code : (α → Bool) → β → ℤ := fun x i ↦
    round ((∑ k, B i k * boolSign (x k)) / d)
  let cost : (α → Bool) → ℝ := fun x ↦ ∑ i, |(code x i : ℝ)|
  have hcost0 : ∀ x, 0 ≤ cost x := fun x ↦ Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hcostsum : (∑ x, cost x) ≤ (2 : ℝ) ^ Fintype.card α * M / 2 := by
    have hrow (i : β) : (∑ x : α → Bool, |(code x i : ℝ)|) ≤
        (2 : ℝ) ^ Fintype.card α * (2 * Real.exp (-128 * L)) := by
      have h := signing_round_sum_le (B i) (hB i) hd ht htd
      change _ ≤ (2 : ℝ) ^ Fintype.card α * (2 * Real.exp (t ^ 2 * s / 2 - t * d / 4)) at h
      rwa [hexponent] at h
    calc
      _ = ∑ i, ∑ x : α → Bool, |(code x i : ℝ)| := Finset.sum_comm
      _ ≤ ∑ _i : β, (2 : ℝ) ^ Fintype.card α * (2 * Real.exp (-128 * L)) :=
        Finset.sum_le_sum fun i _ ↦ hrow i
      _ = (2 : ℝ) ^ Fintype.card α * (2 * R * Real.exp (-128 * L)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [R]
        ring
      _ ≤ (2 : ℝ) ^ Fintype.card α * (s / (512 * L)) :=
        mul_le_mul_of_nonneg_left hmean (by positivity)
      _ = _ := by dsimp [M]; ring
  let G := Finset.univ.filter fun x ↦ cost x ≤ M
  have hM : 0 < M := by dsimp [M]; positivity
  have hG : (2 : ℝ) ^ Fintype.card α / 2 ≤ (G.card : ℝ) := by
    have hc : (Fintype.card (α → Bool) : ℝ) = (2 : ℝ) ^ Fintype.card α := by simp
    have hh := card_good_cost cost hcost0 hM
    rw [hc] at hh
    exact hh hcostsum
  have haM : (4 * L) * M = s / 64 := by
    dsimp [M]
    field_simp
    ring
  have hlarge : Real.exp ((4 * L) * M + 4 * Fintype.card β * Real.exp (-(4 * L)) +
      3 * Fintype.card α / 8) < (G.card : ℝ) := by
    apply lt_of_lt_of_le _ hG
    apply lt_of_le_of_lt _ (exp_small_lt_half_cube hs)
    apply Real.exp_le_exp.mpr
    rw [haM]
    change s / 64 + 4 * R * Real.exp (-(4 * L)) + 3 * s / 8 ≤ 13 * s / 32
    have hp : 4 * R * Real.exp (-(4 * L)) ≤ s / 64 := by simpa only [neg_mul] using hpart
    linarith
  obtain ⟨x, hx, y, hy, hxy, hfar⟩ := exists_same_code_far G code
    (show 0 ≤ 4 * L by positivity) (by simpa only [neg_mul] using hdecay)
    (fun x hx ↦ (Finset.mem_filter.mp hx).2) hlarge
  exact ⟨x, y, hfar, fun i ↦ congrFun hxy i⟩

/-- A zero-start partial coloring fixes a fixed positive fraction of all coordinates. -/
theorem exists_partial_coloring {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (B : β → α → ℝ)
    (hB : ∀ i k, |B i k| ≤ 1) (hs : 0 < Fintype.card α)
    (hsR : Fintype.card α ≤ Fintype.card β) :
    ∃ z : α → ℝ, (∀ k, z k = -1 ∨ z k = 0 ∨ z k = 1) ∧
      (Fintype.card α : ℝ) / 16 ≤ ((Finset.univ.filter fun k ↦ z k ≠ 0).card : ℝ) ∧
      ∀ i, |∑ k, B i k * z k| ≤ 64 * Real.sqrt ((Fintype.card α : ℝ) *
        Real.log (16 * Fintype.card β / Fintype.card α)) := by
  classical
  let s : ℝ := Fintype.card α
  let L := Real.log (16 * Fintype.card β / s)
  have hs0 : 0 < s := by dsimp [s]; exact_mod_cast hs
  have hsR' : s ≤ (Fintype.card β : ℝ) := by dsimp [s]; exact_mod_cast hsR
  have hL := (entropy_log_parameters hs0 hsR').1
  change 1 / 2 ≤ L at hL
  have hL0 : 0 < L := by linarith
  by_cases hn : 32 ≤ Fintype.card α
  · obtain ⟨x, y, hfar, heq⟩ := exists_signings_same_round B hB hn hsR
    let z : α → ℝ := fun k ↦ (boolSign (x k) - boolSign (y k)) / 2
    let d := 64 * Real.sqrt (s * L)
    have hd : 0 < d := by dsimp [d]; positivity
    have hz (k : α) : z k = -1 ∨ z k = 0 ∨ z k = 1 := by
      dsimp [z]
      cases x k <;> cases y k <;> norm_num [boolSign]
    have hcard : (Finset.univ.filter fun k ↦ z k ≠ 0).card = hammingDist x y := by
      unfold hammingDist
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [z]
      cases x k <;> cases y k <;> norm_num [boolSign]
    refine ⟨z, hz, ?_, ?_⟩
    · rw [hcard]
      exact hfar.le
    · intro i
      let u := ∑ k, B i k * boolSign (x k)
      let v := ∑ k, B i k * boolSign (y k)
      have hq : round (u / d) = round (v / d) := heq i
      have hdiff : |u / d - v / d| ≤ 1 := by
        calc
          _ = |(u / d - (round (u / d) : ℝ)) + ((round (u / d) : ℝ) - v / d)| := by
            congr 1
            ring
          _ ≤ |u / d - (round (u / d) : ℝ)| + |(round (u / d) : ℝ) - v / d| := abs_add_le _ _
          _ ≤ 1 := by
            rw [hq, abs_sub_comm (round (v / d) : ℝ)]
            have hu := abs_sub_round (u / d)
            rw [hq] at hu
            linarith [abs_sub_round (v / d)]
      have huv : |u - v| ≤ d := by
        rw [← sub_div, abs_div, abs_of_pos hd] at hdiff
        have := (div_le_iff₀ hd).mp hdiff
        linarith
      change _ ≤ d
      calc
        _ = |(u - v) / 2| := by
          congr 1
          dsimp [u, v, z]
          simp only [← mul_div_assoc, mul_sub]
          rw [← Finset.sum_div, Finset.sum_sub_distrib]
        _ = |u - v| / 2 := by rw [abs_div]; norm_num
        _ ≤ d / 2 := by gcongr
        _ ≤ d := by linarith
  · refine ⟨fun _ ↦ 1, fun _ ↦ Or.inr (Or.inr rfl), ?_, ?_⟩
    · simp only [ne_eq, one_ne_zero, not_false_eq_true, Finset.filter_true,
        Finset.card_univ]
      nlinarith [(Nat.cast_nonneg (Fintype.card α) : (0 : ℝ) ≤ Fintype.card α)]
    · intro i
      have hsum : |∑ k, B i k * (1 : ℝ)| ≤ s := by
        calc
          _ ≤ ∑ k, |B i k * (1 : ℝ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _k : α, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ by simpa using hB i k
          _ = s := by simp [s]
      apply hsum.trans
      change s ≤ 64 * Real.sqrt (s * L)
      have hs32 : s ≤ 32 := by dsimp [s]; exact_mod_cast (by omega : Fintype.card α ≤ 32)
      have hq : (Real.sqrt (s * L)) ^ 2 = s * L := Real.sq_sqrt (by positivity)
      have hp := Real.sqrt_nonneg (s * L)
      nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hs32), mul_le_mul_of_nonneg_left hL hs0.le]

/-- The logarithmic discrepancy potential contracts on shortening the remaining columns. -/
theorem discrepancy_potential_contract {s u R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hu0 : 0 ≤ u) (hu : u ≤ (15 / 16) * s) :
    Real.sqrt (u * Real.log (16 * R / u)) ≤
      (63 / 64) * Real.sqrt (s * Real.log (16 * R / s)) := by
  by_cases hu_eq : u = 0
  · rw [hu_eq]
    simp only [zero_mul, Real.sqrt_zero]
    positivity
  have hu_pos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu_eq)
  have hR : 0 < R := hs.trans_le hsR
  let L := Real.log (16 * R / s)
  have hratio : (16 : ℝ) ≤ 16 * R / s := (le_div_iff₀ hs).mpr (by nlinarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hL : 2 ≤ L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hratio
    rw [hlog16] at hh
    change _ ≤ L at hh
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log (16 * R / u) = L + Real.log (s / u) := by
    have hid : 16 * R / u = (16 * R / s) * (s / u) := by field_simp
    rw [hid, Real.log_mul (by positivity : 16 * R / s ≠ 0) (by positivity : s / u ≠ 0)]
  have hsmall : u * Real.log (s / u) ≤ s - u := by
    calc
      _ ≤ u * (s / u - 1) := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (by positivity)) hu0
      _ = _ := by field_simp
  have hsq : u * Real.log (16 * R / u) ≤ (31 / 32) * (s * L) := by
    rw [hlog, mul_add]
    have hprod := mul_le_mul_of_nonneg_right hu (show 0 ≤ L - 1 by linarith)
    have hLs := mul_le_mul_of_nonneg_left hL hs.le
    nlinarith
  apply (Real.sqrt_le_left (by positivity : 0 ≤ (63 / 64) * Real.sqrt (s * L))).mpr
  have hsqrt := Real.sq_sqrt (mul_nonneg hs.le hL0)
  change u * Real.log (16 * R / u) ≤ ((63 / 64) * Real.sqrt (s * L)) ^ 2
  nlinarith [mul_nonneg hs.le hL0]

/-- Iterating the zero-start partial coloring proves the square-root logarithmic matrix bound. -/
theorem matrix_signing_raw (n : ℕ) :
    ∀ {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
      [Fintype β] [DecidableEq β], Fintype.card α = n →
      ∀ B : β → α → ℝ, (∀ i k, |B i k| ≤ 1) → Fintype.card α ≤ Fintype.card β →
      ∃ ξ : α → ℝ, (∀ k, ξ k = -1 ∨ ξ k = 1) ∧
        ∀ i, |∑ k, B i k * ξ k| ≤ 4096 * Real.sqrt ((Fintype.card α : ℝ) *
          Real.log (16 * Fintype.card β / Fintype.card α)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α β _ _ _ _ hn B hB hsR
    by_cases hn0 : n = 0
    · have hc : Fintype.card α = 0 := hn.trans hn0
      let : IsEmpty α := Fintype.card_eq_zero_iff.mp hc
      refine ⟨fun _ ↦ 1, fun _ ↦ Or.inr rfl, ?_⟩
      intro i
      simp
    have hs : 0 < Fintype.card α := by omega
    have hs0 : (0 : ℝ) < Fintype.card α := by exact_mod_cast hs
    obtain ⟨z, hz, hfix, herr⟩ := exists_partial_coloring B hB hs hsR
    let U := {k : α // z k = 0}
    have hpartitionNat : Fintype.card U + (Finset.univ.filter fun k ↦ z k ≠ 0).card =
        Fintype.card α := by
      dsimp [U]
      rw [Fintype.card_subtype]
      exact Finset.card_filter_add_card_filter_not _
    have hpartition : (Fintype.card U : ℝ) +
        ((Finset.univ.filter fun k ↦ z k ≠ 0).card : ℝ) = Fintype.card α := by
      exact_mod_cast hpartitionNat
    have hUbound : (Fintype.card U : ℝ) ≤ (15 / 16) * Fintype.card α := by linarith
    have hUlt : Fintype.card U < n := by
      have hh : (Fintype.card U : ℝ) < Fintype.card α := by nlinarith
      have hh' : Fintype.card U < Fintype.card α := by exact_mod_cast hh
      omega
    have hUR : Fintype.card U ≤ Fintype.card β := by
      exact (Fintype.card_subtype_le (fun k ↦ z k = 0)).trans hsR
    obtain ⟨ξ, hξ, hξerr⟩ := ih (Fintype.card U) hUlt (α := U) (β := β) rfl
      (fun i k ↦ B i k) (fun i k ↦ hB i k) hUR
    let w : α → ℝ := fun k ↦ if hk : z k = 0 then ξ ⟨k, hk⟩ else z k
    have hw (k : α) : w k = -1 ∨ w k = 1 := by
      by_cases hk : z k = 0
      · simpa only [w, dite_eq_left hk] using hξ ⟨k, hk⟩
      · simp only [w, dite_eq_right hk]
        rcases hz k with hm | hzero | hp
        · exact Or.inl hm
        · exact (hk hzero).elim
        · exact Or.inr hp
    have hsum (i : β) : (∑ k, B i k * w k) = (∑ k, B i k * z k) +
        ∑ k : U, B i k * ξ k := by
      have hpart (f : α → ℝ) : (∑ k, f k) =
          (∑ k : U, f k) + ∑ k : {k : α // z k ≠ 0}, f k :=
        (Fintype.sum_subtype_add_sum_subtype (fun k ↦ z k = 0) f).symm
      rw [hpart (fun k ↦ B i k * w k), hpart (fun k ↦ B i k * z k)]
      have hzero : (∑ k : U, B i k * z k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [k.property, mul_zero]
      have hwU : (∑ k : U, B i k * w k) = ∑ k : U, B i k * ξ k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [w, k.property]
      have hwc : (∑ k : {k : α // z k ≠ 0}, B i k * w k) =
          ∑ k : {k : α // z k ≠ 0}, B i k * z k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [w, k.property]
      rw [hzero, zero_add, hwU, hwc, add_comm]
    refine ⟨w, hw, fun i ↦ ?_⟩
    let P := Real.sqrt ((Fintype.card α : ℝ) *
      Real.log (16 * Fintype.card β / Fintype.card α))
    have hcontract := discrepancy_potential_contract hs0
      (show (Fintype.card α : ℝ) ≤ Fintype.card β by exact_mod_cast hsR)
      (Nat.cast_nonneg (Fintype.card U)) hUbound
    change _ ≤ (63 / 64) * P at hcontract
    rw [hsum]
    calc
      _ ≤ |∑ k, B i k * z k| + |∑ k : U, B i k * ξ k| := abs_add_le _ _
      _ ≤ 64 * P + 4096 * Real.sqrt ((Fintype.card U : ℝ) *
          Real.log (16 * Fintype.card β / Fintype.card U)) := add_le_add (herr i) (hξerr i)
      _ ≤ 64 * P + 4096 * ((63 / 64) * P) := by gcongr
      _ = _ := by change _ = 4096 * P; ring

theorem matrix_signing {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (B : β → α → ℝ)
    (hB : ∀ i k, |B i k| ≤ 1) (hsR : Fintype.card α ≤ Fintype.card β) :
    ∃ ξ : α → ℝ, (∀ k, ξ k = -1 ∨ ξ k = 1) ∧
      ∀ i, |∑ k, B i k * ξ k| ≤ 8192 * Real.sqrt ((Fintype.card α : ℝ) *
        Real.log (2 * Fintype.card β / Fintype.card α)) := by
  obtain ⟨ξ, hξ, herr⟩ := matrix_signing_raw (Fintype.card α) rfl B hB hsR
  refine ⟨ξ, hξ, fun i ↦ (herr i).trans ?_⟩
  by_cases hs : Fintype.card α = 0
  · simp [hs]
  have hs0 : (0 : ℝ) < Fintype.card α := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hR0 : (0 : ℝ) < Fintype.card β := hs0.trans_le (by exact_mod_cast hsR)
  let x : ℝ := Fintype.card β / Fintype.card α
  have hx : 1 ≤ x := (le_div_iff₀ hs0).mpr (by simpa using (show (Fintype.card α : ℝ) ≤ Fintype.card β by exact_mod_cast hsR))
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h16 : Real.log (16 * x) ≤ 4 * Real.log (2 * x) := by
    rw [Real.log_mul (by norm_num) hx0.ne', Real.log_mul (by norm_num) hx0.ne',
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlog2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hsq : Real.sqrt ((Fintype.card α : ℝ) * Real.log (16 * x)) ≤
      2 * Real.sqrt ((Fintype.card α : ℝ) * Real.log (2 * x)) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hh := Real.sq_sqrt (mul_nonneg hs0.le hlog2x)
    nlinarith [mul_le_mul_of_nonneg_left h16 hs0.le]
  dsimp [x] at hsq
  simp only [← mul_div_assoc] at hsq
  nlinarith

/-- Reversing a signing preserves discrepancy and allows its total sum to be nonpositive. -/
theorem matrix_signing_nonpos {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (B : β → α → ℝ) (hB : ∀ i k, |B i k| ≤ 1)
    (hsR : Fintype.card α ≤ Fintype.card β) :
    ∃ ξ : α → ℝ, (∀ k, ξ k = -1 ∨ ξ k = 1) ∧ (∑ k, ξ k) ≤ 0 ∧
      ∀ i, |∑ k, B i k * ξ k| ≤ 8192 * Real.sqrt ((Fintype.card α : ℝ) *
        Real.log (2 * Fintype.card β / Fintype.card α)) := by
  obtain ⟨ξ, hξ, herr⟩ := matrix_signing B hB hsR
  by_cases hsum : (∑ k, ξ k) ≤ 0
  · exact ⟨ξ, hξ, hsum, herr⟩
  refine ⟨fun k ↦ -ξ k, ?_, ?_, ?_⟩
  · intro k
    rcases hξ k with hk | hk <;> simp [hk]
  · rw [Finset.sum_neg_distrib]
    linarith
  · intro i
    simpa only [mul_neg, Finset.sum_neg_distrib, abs_neg] using herr i

/-- The small mass controls the discrepancy potential at every dyadic scale. -/
theorem dyadic_potential_bound {s μ R : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ R)
    (hs : 0 ≤ s) (j : ℕ) (hsmass : s ≤ 2 ^ j * μ) :
    Real.sqrt (s * Real.log (2 * R / s)) / 2 ^ j ≤
      (3 / 4) ^ j * Real.sqrt (μ * Real.log (2 * R / μ)) := by
  have hR : 0 < R := by linarith
  have hratio : (4 : ℝ) ≤ 2 * R / μ := (le_div_iff₀ hμ).mpr (by linarith)
  let L := Real.log (2 * R / μ)
  have hL : 1 ≤ L := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have h4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hratio
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h4
    norm_num at h2 h4
    dsimp [L]
    linarith
  have hφ : 0 ≤ μ * L := mul_nonneg hμ.le (by linarith)
  have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hf : s * Real.log (2 * R / s) ≤ 2 ^ j * (μ * L) := by
    by_cases hz : s = 0
    · rw [hz, zero_mul]
      positivity
    have hs0 : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    have hid : 2 * R / s = (2 * R / μ) * (μ / s) := by field_simp
    rw [hid, Real.log_mul (by positivity : 2 * R / μ ≠ 0)
      (by positivity : μ / s ≠ 0), mul_add]
    have hlog := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (show 0 < μ / s by positivity)) hs
    have heq : s * (μ / s - 1) = μ - s := by field_simp
    rw [heq] at hlog
    have hmult := mul_le_mul_of_nonneg_right hsmass (show 0 ≤ L - 1 by linarith)
    change s * L + s * Real.log (μ / s) ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hpow hμ.le]
  have hscale : (2 : ℝ) ^ j ≤ ((3 / 4) ^ j * 2 ^ j) ^ 2 := by
    calc
      (2 : ℝ) ^ j ≤ (9 / 4) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
      _ = _ := by rw [← mul_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).mpr
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hroot := Real.sq_sqrt hφ
  change s * Real.log (2 * R / s) ≤ ((3 / 4) ^ j * Real.sqrt (μ * L) * 2 ^ j) ^ 2
  calc
    _ ≤ 2 ^ j * (μ * L) := hf
    _ ≤ (((3 / 4) ^ j * 2 ^ j) ^ 2) * (μ * L) := mul_le_mul_of_nonneg_right hscale hφ
    _ = _ := by calc
      _ = ((3 / 4) ^ j * 2 ^ j) ^ 2 * (Real.sqrt (μ * L)) ^ 2 := by rw [hroot]
      _ = _ := by ring

/-- One mass-nonincreasing dyadic rounding step, on the exact odd coordinates. -/
theorem dyadic_round_step {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : β → α → ℝ) (hA : ∀ i k, |A i k| ≤ 1)
    (hαβ : Fintype.card α ≤ Fintype.card β)
    (a : α → ℕ) (j : ℕ) (ha : ∀ k, a k ≤ 2 ^ (j + 1))
    {μ : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ Fintype.card β)
    (hmass : (∑ k, (a k : ℝ) / 2 ^ (j + 1)) ≤ μ) :
    ∃ b : α → ℕ, (∀ k, b k ≤ 2 ^ j) ∧
      (∑ k, (b k : ℝ) / 2 ^ j) ≤ (∑ k, (a k : ℝ) / 2 ^ (j + 1)) ∧
      ∀ i, |∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1))| ≤
        8192 * ((3 / 4) ^ (j + 1) * Real.sqrt
          (μ * Real.log (2 * Fintype.card β / μ))) := by
  classical
  let U := {k : α // a k % 2 = 1}
  have hUβ : Fintype.card U ≤ Fintype.card β :=
    (Fintype.card_subtype_le _).trans hαβ
  obtain ⟨ξ, hξ, hξsum, hξerr⟩ := matrix_signing_nonpos
    (fun i (k : U) ↦ A i k) (fun i k ↦ hA i k) hUβ
  let b : α → ℕ := fun k ↦ a k / 2 +
    if hk : a k % 2 = 1 then (if ξ ⟨k, hk⟩ = 1 then 1 else 0) else 0
  let ζ : α → ℝ := fun k ↦ if hk : a k % 2 = 1 then ξ ⟨k, hk⟩ else 0
  have hb (k : α) : b k ≤ 2 ^ j := by
    have hak := ha k
    rw [pow_succ] at hak
    dsimp [b]
    by_cases hk : a k % 2 = 1
    · rw [dite_eq_left hk]
      split_ifs <;> omega
    · rw [dite_eq_right hk]
      omega
  have hnumer (k : α) : 2 * (b k : ℝ) - a k = ζ k := by
    by_cases hk : a k % 2 = 1
    · dsimp [b, ζ]
      rw [dite_eq_left hk, dite_eq_left hk]
      rcases hξ ⟨k, hk⟩ with hm | hp
      · rw [hm]
        norm_num
        have hn : 2 * (a k / 2) + 1 = a k := by omega
        have hn' : 2 * ((a k / 2 : ℕ) : ℝ) + 1 = a k := by exact_mod_cast hn
        linarith
      · rw [hp]
        norm_num

        have hn : 2 * (a k / 2) + 1 = a k := by omega
        have hn' : 2 * ((a k / 2 : ℕ) : ℝ) + 1 = a k := by exact_mod_cast hn
        linarith
    · dsimp [b, ζ]
      rw [dite_eq_right hk, dite_eq_right hk]
      norm_num
      have hn : 2 * (a k / 2) = a k := by omega
      have hn' : 2 * ((a k / 2 : ℕ) : ℝ) = a k := by exact_mod_cast hn
      linarith
  have hdiff (k : α) : (b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1) =
      ζ k / 2 ^ (j + 1) := by
    rw [pow_succ]
    have hp : (2 : ℝ) ^ j ≠ 0 := by positivity
    field_simp
    nlinarith [hnumer k]
  have hζsum (f : α → ℝ) : (∑ k, f k * ζ k) = ∑ k : U, f k * ξ k := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k ↦ a k % 2 = 1)]
    have hzero : (∑ k : {k : α // ¬ a k % 2 = 1}, f k * ζ k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [ζ, k.property]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    simp [ζ, k.property]
  have hmass' : (∑ k, (b k : ℝ) / 2 ^ j) ≤ ∑ k, (a k : ℝ) / 2 ^ (j + 1) := by
    have hsumdiff : (∑ k, (b k : ℝ) / 2 ^ j) - (∑ k, (a k : ℝ) / 2 ^ (j + 1)) =
        (∑ k : U, ξ k) / 2 ^ (j + 1) := by
      rw [← Finset.sum_sub_distrib]
      simp_rw [hdiff]
      rw [← Finset.sum_div]
      congr 1
      simpa using hζsum (fun _ ↦ 1)
    have hh : (∑ k : U, ξ k) / 2 ^ (j + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hξsum (by positivity)
    linarith
  have hsmass : (Fintype.card U : ℝ) ≤ 2 ^ (j + 1) * μ := by
    have hsumU : (Fintype.card U : ℝ) ≤ ∑ k : U, (a k : ℝ) := by
      calc
        _ = ∑ _k : U, (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun k _ ↦ by
          have hk : 1 ≤ a k := by have := k.property; omega
          exact_mod_cast hk
    have hsumall : (∑ k : U, (a k : ℝ)) ≤ ∑ k : α, (a k : ℝ) := by
      have hh := Fintype.sum_subtype_add_sum_subtype (fun k ↦ a k % 2 = 1) (fun k ↦ (a k : ℝ))
      have hp : 0 ≤ ∑ k : {k : α // ¬ a k % 2 = 1}, (a k : ℝ) := by positivity
      change (∑ k : U, (a k : ℝ)) + _ = _ at hh
      linarith
    rw [← Finset.sum_div] at hmass
    have hm := (div_le_iff₀ (show (0 : ℝ) < 2 ^ (j + 1) by positivity)).mp hmass
    linarith
  refine ⟨b, hb, hmass', fun i ↦ ?_⟩
  have hsum : (∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1))) =
      (∑ k : U, A i k * ξ k) / 2 ^ (j + 1) := by
    simp_rw [hdiff, ← mul_div_assoc]
    rw [← Finset.sum_div, hζsum]
  rw [hsum, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (j + 1))]
  calc
    _ ≤ (8192 * Real.sqrt ((Fintype.card U : ℝ) *
        Real.log (2 * Fintype.card β / Fintype.card U))) / 2 ^ (j + 1) :=
      div_le_div_of_nonneg_right (hξerr i) (by positivity)
    _ = 8192 * (Real.sqrt ((Fintype.card U : ℝ) *
        Real.log (2 * Fintype.card β / Fintype.card U)) / 2 ^ (j + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dyadic_potential_bound hμ hμR (Nat.cast_nonneg _) (j + 1) hsmass) (by norm_num)

/-- Iteration of the dyadic steps. The mass bound is maintained, not reset at each scale. -/
theorem dyadic_round {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : β → α → ℝ) (hA : ∀ i k, |A i k| ≤ 1)
    (hαβ : Fintype.card α ≤ Fintype.card β)
    {μ : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ Fintype.card β) (j : ℕ) :
    ∀ a : α → ℕ, (∀ k, a k ≤ 2 ^ j) →
      (∑ k, (a k : ℝ) / 2 ^ j) ≤ μ →
      ∃ b : α → ℕ, (∀ k, b k ≤ 1) ∧
        (∑ k, (b k : ℝ)) ≤ (∑ k, (a k : ℝ) / 2 ^ j) ∧
        ∀ i, |∑ k, A i k * ((b k : ℝ) - (a k : ℝ) / 2 ^ j)| ≤
          8192 * (3 * (1 - (3 / 4) ^ j) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) := by
  induction j with
  | zero =>
    intro a ha hmass
    refine ⟨a, by simpa using ha, by simp, ?_⟩
    intro i
    simp
  | succ j ih =>
    intro a ha hmass
    obtain ⟨b, hb, hmassb, herrb⟩ := dyadic_round_step A hA hαβ a j ha hμ hμR hmass
    obtain ⟨c, hc, hmassc, herrc⟩ := ih b hb (hmassb.trans hmass)
    refine ⟨c, hc, hmassc.trans hmassb, fun i ↦ ?_⟩
    have hsplit : (∑ k, A i k * ((c k : ℝ) - (a k : ℝ) / 2 ^ (j + 1))) =
        (∑ k, A i k * ((c k : ℝ) - (b k : ℝ) / 2 ^ j)) +
        ∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hsplit]
    calc
      _ ≤ |∑ k, A i k * ((c k : ℝ) - (b k : ℝ) / 2 ^ j)| +
          |∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1))| := abs_add_le _ _
      _ ≤ 8192 * (3 * (1 - (3 / 4) ^ j) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) +
          8192 * ((3 / 4) ^ (j + 1) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) := add_le_add (herrc i) (herrb i)
      _ = _ := by rw [pow_succ]; ring

/-- Defect-sensitive rounding on a real matrix, prior to the circle discretization. -/
theorem matrix_defect_rounding {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : β → α → ℝ) (hA : ∀ i k, |A i k| ≤ 1)
    (hαβ : Fintype.card α ≤ Fintype.card β)
    (p : α → ℝ) (hp : ∀ k, 0 ≤ p k ∧ p k ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ Fintype.card β)
    (hmass : (∑ k, p k) ≤ μ) :
    ∃ p' : α → ℝ, (∀ k, p' k = 0 ∨ p' k = 1) ∧ (∑ k, p' k) ≤ ∑ k, p k ∧
      ∀ i, |∑ k, A i k * (p' k - p k)| ≤
        1 + 24576 * Real.sqrt (μ * Real.log (2 * Fintype.card β / μ)) := by
  classical
  let j := Fintype.card α
  have hjNat : j ≤ 2 ^ j := by
    have hh : ∀ n : ℕ, n ≤ 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hp : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
        rw [pow_succ]
        omega
    exact hh j
  have hj : (Fintype.card α : ℝ) / 2 ^ j ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).mpr
    simp only [one_mul]
    exact_mod_cast hjNat
  let a : α → ℕ := fun k ↦ ⌊2 ^ j * p k⌋₊
  have ha_le (k : α) : (a k : ℝ) ≤ 2 ^ j * p k := Nat.floor_le (mul_nonneg (by positivity) (hp k).1)
  have ha_lt (k : α) : 2 ^ j * p k < (a k : ℝ) + 1 := Nat.lt_floor_add_one _
  have habound (k : α) : a k ≤ 2 ^ j := by
    have hh : (a k : ℝ) ≤ (2 : ℝ) ^ j := (ha_le k).trans
      (by nlinarith [hp k, show (0 : ℝ) ≤ 2 ^ j by positivity])
    exact_mod_cast hh
  have ha_frac (k : α) : (a k : ℝ) / 2 ^ j ≤ p k :=
    (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using ha_le k)
  have ha_err (k : α) : |(a k : ℝ) / 2 ^ j - p k| ≤ 1 / 2 ^ j := by
    rw [abs_of_nonpos (sub_nonpos.mpr (ha_frac k))]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).mpr
    have heq : -((a k : ℝ) / 2 ^ j - p k) * 2 ^ j = 2 ^ j * p k - a k := by
      field_simp ; ring
    rw [heq]
    linarith [ha_lt k]
  have hmass_a : (∑ k, (a k : ℝ) / 2 ^ j) ≤ ∑ k, p k :=
    Finset.sum_le_sum fun k _ ↦ ha_frac k
  have hinit (i : β) : |∑ k, A i k * ((a k : ℝ) / 2 ^ j - p k)| ≤ 1 := by
    calc
      _ ≤ ∑ k, |A i k * ((a k : ℝ) / 2 ^ j - p k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : α, (1 : ℝ) / 2 ^ j := Finset.sum_le_sum fun k _ ↦ by
        rw [abs_mul]
        exact (mul_le_mul (hA i k) (ha_err k) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = (Fintype.card α : ℝ) / 2 ^ j := by simp [div_eq_mul_inv]
      _ ≤ 1 := hj
  obtain ⟨b, hb, hmassb, herrb⟩ := dyadic_round A hA hαβ hμ hμR j a habound
    (hmass_a.trans hmass)
  refine ⟨fun k ↦ (b k : ℝ), ?_, hmassb.trans hmass_a, fun i ↦ ?_⟩
  · intro k
    have hh : b k = 0 ∨ b k = 1 := by have := hb k; omega
    rcases hh with hh | hh <;> simp [hh]
  · have hsplit : (∑ k, A i k * ((b k : ℝ) - p k)) =
        (∑ k, A i k * ((b k : ℝ) - (a k : ℝ) / 2 ^ j)) +
        ∑ k, A i k * ((a k : ℝ) / 2 ^ j - p k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hsplit]
    have hroot := Real.sqrt_nonneg (μ * Real.log (2 * Fintype.card β / μ))
    calc
      _ ≤ |∑ k, A i k * ((b k : ℝ) - (a k : ℝ) / 2 ^ j)| +
          |∑ k, A i k * ((a k : ℝ) / 2 ^ j - p k)| := abs_add_le _ _
      _ ≤ 8192 * (3 * (1 - (3 / 4) ^ j) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) + 1 := add_le_add (herrb i) (hinit i)
      _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) j) hroot]

open scoped ComplexConjugate
open Finset

/-- Orthogonality of the exact full root-of-unity grid. -/
theorem grid_power_orthogonality {M a b : ℕ} [NeZero M] (ha : a < M) (hb : b < M) :
    (∑ j : ZMod M, ZMod.stdAddChar j ^ a * conj (ZMod.stdAddChar j ^ b)) =
      if a = b then (M : ℂ) else 0 := by
  have hpow (n : ℕ) (j : ZMod M) : ZMod.stdAddChar j ^ n =
      ZMod.stdAddChar ((n : ZMod M) * j) := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hconj (j : ZMod M) : conj (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
    rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]
    exact (Circle.coe_inv_eq_conj (ZMod.toCircle j)).symm
  simp_rw [hpow, hconj, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul]
  have hzero : ((a : ZMod M) - b = 0) ↔ a = b := by
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff]
    simp only [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases hab : a = b
  · subst b
    simp
  · rw [ite_eq_right hab]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M (mt hzero.mp hab))

/-- Mean square of a translated Dirichlet kernel on an oversampling grid. -/
theorem grid_dirichlet_square {M n : ℕ} [NeZero M] (hn : n ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ j : ZMod M, ‖∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))‖ ^ 2) =
      (M : ℝ) * n := by
  have hcomplex : (∑ j : ZMod M,
      (∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))) *
      conj (∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ)))) =
      (M : ℂ) * n := by
    simp only [map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Eq.trans ?_ (show (∑ a : Fin n, (M : ℂ)) = (M : ℂ) * n by simp [mul_comm])
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]
    calc
      (∑ b : Fin n, ∑ j : ZMod M,
          z ^ (b : ℕ) * conj (ZMod.stdAddChar j ^ (b : ℕ)) *
            (conj (z ^ (a : ℕ)) * ZMod.stdAddChar j ^ (a : ℕ))) =
        ∑ b : Fin n, (z ^ (b : ℕ) * conj (z ^ (a : ℕ))) *
          (∑ j : ZMod M, ZMod.stdAddChar j ^ (a : ℕ) *
            conj (ZMod.stdAddChar j ^ (b : ℕ))) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ = ∑ b : Fin n, if b = a then (z ^ (a : ℕ) * conj (z ^ (a : ℕ))) * M else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [grid_power_orthogonality (a.isLt.trans_le hn) (b.isLt.trans_le hn)]
        by_cases heq : b = a
        · subst b
          simp
        · have hval : (b : ℕ) ≠ (a : ℕ) := fun h ↦ heq (Fin.ext h)
          simp [heq, Ne.symm hval]
      _ = (M : ℂ) := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hz]
        simp
  have hreal := congrArg Complex.re hcomplex
  simpa only [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, Complex.ofReal_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] using hreal

/-- A rotated, finite Dirichlet kernel on the root grid. -/
def gridDirichlet {M : ℕ} [NeZero M] (n : ℕ) (z : ℂ) (j : ZMod M) : ℂ :=
  ∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))

/-- The cross-Dirichlet kernel reproduces each required nonnegative frequency. -/
theorem grid_reproduce_monomial {M N : ℕ} [NeZero M] (hNM : 2 * N ≤ M)
    (k : Fin N) {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ j : ZMod M, ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
      conj (gridDirichlet N z j)) = (M : ℂ) * N * z ^ (k : ℕ) := by
  have hb (b : Fin N) : (∑ j : ZMod M,
      ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
        (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ))) =
      (M : ℂ) * z ^ (k : ℕ) := by
    have hkb : (k : ℕ) + b < 2 * N := by omega
    let a₀ : Fin (2 * N) := ⟨(k : ℕ) + b, hkb⟩
    simp only [gridDirichlet, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      (∑ a : Fin (2 * N), ∑ j : ZMod M,
          ZMod.stdAddChar j ^ (k : ℕ) *
            (z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))) *
              (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ))) =
        ∑ a : Fin (2 * N), (z ^ (a : ℕ) * conj (z ^ (b : ℕ))) *
          (∑ j : ZMod M, ZMod.stdAddChar j ^ ((k : ℕ) + b) *
            conj (ZMod.stdAddChar j ^ (a : ℕ))) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_add]
        ring
      _ = ∑ a : Fin (2 * N), if a = a₀ then
          (z ^ ((k : ℕ) + b) * conj (z ^ (b : ℕ))) * M else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [grid_power_orthogonality (hkb.trans_le hNM) (a.isLt.trans_le hNM)]
        by_cases heq : a = a₀
        · subst a
          simp [a₀]
        · have hval : (k : ℕ) + b ≠ (a : ℕ) := fun h ↦ heq (Fin.ext h.symm)
          simp [heq, hval]
      _ = (M : ℂ) * z ^ (k : ℕ) := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [pow_add, mul_assoc (z ^ (k : ℕ)) (z ^ (b : ℕ)) (conj (z ^ (b : ℕ))),
          Complex.mul_conj, Complex.normSq_eq_norm_sq,
          norm_pow, hz]
        simp [mul_comm]
  calc
    _ = ∑ j : ZMod M, ∑ b : Fin N,
        ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
          (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [gridDirichlet, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
    _ = ∑ b : Fin N, ∑ j : ZMod M,
        ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
          (conj (z ^ (b : ℕ)) * ZMod.stdAddChar j ^ (b : ℕ)) := Finset.sum_comm
    _ = ∑ _b : Fin N, (M : ℂ) * z ^ (k : ℕ) := Finset.sum_congr rfl (fun b _ ↦ hb b)
    _ = _ := by simp; ring

/-- No logarithmic loss: an oversampled analytic polynomial is controlled on the whole circle. -/
theorem polynomial_grid_bound {N M : ℕ} [NeZero M] (hN : 0 < N) (hNM : 2 * N ≤ M)
    (c : Fin N → ℂ) {G : ℝ} (hG : 0 ≤ G)
    (hgrid : ∀ j : ZMod M, ‖∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)‖ ≤ G)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ ≤ 2 * G := by
  have hid : (M : ℂ) * N * (∑ k : Fin N, c k * z ^ (k : ℕ)) =
      ∑ j : ZMod M, (∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)) *
        gridDirichlet (2 * N) z j * conj (gridDirichlet N z j) := by
    rw [Finset.mul_sum]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = c k * ((M : ℂ) * N * z ^ (k : ℕ)) := by ring
      _ = c k * (∑ j : ZMod M, ZMod.stdAddChar j ^ (k : ℕ) *
          gridDirichlet (2 * N) z j * conj (gridDirichlet N z j)) := by
        rw [grid_reproduce_monomial hNM k hz]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have h2N := grid_dirichlet_square (n := 2 * N) hNM hz
  have hN' := grid_dirichlet_square (n := N) (by omega : N ≤ M) hz
  change (∑ j : ZMod M, ‖gridDirichlet (2 * N) z j‖ ^ 2) = _ at h2N
  change (∑ j : ZMod M, ‖gridDirichlet N z j‖ ^ 2) = _ at hN'
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod M))
    (fun j ↦ ‖gridDirichlet (2 * N) z j‖) (fun j ↦ ‖gridDirichlet N z j‖)
  rw [h2N, hN'] at hcs
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hkernel : (∑ j : ZMod M, ‖gridDirichlet (2 * N) z j‖ *
      ‖gridDirichlet N z j‖) ≤ 2 * M * N := by
    push_cast at hcs
    nlinarith [mul_pos hMpos hNpos]
  have hnorm : (M : ℝ) * N * ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ =
      ‖∑ j : ZMod M, (∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)) *
        gridDirichlet (2 * N) z j * conj (gridDirichlet N z j)‖ := by
    rw [← hid, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hbound : (M : ℝ) * N * ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ ≤
      G * (2 * M * N) := by
    rw [hnorm]
    calc
      _ ≤ ∑ j : ZMod M, ‖(∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)) *
          gridDirichlet (2 * N) z j * conj (gridDirichlet N z j)‖ := norm_sum_le _ _
      _ ≤ ∑ j : ZMod M, G * (‖gridDirichlet (2 * N) z j‖ *
          ‖gridDirichlet N z j‖) := Finset.sum_le_sum fun j _ ↦ by
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        nlinarith [mul_le_mul_of_nonneg_right (hgrid j)
          (mul_nonneg (norm_nonneg (gridDirichlet (2 * N) z j)) (norm_nonneg (gridDirichlet N z j)))]
      _ = G * (∑ j : ZMod M, ‖gridDirichlet (2 * N) z j‖ *
          ‖gridDirichlet N z j‖) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hkernel hG
  nlinarith [mul_pos hMpos hNpos]

def defectMass {N : ℕ} (X : Fin N → ℝ) : ℝ :=
  (∑ k : Fin N, (1 - |X k|)) / 2

theorem defect_rounding {N : ℕ} (hN : 1 ≤ N) (X : Fin N → ℝ)
    (hX : ∀ k, |X k| ≤ 1) :
    ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ‖littlewoodValue ε z - littlewoodValue X z‖ ≤
          196608 * (1 + Real.sqrt (defectMass X * Real.log (80 * N / defectMass X))) := by
  classical
  let μ := defectMass X
  have hμ0 : 0 ≤ μ := by
    dsimp [μ, defectMass]
    exact div_nonneg (Finset.sum_nonneg fun k _ ↦ sub_nonneg.mpr (hX k)) (by norm_num)
  have hμN : 2 * μ ≤ N := by
    have hh : (∑ k : Fin N, (1 - |X k|)) ≤ ∑ _k : Fin N, (1 : ℝ) :=
      Finset.sum_le_sum fun k _ ↦ by linarith [abs_nonneg (X k)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hh
    dsimp [μ, defectMass]
    linarith
  by_cases hμzero : μ = 0
  · have hsumzero : (∑ k : Fin N, (1 - |X k|)) = 0 := by dsimp [μ, defectMass] at hμzero; linarith
    have hxone (k : Fin N) : |X k| = 1 := by
      have hk := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ (Finset.univ : Finset (Fin N))) ↦ sub_nonneg.mpr (hX k))).mp hsumzero k (Finset.mem_univ k)
      linarith
    refine ⟨X, ?_, ?_⟩
    · intro k
      by_cases hk : 0 ≤ X k
      · exact Or.inr (by simpa only [abs_of_nonneg hk] using hxone k)
      · exact Or.inl (by have := hxone k; rw [abs_of_neg (lt_of_not_ge hk)] at this; linarith)
    · intro z hz
      rw [sub_self, norm_zero]
      positivity
  have hμ : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμzero)
  let σ : Fin N → ℝ := fun k ↦ if 0 ≤ X k then 1 else -1
  let p : Fin N → ℝ := fun k ↦ (1 - |X k|) / 2
  have hσ (k : Fin N) : σ k = -1 ∨ σ k = 1 := by dsimp [σ]; split_ifs <;> simp
  have hσabs (k : Fin N) : |σ k| = 1 := by rcases hσ k with hk | hk <;> simp [hk]
  have hp (k : Fin N) : 0 ≤ p k ∧ p k ≤ 1 := by
    dsimp [p]
    constructor <;> linarith [hX k, abs_nonneg (X k)]
  have hXp (k : Fin N) : σ k * (1 - 2 * p k) = X k := by
    dsimp [σ, p]
    split_ifs with hk
    · rw [abs_of_nonneg hk]
      ring
    · rw [abs_of_neg (lt_of_not_ge hk)]
      ring
  have hmass : (∑ k, p k) = μ := by dsimp [p, μ, defectMass]; rw [Finset.sum_div]
  let M := 20 * N
  have hM : M ≠ 0 := by dsimp [M]; omega
  let : NeZero M := ⟨hM⟩
  let A : (ZMod M × Bool) → Fin N → ℝ := fun i k ↦
    σ k * (if i.2 then (ZMod.stdAddChar i.1 ^ (k : ℕ)).im else (ZMod.stdAddChar i.1 ^ (k : ℕ)).re)
  have hrootnorm (j : ZMod M) : ‖ZMod.stdAddChar j‖ = 1 := Circle.norm_coe (ZMod.toCircle j)
  have hA (i : ZMod M × Bool) (k : Fin N) : |A i k| ≤ 1 := by
    dsimp [A]
    rw [abs_mul, hσabs, one_mul]
    split_ifs
    · calc
        _ ≤ ‖ZMod.stdAddChar i.1 ^ (k : ℕ)‖ := Complex.abs_im_le_norm _
        _ = 1 := by rw [norm_pow, hrootnorm]; simp
    · calc
        _ ≤ ‖ZMod.stdAddChar i.1 ^ (k : ℕ)‖ := Complex.abs_re_le_norm _
        _ = 1 := by rw [norm_pow, hrootnorm]; simp
  have hcard : Fintype.card (ZMod M × Bool) = 40 * N := by
    simp [Fintype.card_prod, ZMod.card, M]
    omega
  have hNR : Fintype.card (Fin N) ≤ Fintype.card (ZMod M × Bool) := by rw [hcard, Fintype.card_fin]; omega
  have hμR : 2 * μ ≤ Fintype.card (ZMod M × Bool) := by
    rw [hcard]
    push_cast
    nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  obtain ⟨p', hp', hmass', herr⟩ := matrix_defect_rounding A hA hNR p hp hμ hμR hmass.le
  let ε : Fin N → ℝ := fun k ↦ σ k * (1 - 2 * p' k)
  have hε : IsRealSigning ε := by
    intro k
    rcases hp' k with hp'k | hp'k <;> rcases hσ k with hσk | hσk <;> norm_num [IsRealSigning, ε, hp'k, hσk]
  let D := 1 + 24576 * Real.sqrt (μ * Real.log (80 * N / μ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have herr' (i : ZMod M × Bool) : |∑ k, A i k * (p' k - p k)| ≤ D := by
    have hh := herr i
    rw [hcard] at hh
    push_cast at hh
    convert hh using 1; dsimp [D]; congr 3; ring_nf
  let E : ZMod M → ℂ := fun j ↦ ∑ k, ((σ k * (p' k - p k) : ℝ) : ℂ) * ZMod.stdAddChar j ^ (k : ℕ)
  have hEre (j : ZMod M) : (E j).re = ∑ k, A (j, false) k * (p' k - p k) := by
    dsimp [E, A]
    simp only [Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hEim (j : ZMod M) : (E j).im = ∑ k, A (j, true) k * (p' k - p k) := by
    dsimp [E, A]
    simp only [Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hEnorm (j : ZMod M) : ‖E j‖ ≤ 2 * D := by
    calc
      _ ≤ |(E j).re| + |(E j).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ D + D := by rw [hEre, hEim]; exact add_le_add (herr' (j, false)) (herr' (j, true))
      _ = _ := by ring
  have hcoef (k : Fin N) : ε k - X k = -2 * (σ k * (p' k - p k)) := by
    have hh := hXp k
    dsimp [ε]
    nlinarith
  have hgrid (j : ZMod M) : ‖∑ k : Fin N, ((ε k - X k : ℝ) : ℂ) *
      ZMod.stdAddChar j ^ (k : ℕ)‖ ≤ 4 * D := by
    have heq : (∑ k : Fin N, ((ε k - X k : ℝ) : ℂ) * ZMod.stdAddChar j ^ (k : ℕ)) =
        (-2 : ℂ) * E j := by
      dsimp [E]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcoef]
      push_cast
      ring
    rw [heq, norm_mul]
    norm_num
    nlinarith [hEnorm j]
  refine ⟨ε, hε, fun z hz ↦ ?_⟩
  have hpoly := polynomial_grid_bound (M := M) (by omega : 0 < N)
    (by dsimp [M]; omega : 2 * N ≤ M) (fun k ↦ ((ε k - X k : ℝ) : ℂ))
    (show 0 ≤ 4 * D by positivity) hgrid hz
  have heq : littlewoodValue ε z - littlewoodValue X z =
      ∑ k : Fin N, ((ε k - X k : ℝ) : ℂ) * z ^ (k : ℕ) := by
    dsimp [littlewoodValue]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    ring
  rw [heq]
  apply hpoly.trans
  dsimp [D, μ]
  nlinarith [Real.sqrt_nonneg (defectMass X * Real.log (80 * N / defectMass X))]

end

end AsymptoticallyMinimalLittlewood

end OAI
