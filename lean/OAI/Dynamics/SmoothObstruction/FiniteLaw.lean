import Mathlib

namespace OAI

section

open Finset

namespace SmoothObstruction.FiniteLaw

variable (A : Type*) [Fintype A]

structure Law where
  mass : A → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

variable {A}

noncomputable def expect (P : Law A) (f : A → ℝ) : ℝ := ∑ a, P.mass a * f a

lemma expect_nonneg (P : Law A) {f : A → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ expect P f := sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (hf a))

lemma expect_mono (P : Law A) {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    expect P f ≤ expect P g := sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (P.nonneg a))

@[simp] lemma expect_const (P : Law A) (c : ℝ) : expect P (fun _ => c) = c := by
  simp [expect, ← sum_mul, P.total]

lemma expect_add (P : Law A) (f g : A → ℝ) :
    expect P (fun a => f a + g a) = expect P f + expect P g := by
  simp only [expect, mul_add, sum_add_distrib]

lemma expect_sub (P : Law A) (f g : A → ℝ) :
    expect P (fun a => f a - g a) = expect P f - expect P g := by
  simp only [expect, mul_sub, sum_sub_distrib]

lemma expect_mul_const (P : Law A) (f : A → ℝ) (c : ℝ) :
    expect P (fun a => f a * c) = expect P f * c := by
  simp only [expect, ← mul_assoc, sum_mul]

lemma expect_const_mul (P : Law A) (c : ℝ) (f : A → ℝ) :
    expect P (fun a => c * f a) = c * expect P f := by
  simpa only [mul_comm] using expect_mul_const P f c

lemma expect_sum {I : Type*} [Fintype I] (P : Law A) (f : I → A → ℝ) :
    expect P (fun a => ∑ i, f i a) = ∑ i, expect P (f i) := by
  simp only [expect, mul_sum]
  exact sum_comm

lemma expect_sq_abs (P : Law A) (f : A → ℝ) :
    (expect P (fun a => |f a|)) ^ 2 ≤ expect P (fun a => f a ^ 2) := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (f := P.mass) (g := fun a => P.mass a * f a ^ 2)
    (r := fun a => P.mass a * |f a|)
    (fun a _ => P.nonneg a) (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
    (fun a _ => by rw [mul_pow, sq_abs]; ring_nf; exact le_rfl)
  simpa only [P.total, one_mul, expect] using h

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def product (P : I → Law A) : Law (I → A) where
  mass x := ∏ i, (P i).mass (x i)
  nonneg x := prod_nonneg (fun i _ => (P i).nonneg _)
  total := by
    classical
    have h := prod_univ_sum (fun _ : I => (univ : Finset A)) (fun i a => (P i).mass a)
    simp only [Fintype.piFinset_univ, (P _).total, prod_const_one] at h
    exact h.symm

lemma product_moment (P : I → Law A) (f : I → A → ℝ) :
    expect (product P) (fun x => ∏ i, f i (x i)) = ∏ i, expect (P i) (f i) := by
  classical
  simp only [expect, product, ← prod_mul_distrib]
  exact (show (∏ i, ∑ a, (P i).mass a * f i a) =
    ∑ x : I → A, ∏ i, (P i).mass (x i) * f i (x i) by
    simpa only [Fintype.piFinset_univ] using
      (prod_univ_sum (fun _ : I => (univ : Finset A)) (fun i a => (P i).mass a * f i a))).symm

lemma product_one_moment (P : I → Law A) (i : I) (f : A → ℝ) :
    expect (product P) (fun x => f (x i)) = expect (P i) f := by
  have h := product_moment P (fun j a => if j = i then f a else 1)
  simp only [Fintype.prod_ite_eq'] at h
  have he (j : I) : expect (P j) (fun a => if j = i then f a else 1) =
      if j = i then expect (P j) f else 1 := by
    split_ifs <;> simp [*]
  simp_rw [he] at h
  simpa only [Fintype.prod_ite_eq'] using h

lemma product_two_moment (P : I → Law A) {i j : I} (hij : i ≠ j)
    (f g : A → ℝ) :
    expect (product P) (fun x => f (x i) * g (x j)) =
      expect (P i) f * expect (P j) g := by
  have h := product_moment P (fun k a => (if k = i then f a else 1) *
    (if k = j then g a else 1))
  simp only [prod_mul_distrib, Fintype.prod_ite_eq'] at h
  have he (k : I) : expect (P k) (fun a => (if k = i then f a else 1) *
      (if k = j then g a else 1)) =
      (if k = i then expect (P k) f else 1) *
      (if k = j then expect (P k) g else 1) := by
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all
  simp_rw [he] at h
  simpa only [prod_mul_distrib, Fintype.prod_ite_eq'] using h

variable [DecidableEq A]

noncomputable def condition (P : Law A) (E : Finset A) (hE : 0 < ∑ a ∈ E, P.mass a) : Law A where
  mass a := if a ∈ E then P.mass a / (∑ a ∈ E, P.mass a) else 0
  nonneg a := by split_ifs; exact div_nonneg (P.nonneg a) hE.le; exact le_rfl
  total := by
    classical
    simp only [sum_ite_mem, univ_inter, ← sum_div]
    exact div_self hE.ne'

lemma condition_bound (P : Law A) (E : Finset A) (hE : 1 / 2 ≤ ∑ a ∈ E, P.mass a)
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    expect (condition P E (by linarith)) f ≤ 2 * expect P f := by
  change (∑ a, (if a ∈ E then P.mass a / (∑ a ∈ E, P.mass a) else 0) * f a) ≤
    2 * ∑ a, P.mass a * f a
  rw [mul_sum]
  simp only [← mul_assoc]
  apply sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_right _ (hf a)
  change (if a ∈ E then _ else 0) ≤ 2 * P.mass a
  split_ifs
  · apply (div_le_iff₀ (by linarith : 0 < ∑ a ∈ E, P.mass a)).mpr
    nlinarith [P.nonneg a]
  · exact mul_nonneg (by norm_num) (P.nonneg a)

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.FiniteLaw
open Finset

variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J] [DecidableEq I]

omit [DecidableEq I] in
lemma orthogonal_sum_square (P : Law A) (Z : I → A → ℝ)
    (h : ∀ i j, i ≠ j → expect P (fun x => Z i x * Z j x) = 0) :
    expect P (fun x => (∑ i, Z i x) ^ 2) = ∑ i, expect P (fun x => Z i x ^ 2) := by
  have hex (x : A) : (∑ i, Z i x) ^ 2 = ∑ i, ∑ j, Z i x * Z j x := by
    simp only [sq, sum_mul, mul_sum]
    exact sum_comm
  simp_rw [hex, expect_sum]
  apply sum_congr rfl
  intro i _
  rw [sum_eq_single i]
  · simp only [sq]
  · intro j _ hji
    exact h i j hji.symm
  · simp

lemma centered_square_le (P : Law A) (f : A → ℝ) (p : ℝ) (he : expect P f = p) :
    expect P (fun x => (f x - p) ^ 2) ≤ expect P (fun x => f x ^ 2) := by
  have hr (x : A) : (f x - p) ^ 2 = f x ^ 2 - 2 * p * f x + p ^ 2 := by ring
  simp_rw [hr, expect_add, expect_sub, expect_const_mul, expect_const, he]
  nlinarith [sq_nonneg p]

/-- The exact second-moment calculation for genuinely independent sampled
probability vectors. The vector's coordinates need not be independent. -/
lemma empirical_variance [Nonempty I] (P : I → Law A) (Y : I → A → J → ℝ)
    (p : J → ℝ) (hY : ∀ i x a, 0 ≤ Y i x a) (hs : ∀ i x, ∑ a, Y i x a = 1)
    (hm : ∀ i a, expect (P i) (fun x => Y i x a) = p a) :
    (∑ a, expect (product P) (fun x =>
      ((∑ i, Y i (x i) a) / Fintype.card I - p a) ^ 2)) ≤
        1 / Fintype.card I := by
  let q : ℝ := Fintype.card I
  have hq : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  have hcenter (i : I) (a : J) : expect (P i) (fun x => Y i x a - p a) = 0 := by
    rw [expect_sub, hm, expect_const, sub_self]
  have horth (a : J) (i j : I) (hij : i ≠ j) :
      expect (product P) (fun x => (Y i (x i) a - p a) * (Y j (x j) a - p a)) = 0 := by
    rw [product_two_moment P hij (fun x => Y i x a - p a) (fun x => Y j x a - p a),
      hcenter, hcenter, zero_mul]
  have hid (a : J) : expect (product P) (fun x =>
      ((∑ i, Y i (x i) a) / q - p a) ^ 2) =
      (∑ i, expect (P i) (fun x => (Y i x a - p a) ^ 2)) * (q ^ 2)⁻¹ := by
    have hx (x : I → A) : ((∑ i, Y i (x i) a) / q - p a) ^ 2 =
        (∑ i, (Y i (x i) a - p a)) ^ 2 * (q ^ 2)⁻¹ := by
      simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
      change (_ / q - p a) ^ 2 = (_ - q * p a) ^ 2 * _
      field_simp [hq.ne']
    simp_rw [hx]
    rw [expect_mul_const, orthogonal_sum_square _ _ (horth a)]
    congr 1
    apply sum_congr rfl
    intro i _
    exact product_one_moment P i (fun x => (Y i x a - p a) ^ 2)
  have hb (i : I) : ∑ a, expect (P i) (fun x => (Y i x a - p a) ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ a, expect (P i) (fun x => Y i x a ^ 2) :=
        sum_le_sum (fun a _ => centered_square_le _ _ _ (hm i a))
      _ = expect (P i) (fun x => ∑ a, Y i x a ^ 2) := (expect_sum _ _).symm
      _ ≤ expect (P i) (fun _ => 1) := expect_mono _ (fun x => by
        simpa only [hs, one_pow] using sum_sq_le_sq_sum_of_nonneg (s := univ)
          (f := fun a => Y i x a) (fun a _ => hY i x a))
      _ = 1 := expect_const _ _
  change (∑ a, expect (product P) (fun x => ((∑ i, Y i (x i) a) / q - p a) ^ 2)) ≤ 1 / q
  simp_rw [hid]
  rw [← sum_mul, sum_comm]
  calc
    _ ≤ (∑ _i : I, (1 : ℝ)) * (q ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (sum_le_sum (fun i _ => hb i)) (by positivity)
    _ = 1 / q := by
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
      change q * (q ^ 2)⁻¹ = 1 / q
      field_simp [hq.ne']

/-- A finite form of the TV/second-moment inequality, including samples with
zero mass. -/
lemma expected_tv_of_second_moment (P : Law A) (Z : A → J → ℝ) {v : ℝ}
    (hv : 0 ≤ v) (hvar : ∑ a, expect P (fun x => Z x a ^ 2) ≤ v) :
    expect P (fun x => (1 / 2 : ℝ) * ∑ a, |Z x a|) ≤
      (1 / 2 : ℝ) * Real.sqrt (Fintype.card J * v) := by
  have hsq : (∑ a, expect P (fun x => |Z x a|)) ^ 2 ≤ Fintype.card J * v := by
    calc
      _ ≤ Fintype.card J * ∑ a, (expect P (fun x => |Z x a|)) ^ 2 := by
        simpa only [card_univ] using sq_sum_le_card_mul_sum_sq
          (s := (univ : Finset J)) (f := fun a => expect P (fun x => |Z x a|))
      _ ≤ Fintype.card J * ∑ a, expect P (fun x => Z x a ^ 2) := by
        apply mul_le_mul_of_nonneg_left (sum_le_sum (fun a _ => expect_sq_abs _ _))
        positivity
      _ ≤ Fintype.card J * v := mul_le_mul_of_nonneg_left hvar (by positivity)
  have hn : 0 ≤ (Fintype.card J : ℝ) * v := mul_nonneg (by positivity) hv
  have hroot := Real.sq_sqrt hn
  have hrnon := Real.sqrt_nonneg ((Fintype.card J : ℝ) * v)
  rw [expect_const_mul, expect_sum]
  have hsum : (∑ a, expect P (fun x => |Z x a|)) ≤ Real.sqrt (Fintype.card J * v) := by
    nlinarith
  linarith

/-- Source lem:word-tv, for independent complete vectors, with its literal
one-half constant. This is used twice, not an assumption about empirical laws. -/
theorem independent_vectors_tv [Nonempty I] (P : I → Law A) (Y : I → A → J → ℝ)
    (p : J → ℝ) (hY : ∀ i x a, 0 ≤ Y i x a) (hs : ∀ i x, ∑ a, Y i x a = 1)
    (hm : ∀ i a, expect (P i) (fun x => Y i x a) = p a) :
    expect (product P) (fun x => (1 / 2 : ℝ) *
      ∑ a, |(∑ i, Y i (x i) a) / Fintype.card I - p a|) ≤
        (1 / 2 : ℝ) * Real.sqrt (Fintype.card J / Fintype.card I) := by
  simpa only [mul_one_div] using expected_tv_of_second_moment (product P)
    (fun x a => (∑ i, Y i (x i) a) / Fintype.card I - p a)
    (by positivity : 0 ≤ (1 : ℝ) / Fintype.card I)
    (empirical_variance P Y p hY hs hm)

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.FiniteLaw
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def prob (P : Law A) (E : Finset A) : ℝ := ∑ a ∈ E, P.mass a

omit [DecidableEq A] in
lemma prob_nonneg (P : Law A) (E : Finset A) : 0 ≤ prob P E :=
  sum_nonneg (fun a _ => P.nonneg a)

omit [DecidableEq A] in
lemma prob_le_one (P : Law A) (E : Finset A) : prob P E ≤ 1 := by
  unfold prob
  rw [← P.total]
  exact sum_le_univ_sum_of_nonneg (fun a => P.nonneg a)

lemma prob_eq_expect (P : Law A) (E : Finset A) :
    prob P E = expect P (fun a => if a ∈ E then 1 else 0) := by
  simp [prob, expect, mul_ite]

lemma prob_compl (P : Law A) (E : Finset A) : prob P Eᶜ = 1 - prob P E := by
  have h := sum_add_sum_compl E P.mass
  rw [P.total] at h
  simpa [prob] using (eq_sub_iff_add_eq.mpr (by linarith : (∑ a ∈ Eᶜ, P.mass a) + ∑ a ∈ E, P.mass a = 1))

lemma markov (P : Law A) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) {δ : ℝ} (hδ : 0 < δ) :
    prob P (univ.filter (fun a => δ < f a)) ≤ expect P f / δ := by
  rw [prob_eq_expect, le_div_iff₀ hδ, ← expect_mul_const]
  apply expect_mono
  intro a
  simp only [mem_filter, mem_univ, true_and]
  split_ifs with h
  · simpa using h.le
  · simpa using hf a

lemma union_bound {I : Type*} [Fintype I] (P : Law A) (E : I → Finset A) :
    prob P (univ.biUnion E) ≤ ∑ i, prob P (E i) := by
  simp_rw [prob_eq_expect]
  rw [← expect_sum]
  apply expect_mono
  intro a
  split_ifs with ha
  · obtain ⟨i, _, hi⟩ := mem_biUnion.mp ha
    calc
      (1 : ℝ) = (if a ∈ E i then 1 else 0) := by simp [hi]
      _ ≤ ∑ j, if a ∈ E j then (1 : ℝ) else 0 :=
        single_le_sum (f := fun j => if a ∈ E j then (1 : ℝ) else 0)
          (fun j _ => by positivity) (mem_univ i)
  · exact sum_nonneg (fun j _ => by positivity)

lemma good_event_mass {I : Type*} [Fintype I] (P : Law A) (f : I → A → ℝ)
    (hf : ∀ i a, 0 ≤ f i a) {δ c : ℝ} (hδ : 0 < δ)
    (hb : ∀ i, expect P (f i) ≤ c)
    (hc : (Fintype.card I : ℝ) * c / δ ≤ 1 / 2) :
    1 / 2 ≤ prob P (univ.filter (fun a => ∀ i, f i a ≤ δ)) := by
  classical
  let E : I → Finset A := fun i => univ.filter (fun a => δ < f i a)
  have he : (univ.filter (fun a => ∀ i, f i a ≤ δ)) = (univ.biUnion E)ᶜ := by
    ext a
    simp [E]
  rw [he, prob_compl]
  have hbound : prob P (univ.biUnion E) ≤ 1 / 2 := calc
    _ ≤ ∑ i, prob P (E i) := union_bound P E
    _ ≤ ∑ _ : I, c / δ := sum_le_sum fun i _ =>
      (markov P (f i) (hf i) hδ).trans (div_le_div_of_nonneg_right (hb i) hδ.le)
    _ = Fintype.card I * c / δ := by simp [mul_div_assoc]
    _ ≤ _ := hc
  linarith

lemma exists_good {I : Type*} [Fintype I] (P : Law A) (E : I → Finset A)
    (h : (∑ i, prob P (E i)) < 1) : ∃ a, 0 < P.mass a ∧ ∀ i, a ∉ E i := by
  classical
  have hpos : 0 < prob P (univ.biUnion E)ᶜ := by
    rw [prob_compl]
    have := union_bound P E
    linarith
  obtain ⟨a, ha, hw⟩ := sum_pos_iff_of_nonneg (fun a _ => P.nonneg a) |>.mp
    (show 0 < ∑ a ∈ (univ.biUnion E)ᶜ, P.mass a from hpos)
  exact ⟨a, hw, fun i hi => (mem_compl.mp ha) (mem_biUnion.mpr ⟨i, mem_univ i, hi⟩)⟩

lemma condition_supported (P : Law A) (E : Finset A) (hE : 0 < prob P E) {a : A}
    (ha : 0 < (condition P E hE).mass a) : a ∈ E ∧ 0 < P.mass a := by
  by_cases he : a ∈ E
  · refine ⟨he, ?_⟩
    have hdiv : 0 < P.mass a / prob P E := by simpa [condition, he, prob] using ha
    exact (div_pos_iff_of_pos_right hE).mp hdiv
  · simp [condition, he] at ha

noncomputable def push {C : Type*} [Fintype C] [DecidableEq C]
    (P : Law A) (f : A → C) : Law C where
  mass c := ∑ a, if f a = c then P.mass a else 0
  nonneg c := sum_nonneg (fun a _ => by split_ifs; exact P.nonneg a; exact le_rfl)
  total := by rw [sum_comm]; simpa using P.total

omit [DecidableEq A] in
lemma expect_push {C : Type*} [Fintype C] [DecidableEq C]
    (P : Law A) (f : A → C) (g : C → ℝ) :
    expect (push P f) g = expect P (g ∘ f) := by
  simp only [expect, push, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp [ite_mul]

end SmoothObstruction.FiniteLaw

end

end OAI
