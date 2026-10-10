import OAI.NumberTheory.JointDickman.Probability.BernoulliComparison

namespace OAI

/-!
# Comparing finite product laws

Replacing one independent coordinate at a time bounds the `L¹` distance
of two finite product probability laws by the sum of their coordinate
distances. Applied to the mutually exclusive prime-site law, this gives
the accumulated quadratic error for arbitrary bounded complex tests.
All identities and inequalities here are proved by finite sums.
-/

namespace JointDickman

open scoped BigOperators

/-- Product mass on a finite family of coordinate spaces. -/
noncomputable def finiteProductMass {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    (a : ∀ i, Ω i → ℝ) (x : ∀ i, Ω i) : ℝ := ∏ i, a i (x i)

theorem finiteProductMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    (a : ∀ i, Ω i → ℝ) (ha : ∀ i x, 0 ≤ a i x) (x : ∀ i, Ω i) :
    0 ≤ finiteProductMass a x :=
  Finset.prod_nonneg (fun i _ => ha i (x i))

theorem finiteProductMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (a : ∀ i, Ω i → ℝ)
    (ha : ∀ i, ∑ x, a i x = 1) : ∑ x, finiteProductMass a x = 1 := by
  classical
  unfold finiteProductMass
  rw [← Fintype.prod_sum]
  simp only [ha, Finset.prod_const_one]

private theorem finiteProductMass_coordinate_l1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (a b : ∀ i, Ω i → ℝ) (i : ι)
    (ha : ∀ j x, 0 ≤ a j x) (ha1 : ∀ j, ∑ x, a j x = 1)
    (hab : ∀ j, j ≠ i → ∀ x, a j x = b j x) :
    (∑ x, |finiteProductMass a x - finiteProductMass b x|) =
      ∑ y, |a i y - b i y| := by
  classical
  let c : ∀ j, Ω j → ℝ := fun j y => if j = i then |a j y - b j y| else a j y
  have hp (x : ∀ j, Ω j) :
      |finiteProductMass a x - finiteProductMass b x| = finiteProductMass c x := by
    have hr : (∏ j ∈ Finset.univ.erase i, a j (x j)) =
        ∏ j ∈ Finset.univ.erase i, b j (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hab j (Finset.ne_of_mem_erase hj) (x j)
    have hcr : (∏ j ∈ Finset.univ.erase i, c j (x j)) =
        ∏ j ∈ Finset.univ.erase i, a j (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [c, Finset.ne_of_mem_erase hj]
    unfold finiteProductMass
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun j => b j (x j)) (Finset.mem_univ i), ← hr,
      ← sub_mul, abs_mul, abs_of_nonneg (Finset.prod_nonneg (fun j _ => ha j (x j))),
      ← Finset.mul_prod_erase _ (fun j => c j (x j)) (Finset.mem_univ i), hcr]
    simp [c]
  simp_rw [hp]
  unfold finiteProductMass
  rw [← Fintype.prod_sum]
  have hc (j : ι) : (∑ y, c j y) = if j = i then (∑ y, |a j y - b j y|) else 1 := by
    by_cases hj : j = i
    · simp [c, hj]
    · simp [c, hj, ha1]
  simp_rw [hc]
  exact Fintype.prod_ite_eq' i (fun j => ∑ y, |a j y - b j y|)

/-- The `L¹` discrepancy of product probability masses is at most the
sum of the coordinate discrepancies. No order on the coordinates is needed. -/
theorem finiteProductMass_l1_le {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (a b : ∀ i, Ω i → ℝ)
    (ha : ∀ i x, 0 ≤ a i x) (hb : ∀ i x, 0 ≤ b i x)
    (ha1 : ∀ i, ∑ x, a i x = 1) (hb1 : ∀ i, ∑ x, b i x = 1) :
    (∑ x, |finiteProductMass a x - finiteProductMass b x|) ≤
      ∑ i, ∑ y, |a i y - b i y| := by
  classical
  let mix (s : Finset ι) : ∀ i, Ω i → ℝ := fun i y => if i ∈ s then a i y else b i y
  have hm (s : Finset ι) (i : ι) (y : Ω i) : 0 ≤ mix s i y := by
    dsimp [mix]
    split_ifs <;> [exact ha i y; exact hb i y]
  have hm1 (s : Finset ι) (i : ι) : ∑ y, mix s i y = 1 := by
    by_cases hi : i ∈ s <;> simp [mix, hi, ha1, hb1]
  have h (s : Finset ι) :
      (∑ x, |finiteProductMass (mix s) x - finiteProductMass b x|) ≤
        ∑ i ∈ s, ∑ y, |a i y - b i y| := by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert i s hi ih =>
      have heq := finiteProductMass_coordinate_l1 (mix (insert i s)) (mix s) i
        (hm _) (hm1 _) (by
          intro j hji y
          simp [mix, hji])
      have ht : (∑ x, |finiteProductMass (mix (insert i s)) x - finiteProductMass b x|) ≤
          (∑ x, |finiteProductMass (mix (insert i s)) x - finiteProductMass (mix s) x|) +
            ∑ x, |finiteProductMass (mix s) x - finiteProductMass b x| := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro x _
        exact abs_sub_le _ _ _
      rw [heq] at ht
      simp only [mix, Finset.mem_insert_self, ↓reduceIte, hi] at ht
      rw [Finset.sum_insert hi]
      linarith
  simpa [mix] using h Finset.univ

/-- A bounded complex test sees no more than its bound times the sum
of the coordinate `L¹` errors. -/
theorem finiteProductMass_test_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (a b : ∀ i, Ω i → ℝ)
    (ha : ∀ i x, 0 ≤ a i x) (hb : ∀ i x, 0 ≤ b i x)
    (ha1 : ∀ i, ∑ x, a i x = 1) (hb1 : ∀ i, ∑ x, b i x = 1)
    (F : (∀ i, Ω i) → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x, ‖F x‖ ≤ L) :
    ‖(∑ x, (finiteProductMass a x : ℂ) * F x) -
      (∑ x, (finiteProductMass b x : ℂ) * F x)‖ ≤
      L * ∑ i, ∑ y, |a i y - b i y| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, ‖(finiteProductMass a x : ℂ) * F x -
        (finiteProductMass b x : ℂ) * F x‖ := norm_sum_le _ _
    _ ≤ ∑ x, |finiteProductMass a x - finiteProductMass b x| * L := by
      apply Finset.sum_le_sum
      intro x _
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)
    _ = L * ∑ x, |finiteProductMass a x - finiteProductMass b x| := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (finiteProductMass_l1_le a b ha hb ha1 hb1) hL

/-- Mutually exclusive site hits, independent between coordinates. -/
noncomputable def categoricalProductMass {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (P : Finset α) (q : ι → α → ℝ) (x : ι → P.powerset) : ℝ :=
  finiteProductMass (fun i S => categoricalSubsetMass P (q i) S.val) x

/-- Independent site hits, independent also between coordinates. -/
noncomputable def bernoulliProductMass {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (P : Finset α) (q : ι → α → ℝ) (x : ι → P.powerset) : ℝ :=
  finiteProductMass (fun i S => bernoulliSubsetMass P (q i) S.val) x

theorem categoricalProduct_l1_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (P : Finset α) (q : ι → α → ℝ)
    (hq : ∀ i j, j ∈ P → 0 ≤ q i j ∧ q i j ≤ 1)
    (hsum : ∀ i, ∑ j ∈ P, q i j ≤ 1) :
    (∑ x, |categoricalProductMass P q x - bernoulliProductMass P q x|) ≤
      2 * ∑ i, (∑ j ∈ P, q i j) ^ 2 := by
  classical
  have h := finiteProductMass_l1_le
    (fun i (S : P.powerset) => categoricalSubsetMass P (q i) S.val)
    (fun i (S : P.powerset) => bernoulliSubsetMass P (q i) S.val)
    (fun i _ => categoricalSubsetMass_nonneg (fun j hj => (hq i j hj).1) (hsum i))
    (fun i S => bernoulliSubsetMass_nonneg (Finset.mem_powerset.mp S.property) (hq i))
    (fun i => by simpa only [Finset.sum_coe_sort] using categoricalSubsetMass_sum P (q i))
    (fun i => by simpa only [Finset.sum_coe_sort] using bernoulliSubsetMass_sum P (q i))
  refine h.trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ = ∑ S ∈ P.powerset, |categoricalSubsetMass P (q i) S -
        bernoulliSubsetMass P (q i) S| := Finset.sum_coe_sort _ _
    _ ≤ _ := categorical_bernoulli_l1_le P (q i) (hq i)

theorem categoricalProduct_test_bound {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (P : Finset α) (q : ι → α → ℝ)
    (hq : ∀ i j, j ∈ P → 0 ≤ q i j ∧ q i j ≤ 1)
    (hsum : ∀ i, ∑ j ∈ P, q i j ≤ 1)
    (F : (ι → P.powerset) → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x, ‖F x‖ ≤ L) :
    ‖(∑ x, (categoricalProductMass P q x : ℂ) * F x) -
      (∑ x, (bernoulliProductMass P q x : ℂ) * F x)‖ ≤
      2 * L * ∑ i, (∑ j ∈ P, q i j) ^ 2 := by
  classical
  have h := finiteProductMass_test_bound
    (fun i (S : P.powerset) => categoricalSubsetMass P (q i) S.val)
    (fun i (S : P.powerset) => bernoulliSubsetMass P (q i) S.val)
    (fun i _ => categoricalSubsetMass_nonneg (fun j hj => (hq i j hj).1) (hsum i))
    (fun i S => bernoulliSubsetMass_nonneg (Finset.mem_powerset.mp S.property) (hq i))
    (fun i => by simpa only [Finset.sum_coe_sort] using categoricalSubsetMass_sum P (q i))
    (fun i => by simpa only [Finset.sum_coe_sort] using bernoulliSubsetMass_sum P (q i))
    F hL hF
  refine h.trans ?_
  calc
    _ ≤ L * ∑ i, 2 * (∑ j ∈ P, q i j) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hL
      apply Finset.sum_le_sum
      intro i _
      calc
        _ = ∑ S ∈ P.powerset, |categoricalSubsetMass P (q i) S -
            bernoulliSubsetMass P (q i) S| := Finset.sum_coe_sort _ _
        _ ≤ _ := categorical_bernoulli_l1_le P (q i) (hq i)
    _ = _ := by rw [← Finset.mul_sum]; ring

private theorem prime_site_probability_square_sum {α : Type*}
    (P : Finset α) (Q : Finset ℕ) :
    (∑ p : Q, (∑ _j ∈ P, 1 / (p.val : ℝ)) ^ 2) =
      (P.card : ℝ) ^ 2 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
  classical
  rw [show (∑ p : Q, (∑ _j ∈ P, 1 / (p.val : ℝ)) ^ 2) =
    ∑ p ∈ Q, (∑ _j ∈ P, 1 / (p : ℝ)) ^ 2 from
      Finset.sum_coe_sort Q (fun p => (∑ _j ∈ P, 1 / (p : ℝ)) ^ 2), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div, div_pow]

/-- Accumulated prime-site discrepancy. The site count must not exceed
any prime, precisely so that the categorical laws are nonnegative. -/
theorem categoricalPrimeProduct_l1_le {α : Type*} [DecidableEq α]
    (P : Finset α) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hcard : ∀ p ∈ Q, P.card ≤ p) :
    (∑ x, |categoricalProductMass P (fun (p : Q) _ => 1 / (p.val : ℝ)) x -
      bernoulliProductMass P (fun (p : Q) _ => 1 / (p.val : ℝ)) x|) ≤
      2 * (P.card : ℝ) ^ 2 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
  classical
  have hq (p : Q) (j : α) (_hj : j ∈ P) :
      0 ≤ 1 / (p.val : ℝ) ∧ 1 / (p.val : ℝ) ≤ 1 := by
    have hp := hQ p.val p.property
    have hp0 : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) ≤ p.val := by exact_mod_cast hp.one_le
    exact ⟨by positivity, (div_le_one hp0).mpr hp1⟩
  have hs (p : Q) : (∑ _j ∈ P, 1 / (p.val : ℝ)) ≤ 1 := by
    have hp0 : (0 : ℝ) < p.val := by exact_mod_cast (hQ p.val p.property).pos
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    exact (div_le_one hp0).mpr (by exact_mod_cast hcard p.val p.property)
  have h := categoricalProduct_l1_le P (fun (p : Q) _ => 1 / (p.val : ℝ)) hq hs
  rw [prime_site_probability_square_sum] at h
  simpa only [mul_assoc] using h

/-- For any bounded complex function of all prime hit sets, independent
Bernoulli replacement costs at most `2 L M² sum_p 1/p²`. -/
theorem categoricalPrimeProduct_test_bound {α : Type*} [DecidableEq α]
    (P : Finset α) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hcard : ∀ p ∈ Q, P.card ≤ p)
    (F : (Q → P.powerset) → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x, ‖F x‖ ≤ L) :
    ‖(∑ x, (categoricalProductMass P (fun (p : Q) _ => 1 / (p.val : ℝ)) x : ℂ) * F x) -
      (∑ x, (bernoulliProductMass P (fun (p : Q) _ => 1 / (p.val : ℝ)) x : ℂ) * F x)‖ ≤
      2 * L * (P.card : ℝ) ^ 2 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
  classical
  have hq (p : Q) (j : α) (_hj : j ∈ P) :
      0 ≤ 1 / (p.val : ℝ) ∧ 1 / (p.val : ℝ) ≤ 1 := by
    have hp := hQ p.val p.property
    have hp0 : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) ≤ p.val := by exact_mod_cast hp.one_le
    exact ⟨by positivity, (div_le_one hp0).mpr hp1⟩
  have hs (p : Q) : (∑ _j ∈ P, 1 / (p.val : ℝ)) ≤ 1 := by
    have hp0 : (0 : ℝ) < p.val := by exact_mod_cast (hQ p.val p.property).pos
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    exact (div_le_one hp0).mpr (by exact_mod_cast hcard p.val p.property)
  have h := categoricalProduct_test_bound P (fun (p : Q) _ => 1 / (p.val : ℝ)) hq hs F hL hF
  rw [prime_site_probability_square_sum] at h
  simpa only [mul_assoc] using h

/-- One Bernoulli coordinate, written as a mass on `Bool`. -/
noncomputable def bernoulliBitMass (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

theorem bernoulliBitMass_sum (q : ℝ) : ∑ b, bernoulliBitMass q b = 1 := by
  simp [bernoulliBitMass]

theorem bernoulliBitMass_nonneg {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) (b : Bool) :
    0 ≤ bernoulliBitMass q b := by
  cases b <;> simp only [bernoulliBitMass, Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr hq.2
  · exact hq.1

/-- Changing a Bernoulli success probability has exactly this `L¹` cost. -/
theorem bernoulliBitMass_l1 (q r : ℝ) :
    (∑ b, |bernoulliBitMass q b - bernoulliBitMass r b|) = 2 * |q - r| := by
  simp only [Fintype.sum_bool, bernoulliBitMass, Bool.false_eq_true, ↓reduceIte]
  rw [show 1 - q - (1 - r) = -(q - r) by ring, abs_neg]
  ring

/-- The membership indicators of a subset give its finite Boolean coordinates. -/
noncomputable def subsetHitEquiv {α : Type*} [DecidableEq α] (P : Finset α) :
    P.powerset ≃ (P → Bool) where
  toFun S i := decide (i.val ∈ S.val)
  invFun f := ⟨P.filter (fun i => ∃ hi : i ∈ P, f ⟨i, hi⟩ = true),
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
  left_inv S := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨_, _, hi⟩
      exact hi
    · intro hi
      have hiP := Finset.mem_powerset.mp S.property hi
      exact ⟨hiP, hiP, hi⟩
  right_inv f := by
    funext i
    change decide (i.val ∈ P.filter (fun j => ∃ hj : j ∈ P, f ⟨j, hj⟩ = true)) = f i
    cases hf : f i <;> simp [Finset.mem_filter, i.property, hf]

theorem bernoulliSubsetMass_eq_product {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (S : P.powerset) :
    finiteProductMass (fun (i : P) => bernoulliBitMass (q i.val)) (subsetHitEquiv P S) =
      bernoulliSubsetMass P q S.val := by
  classical
  have hp : finiteProductMass (fun (i : P) => bernoulliBitMass (q i.val))
      (subsetHitEquiv P S) = ∏ i : P, if i.val ∈ S.val then q i.val else 1 - q i.val := by
    unfold finiteProductMass
    apply Finset.prod_congr rfl
    intro i _
    simp [bernoulliBitMass, subsetHitEquiv]
  rw [hp, show (∏ i : P, if i.val ∈ S.val then q i.val else 1 - q i.val) =
    ∏ i ∈ P, if i ∈ S.val then q i else 1 - q i from
      Finset.prod_coe_sort P (fun i => if i ∈ S.val then q i else 1 - q i), Finset.prod_ite]
  have hs : P.filter (fun i => i ∈ S.val) = S.val := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => Finset.mem_powerset.mp S.property hi)
  have hc : P.filter (fun i => i ∉ S.val) = P \ S.val := by
    ext i
    simp
  rw [hs, hc]
  rfl

/-- Independent Bernoulli subset laws are Lipschitz in their probabilities. -/
theorem bernoulliSubsetMass_l1_perturb {α : Type*} [DecidableEq α]
    (P : Finset α) (q r : α → ℝ)
    (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1) (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1) :
    (∑ S ∈ P.powerset, |bernoulliSubsetMass P q S - bernoulliSubsetMass P r S|) ≤
      2 * ∑ i ∈ P, |q i - r i| := by
  classical
  have h := finiteProductMass_l1_le
    (fun (i : P) => bernoulliBitMass (q i.val))
    (fun (i : P) => bernoulliBitMass (r i.val))
    (fun i b => bernoulliBitMass_nonneg (hq i.val i.property) b)
    (fun i b => bernoulliBitMass_nonneg (hr i.val i.property) b)
    (fun i => bernoulliBitMass_sum (q i.val)) (fun i => bernoulliBitMass_sum (r i.val))
  rw [← (subsetHitEquiv P).sum_comp
    (fun x => |finiteProductMass (fun (i : P) => bernoulliBitMass (q i.val)) x -
      finiteProductMass (fun (i : P) => bernoulliBitMass (r i.val)) x|)] at h
  simp_rw [bernoulliSubsetMass_eq_product, bernoulliBitMass_l1] at h
  have hl : (∑ S : P.powerset, |bernoulliSubsetMass P q S.val - bernoulliSubsetMass P r S.val|) =
      ∑ S ∈ P.powerset, |bernoulliSubsetMass P q S - bernoulliSubsetMass P r S| :=
    Finset.sum_coe_sort P.powerset (fun S => |bernoulliSubsetMass P q S - bernoulliSubsetMass P r S|)
  rw [hl, show (∑ i : P, 2 * |q i.val - r i.val|) = ∑ i ∈ P, 2 * |q i - r i| from
    Finset.sum_coe_sort P (fun i => 2 * |q i - r i|), ← Finset.mul_sum] at h
  exact h

/-- Perturbing all prime/site probabilities costs the sum of their local
probability changes, with no independence hypothesis beyond the product definition. -/
theorem bernoulliProduct_l1_perturb {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (P : Finset α) (q r : ι → α → ℝ)
    (hq : ∀ i j, j ∈ P → 0 ≤ q i j ∧ q i j ≤ 1)
    (hr : ∀ i j, j ∈ P → 0 ≤ r i j ∧ r i j ≤ 1) :
    (∑ x, |bernoulliProductMass P q x - bernoulliProductMass P r x|) ≤
      2 * ∑ i, ∑ j ∈ P, |q i j - r i j| := by
  classical
  have h := finiteProductMass_l1_le
    (fun i (S : P.powerset) => bernoulliSubsetMass P (q i) S.val)
    (fun i (S : P.powerset) => bernoulliSubsetMass P (r i) S.val)
    (fun i S => bernoulliSubsetMass_nonneg (Finset.mem_powerset.mp S.property) (hq i))
    (fun i S => bernoulliSubsetMass_nonneg (Finset.mem_powerset.mp S.property) (hr i))
    (fun i => by simpa only [Finset.sum_coe_sort] using bernoulliSubsetMass_sum P (q i))
    (fun i => by simpa only [Finset.sum_coe_sort] using bernoulliSubsetMass_sum P (r i))
  refine h.trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ = ∑ S ∈ P.powerset, |bernoulliSubsetMass P (q i) S -
        bernoulliSubsetMass P (r i) S| := Finset.sum_coe_sort _ _
    _ ≤ _ := bernoulliSubsetMass_l1_perturb P (q i) (r i) (hq i) (hr i)

/-- Finite `L¹` error controls every bounded complex test. -/
theorem finiteMass_test_bound_of_l1 {Ω : Type*} [Fintype Ω]
    (a b : Ω → ℝ) (F : Ω → ℂ) {L ε : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x, ‖F x‖ ≤ L) (hε : (∑ x, |a x - b x|) ≤ ε) :
    ‖(∑ x, (a x : ℂ) * F x) - (∑ x, (b x : ℂ) * F x)‖ ≤ L * ε := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, ‖(a x : ℂ) * F x - (b x : ℂ) * F x‖ := norm_sum_le _ _
    _ ≤ ∑ x, |a x - b x| * L := by
      apply Finset.sum_le_sum
      intro x _
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)
    _ = L * ∑ x, |a x - b x| := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hε hL

theorem bernoulliProduct_test_perturb {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (P : Finset α) (q r : ι → α → ℝ)
    (hq : ∀ i j, j ∈ P → 0 ≤ q i j ∧ q i j ≤ 1)
    (hr : ∀ i j, j ∈ P → 0 ≤ r i j ∧ r i j ≤ 1)
    (F : (ι → P.powerset) → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x, ‖F x‖ ≤ L) :
    ‖(∑ x, (bernoulliProductMass P q x : ℂ) * F x) -
      (∑ x, (bernoulliProductMass P r x : ℂ) * F x)‖ ≤
      2 * L * ∑ i, ∑ j ∈ P, |q i j - r i j| := by
  have h := finiteMass_test_bound_of_l1 _ _ F hL hF (bernoulliProduct_l1_perturb P q r hq hr)
  simpa only [mul_left_comm, mul_assoc] using h

/-- Mutually exclusive probabilities may also be perturbed when replacing
them by independent hits. This combines the two actual comparison errors. -/
theorem categoricalProduct_l1_perturb {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (P : Finset α) (q r : ι → α → ℝ)
    (hq : ∀ i j, j ∈ P → 0 ≤ q i j ∧ q i j ≤ 1)
    (hr : ∀ i j, j ∈ P → 0 ≤ r i j ∧ r i j ≤ 1)
    (hsum : ∀ i, ∑ j ∈ P, q i j ≤ 1) :
    (∑ x, |categoricalProductMass P q x - bernoulliProductMass P r x|) ≤
      2 * (∑ i, (∑ j ∈ P, q i j) ^ 2) + 2 * ∑ i, ∑ j ∈ P, |q i j - r i j| := by
  have ht : (∑ x, |categoricalProductMass P q x - bernoulliProductMass P r x|) ≤
      (∑ x, |categoricalProductMass P q x - bernoulliProductMass P q x|) +
        ∑ x, |bernoulliProductMass P q x - bernoulliProductMass P r x| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun x _ => abs_sub_le _ _ _)
  exact ht.trans (add_le_add (categoricalProduct_l1_le P q hq hsum)
    (bernoulliProduct_l1_perturb P q r hq hr))

/-- The probability change for the extra-root model in `graph.tex`. -/
theorem reciprocal_exclusion_perturb {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (hMp : 2 * M ≤ p) : |1 / (p - M) - 1 / p| ≤ 2 * M / p ^ 2 := by
  have hd : 0 < p - M := by linarith
  have he : 1 / (p - M) - 1 / p = M / (p * (p - M)) := by
    field_simp
    ring
  rw [he, abs_of_nonneg (div_nonneg hM (mul_pos hp hd).le)]
  apply (div_le_div_iff₀ (mul_pos hp hd) (sq_pos_of_pos hp)).mpr
  have h := mul_nonneg (mul_nonneg hM hp.le) (sub_nonneg.mpr hMp)
  nlinarith

end JointDickman

end OAI
