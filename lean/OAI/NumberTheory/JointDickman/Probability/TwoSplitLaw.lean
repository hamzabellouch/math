import OAI.NumberTheory.JointDickman.Amplification.ProductComparison

namespace OAI

/-!
# Two fair splits of the same prime site

The local law is constructed by first selecting a Bernoulli site and then,
conditional on that hit, taking two independent fair splits. Its common and
exclusive categories have mass `q/4` each. Finite product comparison gives
the independent common/exclusive model without assuming a coupling.
-/

namespace JointDickman

open scoped BigOperators

/-- Finite pushforward of a real mass function. -/
noncomputable def finitePushMass {A B : Type*} [Fintype A]
    (a : A → ℝ) (f : A → B) (y : B) : ℝ := by
  classical
  exact ∑ x, if f x = y then a x else 0

theorem finitePushMass_test {A B : Type*} [Fintype A] [Fintype B]
    (a : A → ℝ) (f : A → B) (F : B → ℂ) :
    (∑ y, (finitePushMass a f y : ℂ) * F y) = ∑ x, (a x : ℂ) * F (f x) := by
  classical
  calc
    _ = ∑ y, ∑ x, if f x = y then (a x : ℂ) * F y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [finitePushMass, Complex.ofReal_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = ∑ x, ∑ y, if f x = y then (a x : ℂ) * F y else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      simp

/-- Pushforward commutes with finite independent products. -/
theorem finiteProductMass_pushforward {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (a : ∀ i, A i → ℝ) (f : ∀ i, A i → B i) (y : ∀ i, B i) :
    finiteProductMass (fun i => finitePushMass (a i) (f i)) y =
      finitePushMass (finiteProductMass a) (fun x i => f i (x i)) y := by
  classical
  unfold finiteProductMass finitePushMass
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f i (x i)) = y
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i _
    rw [ite_eq_left (congrFun h i)]
  · rw [ite_eq_right h]
    have hne : ∃ i, f i (x i) ≠ y i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem finiteProductMass_pushforward_test {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (a : ∀ i, A i → ℝ) (f : ∀ i, A i → B i) (F : (∀ i, B i) → ℂ) :
    (∑ y, (finiteProductMass (fun i => finitePushMass (a i) (f i)) y : ℂ) * F y) =
      ∑ x, (finiteProductMass a x : ℂ) * F (fun i => f i (x i)) := by
  simp_rw [finiteProductMass_pushforward]
  exact finitePushMass_test _ _ _

/-- Conditional on a site hit, the two choices are independent fair bits;
an absent site gives two absent splits. -/
noncomputable def conditionalFairSplitMass (hit : Bool) (b : Bool × Bool) : ℝ :=
  if hit then bernoulliBitMass (1 / 2) b.1 * bernoulliBitMass (1 / 2) b.2
  else if b = (false, false) then 1 else 0

/-- The actual same-site two-split law, integrating out the Bernoulli hit. -/
noncomputable def sameSiteTwoSplitMass (q : ℝ) (b : Bool × Bool) : ℝ :=
  ∑ hit, bernoulliBitMass q hit * conditionalFairSplitMass hit b

theorem conditionalFairSplitMass_sum (hit : Bool) : ∑ b, conditionalFairSplitMass hit b = 1 := by
  cases hit <;> norm_num [conditionalFairSplitMass, bernoulliBitMass,
    Fintype.sum_prod_type, Fintype.sum_bool]

theorem sameSiteTwoSplitMass_formula (q : ℝ) (b : Bool × Bool) :
    sameSiteTwoSplitMass q b = if b = (false, false) then 1 - 3 * q / 4 else q / 4 := by
  rcases b with ⟨b₁, b₂⟩
  cases b₁ <;> cases b₂ <;>
    simp [sameSiteTwoSplitMass, conditionalFairSplitMass, bernoulliBitMass] <;> ring

theorem sameSiteTwoSplitMass_sum (q : ℝ) : ∑ b, sameSiteTwoSplitMass q b = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, sameSiteTwoSplitMass_formula]
  norm_num
  ring

theorem sameSiteTwoSplitMass_nonneg {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) (b : Bool × Bool) :
    0 ≤ sameSiteTwoSplitMass q b := by
  rw [sameSiteTwoSplitMass_formula]
  split_ifs <;> linarith [hq.1, hq.2]

/-- The three labels are common, first-exclusive, second-exclusive. -/
abbrev SplitCategories := ((Finset.univ : Finset (Fin 3)).powerset : Type)

def splitCategory (b : Bool × Bool) : SplitCategories :=
  ⟨match b with
    | (true, true) => {0}
    | (true, false) => {1}
    | (false, true) => {2}
    | (false, false) => ∅,
    Finset.mem_powerset.mpr (Finset.subset_univ _)⟩

/-- This identifies the categorical law from the actual conditional split
construction, including its empty-set mass. -/
theorem sameSiteTwoSplitMass_categories (q : ℝ) (S : SplitCategories) :
    finitePushMass (sameSiteTwoSplitMass q) splitCategory S =
      categoricalSubsetMass Finset.univ (fun _ : Fin 3 => q / 4) S.val := by
  simp [finitePushMass, sameSiteTwoSplitMass_formula, splitCategory,
    categoricalSubsetMass, Fintype.sum_prod_type, Fin.sum_univ_succ, Subtype.ext_iff, eq_comm]
  ring_nf

theorem threeCategoryBernoulli_factor (q : ℝ) (S : SplitCategories) :
    bernoulliSubsetMass Finset.univ (fun _ : Fin 3 => q) S.val =
      bernoulliBitMass q (decide ((0 : Fin 3) ∈ S.val)) *
      bernoulliBitMass q (decide ((1 : Fin 3) ∈ S.val)) *
      bernoulliBitMass q (decide ((2 : Fin 3) ∈ S.val)) := by
  have h := bernoulliSubsetMass_eq_product (Finset.univ : Finset (Fin 3)) (fun _ => q) S
  change (∏ i : (Finset.univ : Finset (Fin 3)),
    bernoulliBitMass q (decide (i.val ∈ S.val))) = _ at h
  rw [show (∏ i : (Finset.univ : Finset (Fin 3)),
      bernoulliBitMass q (decide (i.val ∈ S.val))) =
        ∏ i : Fin 3, bernoulliBitMass q (decide (i ∈ S.val)) from
          Finset.prod_coe_sort (Finset.univ : Finset (Fin 3))
            (fun i => bernoulliBitMass q (decide (i ∈ S.val))), Fin.prod_univ_three] at h
  exact h.symm

/-- The comparison law really is a product of the three category vectors,
each of which is itself a product of Bernoulli coordinates. -/
theorem independentCategoryProductMass_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (y : ι → SplitCategories) :
    bernoulliProductMass Finset.univ (fun i (_ : Fin 3) => q i) y =
      finiteProductMass (fun i => bernoulliBitMass (q i)) (fun i => decide ((0 : Fin 3) ∈ (y i).val)) *
      finiteProductMass (fun i => bernoulliBitMass (q i)) (fun i => decide ((1 : Fin 3) ∈ (y i).val)) *
      finiteProductMass (fun i => bernoulliBitMass (q i)) (fun i => decide ((2 : Fin 3) ∈ (y i).val)) := by
  unfold bernoulliProductMass finiteProductMass
  simp_rw [threeCategoryBernoulli_factor]
  simp only [Finset.prod_mul_distrib]

/-- Product law of the actual pairs of fair splits. -/
noncomputable def sameSiteTwoSplitProductMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (x : ι → Bool × Bool) : ℝ :=
  finiteProductMass (fun i => sameSiteTwoSplitMass (q i)) x

theorem sameSiteTwoSplitProductMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) : ∑ x, sameSiteTwoSplitProductMass q x = 1 :=
  finiteProductMass_sum _ (fun i => sameSiteTwoSplitMass_sum (q i))

theorem sameSiteTwoSplitProductMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (x : ι → Bool × Bool) :
    0 ≤ sameSiteTwoSplitProductMass q x :=
  finiteProductMass_nonneg _ (fun i b => sameSiteTwoSplitMass_nonneg (hq i) b) x

theorem sameSiteTwoSplitProduct_categories {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (F : (ι → SplitCategories) → ℂ) :
    (∑ x, (sameSiteTwoSplitProductMass q x : ℂ) * F (fun i => splitCategory (x i))) =
      ∑ y, (categoricalProductMass Finset.univ (fun i (_ : Fin 3) => q i / 4) y : ℂ) * F y := by
  have h := finiteProductMass_pushforward_test (fun i => sameSiteTwoSplitMass (q i))
    (fun _ => splitCategory) F
  unfold finiteProductMass at h
  simp_rw [sameSiteTwoSplitMass_categories] at h
  exact h.symm

/-- Comparing the actual two-split law to three independent category bits. -/
theorem sameSiteTwoSplitProduct_test_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (F : (ι → SplitCategories) → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ y, ‖F y‖ ≤ L) :
    ‖(∑ x, (sameSiteTwoSplitProductMass q x : ℂ) * F (fun i => splitCategory (x i))) -
      (∑ y, (bernoulliProductMass Finset.univ (fun i (_ : Fin 3) => q i / 4) y : ℂ) * F y)‖ ≤
      (9 / 8 : ℝ) * L * ∑ i, (q i) ^ 2 := by
  rw [sameSiteTwoSplitProduct_categories]
  have hq' (i : ι) (j : Fin 3) (_hj : j ∈ (Finset.univ : Finset (Fin 3))) :
      0 ≤ q i / 4 ∧ q i / 4 ≤ 1 := by
    constructor <;> linarith [(hq i).1, (hq i).2]
  have hs (i : ι) : (∑ _j ∈ (Finset.univ : Finset (Fin 3)), q i / 4) ≤ 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    linarith [(hq i).2]
  have h := categoricalProduct_test_bound Finset.univ (fun i (_ : Fin 3) => q i / 4)
    hq' hs F hL hF
  have he (i : ι) : (∑ _j ∈ (Finset.univ : Finset (Fin 3)), q i / 4) ^ 2 =
      (9 / 16 : ℝ) * (q i) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    ring
  simp_rw [he] at h
  rw [← Finset.mul_sum] at h
  convert h using 1
  ring

/-- Prime-site specialization with the explicit `9/8` coefficient. -/
theorem sameSiteTwoSplitPrime_test_bound (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (F : (Q → SplitCategories) → ℂ)
    {L : ℝ} (hL : 0 ≤ L) (hF : ∀ y, ‖F y‖ ≤ L) :
    ‖(∑ x, (sameSiteTwoSplitProductMass (fun p : Q => 1 / (p.val : ℝ)) x : ℂ) *
        F (fun p => splitCategory (x p))) -
      (∑ y, (bernoulliProductMass Finset.univ
        (fun (p : Q) (_ : Fin 3) => 1 / (4 * (p.val : ℝ))) y : ℂ) * F y)‖ ≤
      (9 / 8 : ℝ) * L * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
  have hq (p : Q) : 0 ≤ 1 / (p.val : ℝ) ∧ 1 / (p.val : ℝ) ≤ 1 := by
    have hp := hQ p.val p.property
    have hp0 : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) ≤ p.val := by exact_mod_cast hp.one_le
    exact ⟨by positivity, (div_le_one hp0).mpr hp1⟩
  have h := sameSiteTwoSplitProduct_test_bound (fun p : Q => 1 / (p.val : ℝ)) hq F hL hF
  have hs : (∑ p : Q, (1 / (p.val : ℝ)) ^ 2) = ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
    simp only [div_pow, one_pow]
    exact Finset.sum_coe_sort Q (fun p => 1 / (p : ℝ) ^ 2)
  rw [hs] at h
  simpa only [div_div, mul_comm _ (4 : ℝ)] using h

/-- Prime product corresponding to one of the common/exclusive categories. -/
noncomputable def categoryPrimeProduct (Q : Finset ℕ) (k : Fin 3)
    (y : Q → SplitCategories) : ℕ :=
  ∏ p, if k ∈ (y p).val then p.val else 1

/-- The independent model is `(C E₁, C E₂)`. If two categories contain the
same prime, its square is retained in the corresponding product. -/
noncomputable def independentSplitProducts (Q : Finset ℕ) (y : Q → SplitCategories) : ℕ × ℕ :=
  (categoryPrimeProduct Q 0 y * categoryPrimeProduct Q 1 y,
    categoryPrimeProduct Q 0 y * categoryPrimeProduct Q 2 y)

/-- Prime products of the actual pair of splits. -/
noncomputable def actualSplitProducts (Q : Finset ℕ) (x : Q → Bool × Bool) : ℕ × ℕ :=
  (∏ p, if (x p).1 then p.val else 1, ∏ p, if (x p).2 then p.val else 1)

theorem independentSplitProducts_of_actual (Q : Finset ℕ) (x : Q → Bool × Bool) :
    independentSplitProducts Q (fun p => splitCategory (x p)) = actualSplitProducts Q x := by
  apply Prod.ext
  · change (∏ p : Q, if (0 : Fin 3) ∈ (splitCategory (x p)).val then p.val else 1) *
        (∏ p : Q, if (1 : Fin 3) ∈ (splitCategory (x p)).val then p.val else 1) = _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rcases x p with ⟨a, b⟩
    cases a <;> cases b <;> simp [splitCategory]
  · change (∏ p : Q, if (0 : Fin 3) ∈ (splitCategory (x p)).val then p.val else 1) *
        (∏ p : Q, if (2 : Fin 3) ∈ (splitCategory (x p)).val then p.val else 1) = _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rcases x p with ⟨a, b⟩
    cases a <;> cases b <;> simp [splitCategory]

/-- The manuscript's two-split comparison, directly for arbitrary bounded
tests of the resulting pair of prime products. It applies in particular to
every pair of cells used in the step kernel. -/
theorem twoSplitPrimeProducts_test_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (F : ℕ × ℕ → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ z, ‖F z‖ ≤ L) :
    ‖(∑ x, (sameSiteTwoSplitProductMass (fun p : Q => 1 / (p.val : ℝ)) x : ℂ) *
        F (actualSplitProducts Q x)) -
      (∑ y, (bernoulliProductMass Finset.univ
        (fun (p : Q) (_ : Fin 3) => 1 / (4 * (p.val : ℝ))) y : ℂ) *
          F (independentSplitProducts Q y))‖ ≤
      (9 / 8 : ℝ) * L * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
  have h := sameSiteTwoSplitPrime_test_bound Q hQ (fun y => F (independentSplitProducts Q y))
    hL (fun y => hF _)
  simpa only [independentSplitProducts_of_actual] using h

open Classical in
/-- The cell-pair probability estimate used to compare step kernels. -/
theorem twoSplitPrimeProducts_cell_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (A B : Set ℕ) :
    |(∑ x, if (actualSplitProducts Q x).1 ∈ A ∧ (actualSplitProducts Q x).2 ∈ B then
        sameSiteTwoSplitProductMass (fun p : Q => 1 / (p.val : ℝ)) x else 0) -
      (∑ y, if (independentSplitProducts Q y).1 ∈ A ∧ (independentSplitProducts Q y).2 ∈ B then
        bernoulliProductMass Finset.univ
          (fun (p : Q) (_ : Fin 3) => 1 / (4 * (p.val : ℝ))) y else 0)| ≤
      (9 / 8 : ℝ) * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
  classical
  let F : ℕ × ℕ → ℂ := fun z => if z.1 ∈ A ∧ z.2 ∈ B then 1 else 0
  have hF (z : ℕ × ℕ) : ‖F z‖ ≤ (1 : ℝ) := by
    dsimp [F]
    split_ifs <;> norm_num
  have h := twoSplitPrimeProducts_test_bound Q hQ F (by norm_num : (0 : ℝ) ≤ 1) hF
  simp only [F, mul_ite, mul_one, mul_zero] at h
  have hc (P : Prop) [Decidable P] (a : ℝ) :
      (if P then (a : ℂ) else 0) = ((if P then a else 0 : ℝ) : ℂ) := by
    split_ifs <;> rfl
  simp_rw [hc] at h
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  simpa only [mul_one] using h

end JointDickman

end OAI
