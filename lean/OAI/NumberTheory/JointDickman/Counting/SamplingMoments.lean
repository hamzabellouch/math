import OAI.NumberTheory.JointDickman.Counting.SamplingConcentration

namespace OAI

/-!
# Finite-product moments for the sampling argument

All expectations here are finite sums with the actual independent site
masses. The variance identities, conditional moments, and absolute-error
estimates are proved directly; no moment or independence input is assumed.
-/

open Finset
open scoped BigOperators
open JointDickman.PublishedInputs

namespace JointDickman

section Expectation

variable {Ω : Type*} [Fintype Ω]

theorem finiteExpectation_add (w f g : Ω → ℝ) :
    finiteExpectation w (fun x => f x + g x) = finiteExpectation w f + finiteExpectation w g := by
  simp [finiteExpectation, mul_add, sum_add_distrib]

theorem finiteExpectation_sub (w f g : Ω → ℝ) :
    finiteExpectation w (fun x => f x - g x) = finiteExpectation w f - finiteExpectation w g := by
  simp [finiteExpectation, mul_sub, sum_sub_distrib]

theorem finiteExpectation_const_mul (w f : Ω → ℝ) (c : ℝ) :
    finiteExpectation w (fun x => c * f x) = c * finiteExpectation w f := by
  simp only [finiteExpectation, mul_sum]
  apply sum_congr rfl
  intro x _
  ring

theorem finiteExpectation_mul_const (w f : Ω → ℝ) (c : ℝ) :
    finiteExpectation w (fun x => f x * c) = finiteExpectation w f * c := by
  simp only [finiteExpectation, sum_mul, mul_assoc]

theorem finiteExpectation_const (w : Ω → ℝ) (hw : (∑ x, w x) = 1) (c : ℝ) :
    finiteExpectation w (fun _ => c) = c := by
  rw [finiteExpectation, ← sum_mul, hw, one_mul]

theorem finiteExpectation_sum {J : Type*} [Fintype J] (w : Ω → ℝ) (f : J → Ω → ℝ) :
    finiteExpectation w (fun x => ∑ j, f j x) = ∑ j, finiteExpectation w (f j) := by
  simp only [finiteExpectation, mul_sum]
  exact sum_comm

theorem finiteExpectation_mono (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    {f g : Ω → ℝ} (hfg : ∀ x, f x ≤ g x) : finiteExpectation w f ≤ finiteExpectation w g := by
  exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hw x)

theorem finiteExpectation_abs_le_sqrt_sq (w f : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hwone : (∑ x, w x) = 1) :
    finiteExpectation w (fun x => |f x|) ≤ Real.sqrt (finiteExpectation w (fun x => f x ^ 2)) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset Ω)
    (f := w) (g := fun x => w x * f x ^ 2) (r := fun x => w x * |f x|)
    (fun x _ => hw x) (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    (fun x _ => by rw [mul_pow, sq_abs]; ring_nf; exact le_rfl)
  rw [hwone, one_mul] at h
  exact Real.le_sqrt_of_sq_le h

theorem finiteExpectation_centered_sq (w f : Ω → ℝ) (hwone : (∑ x, w x) = 1) :
    finiteExpectation w (fun x => (f x - finiteExpectation w f) ^ 2) =
      finiteExpectation w (fun x => f x ^ 2) - (finiteExpectation w f) ^ 2 := by
  simp_rw [sub_sq, finiteExpectation_add, finiteExpectation_sub]
  rw [finiteExpectation_const w hwone, finiteExpectation_mul_const,
    finiteExpectation_const_mul]
  ring

end Expectation

section IndependentSites

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

omit [DecidableEq ι] [Fintype A] in
theorem siteProductMass_nonneg (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (x : ι → A) :
    0 ≤ siteProductMass p x := prod_nonneg fun i _ => hp i (x i)

/-- The finite sum-product identity supplies independence, with no probabilistic input. -/
theorem siteProduct_expectation_prod (p f : ι → A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => ∏ i, f i (x i)) =
      ∏ i, finiteExpectation (p i) (f i) := by
  simp only [finiteExpectation, siteProductMass, ← prod_mul_distrib]
  simpa using (prod_univ_sum (fun _ : ι => (univ : Finset A))
    (fun i a => p i a * f i a)).symm

theorem siteProductMass_sum (p : ι → A → ℝ) (hpone : ∀ i, ∑ a, p i a = 1) :
    (∑ x, siteProductMass p x) = 1 := by
  have h := siteProduct_expectation_prod p (fun _ _ => 1)
  simpa [finiteExpectation, hpone] using h

theorem siteProduct_expectation_coordinate (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (i : ι) (f : A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => f (x i)) = finiteExpectation (p i) f := by
  classical
  let g : ι → A → ℝ := fun j a => if j = i then f a else 1
  have hl (x : ι → A) : (∏ j, g j (x j)) = f (x i) := by simp [g]
  have hr : (∏ j, finiteExpectation (p j) (g j)) = finiteExpectation (p i) f := by
    rw [prod_eq_single i]
    · simp [g]
    · intro j _ hji
      simp [g, hji, finiteExpectation, hpone]
    · simp
  simpa only [hl, hr] using siteProduct_expectation_prod p g

theorem siteProduct_expectation_pair (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) {i j : ι} (hij : i ≠ j) (f g : A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => f (x i) * g (x j)) =
      finiteExpectation (p i) f * finiteExpectation (p j) g := by
  classical
  let h : ι → A → ℝ := fun k a => if k = i then f a else if k = j then g a else 1
  have hl (x : ι → A) : (∏ k, h k (x k)) = f (x i) * g (x j) := by
    rw [prod_eq_mul_of_mem i j (mem_univ _) (mem_univ _) hij]
    · simp [h, hij.symm]
    · intro k _ ⟨hki, hkj⟩
      simp [h, hki, hkj]
  have hr : (∏ k, finiteExpectation (p k) (h k)) =
      finiteExpectation (p i) f * finiteExpectation (p j) g := by
    rw [prod_eq_mul_of_mem i j (mem_univ _) (mem_univ _) hij]
    · simp [h, hij.symm]
    · intro k _ ⟨hki, hkj⟩
      simp [h, hki, hkj, finiteExpectation, hpone]
  simpa only [hl, hr] using siteProduct_expectation_prod p h

/-- Variance of a sum of independent centered single-site functions. -/
theorem siteProduct_centered_sum_sq (p f : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (hf : ∀ i, finiteExpectation (p i) (f i) = 0) :
    finiteExpectation (siteProductMass p) (fun x => (∑ i, f i (x i)) ^ 2) =
      ∑ i, finiteExpectation (p i) (fun a => f i a ^ 2) := by
  simp_rw [pow_two, sum_mul, mul_sum]
  rw [finiteExpectation_sum]
  simp_rw [finiteExpectation_sum]
  have hp (i j : ι) :
      finiteExpectation (siteProductMass p) (fun x => f i (x i) * f j (x j)) =
        if i = j then finiteExpectation (p i) (fun a => f i a * f i a) else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      exact siteProduct_expectation_coordinate p hpone i (fun a => f i a * f i a)
    · rw [siteProduct_expectation_pair p hpone hij, hf, hf, zero_mul, ite_eq_right hij]
  simp_rw [hp]
  simp

theorem siteProduct_sum_centered_sq (p f : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) :
    finiteExpectation (siteProductMass p)
      (fun x => ((∑ i, f i (x i)) - ∑ i, finiteExpectation (p i) (f i)) ^ 2) =
      ∑ i, (finiteExpectation (p i) (fun a => f i a ^ 2) -
        (finiteExpectation (p i) (f i)) ^ 2) := by
  have hc (i : ι) : finiteExpectation (p i)
      (fun a => f i a - finiteExpectation (p i) (f i)) = 0 := by
    rw [finiteExpectation_sub, finiteExpectation_const _ (hpone i), sub_self]
  have he (x : ι → A) : (∑ i, f i (x i)) - ∑ i, finiteExpectation (p i) (f i) =
      ∑ i, (f i (x i) - finiteExpectation (p i) (f i)) := by rw [sum_sub_distrib]
  simp_rw [he]
  rw [siteProduct_centered_sum_sq _ _ hpone hc]
  apply sum_congr rfl
  intro i _
  exact finiteExpectation_centered_sq _ _ (hpone i)

theorem siteProduct_sum_centered_sq_le (p f : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) :
    finiteExpectation (siteProductMass p)
      (fun x => ((∑ i, f i (x i)) - ∑ i, finiteExpectation (p i) (f i)) ^ 2) ≤
      ∑ i, finiteExpectation (p i) (fun a => f i a ^ 2) := by
  rw [siteProduct_sum_centered_sq p f hpone]
  exact sum_le_sum fun i _ => sub_le_self _ (sq_nonneg _)

theorem siteProduct_sum_abs_centered_le (p f : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1) :
    finiteExpectation (siteProductMass p)
      (fun x => |(∑ i, f i (x i)) - ∑ i, finiteExpectation (p i) (f i)|) ≤
      Real.sqrt (∑ i, finiteExpectation (p i) (fun a => f i a ^ 2)) := by
  exact (finiteExpectation_abs_le_sqrt_sq _ _ (siteProductMass_nonneg p hp)
    (siteProductMass_sum p hpone)).trans
      (Real.sqrt_le_sqrt (siteProduct_sum_centered_sq_le p f hpone))

theorem siteProduct_sum_mean (p f : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) :
    finiteExpectation (siteProductMass p) (fun x => ∑ i, f i (x i)) =
      ∑ i, finiteExpectation (p i) (f i) := by
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro i _
  exact siteProduct_expectation_coordinate p hpone i (f i)

theorem siteProduct_sum_sq_le (p f : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) :
    finiteExpectation (siteProductMass p) (fun x => (∑ i, f i (x i)) ^ 2) ≤
      (∑ i, finiteExpectation (p i) (f i)) ^ 2 +
        ∑ i, finiteExpectation (p i) (fun a => f i a ^ 2) := by
  have hvar := siteProduct_sum_centered_sq_le p f hpone
  have he := finiteExpectation_centered_sq (siteProductMass p)
    (fun x => ∑ i, f i (x i)) (siteProductMass_sum p hpone)
  rw [siteProduct_sum_mean p f hpone] at he
  linarith

end IndependentSites

section ConditionalSite

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- Reinsert one fixed site into a configuration on the other sites. -/
def insertSite (k : ι) (a : A) (x : {i : ι // i ≠ k} → A) (i : ι) : A :=
  if h : i = k then a else x ⟨i, h⟩

omit [Fintype ι] [Fintype A] in
@[simp] theorem insertSite_self (k : ι) (a : A) (x : {i : ι // i ≠ k} → A) :
    insertSite k a x k = a := by simp [insertSite]

omit [Fintype ι] [Fintype A] in
@[simp] theorem insertSite_other (k : ι) (a : A) (x : {i : ι // i ≠ k} → A)
    (i : {i : ι // i ≠ k}) : insertSite k a x i = x i := by simp [insertSite, i.property]

omit [Fintype ι] [Fintype A] in
theorem insertSite_restrict (k : ι) (x : ι → A) :
    insertSite k (x k) (fun i => x i) = x := by
  funext i
  by_cases hi : i = k <;> simp [insertSite, hi]

omit [Fintype A] in
theorem siteProductMass_insertSite (p : ι → A → ℝ) (k : ι) (a : A)
    (x : {i : ι // i ≠ k} → A) :
    siteProductMass p (insertSite k a x) =
      p k a * siteProductMass (fun i : {i : ι // i ≠ k} => p i) x := by
  unfold siteProductMass
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
  simp

/-- Exact finite disintegration at one site; no normalization is needed. -/
theorem siteProduct_disintegrate (p : ι → A → ℝ) (k : ι) (F : (ι → A) → ℝ) :
    finiteExpectation (siteProductMass p) F =
      finiteExpectation (p k) (fun a =>
        finiteExpectation (siteProductMass (fun i : {i : ι // i ≠ k} => p i))
          (fun x => F (insertSite k a x))) := by
  classical
  unfold finiteExpectation
  calc
    _ = ∑ z : A × ({i : ι // i ≠ k} → A),
        siteProductMass p (insertSite k z.1 z.2) * F (insertSite k z.1 z.2) := by
      refine Fintype.sum_equiv (Equiv.funSplitAt k A) _ _ ?_
      intro x
      change siteProductMass p x * F x =
        siteProductMass p (insertSite k (x k) (fun i => x i)) *
          F (insertSite k (x k) (fun i => x i))
      rw [insertSite_restrict]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [siteProductMass_insertSite, mul_sum, mul_assoc]

theorem siteProduct_expectation_two (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) {k j : ι} (hkj : k ≠ j) (F : A → A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => F (x k) (x j)) =
      finiteExpectation (p k) (fun a => finiteExpectation (p j) (F a)) := by
  rw [siteProduct_disintegrate p k]
  congr 1
  funext a
  have hj : j ≠ k := hkj.symm
  have hh := siteProduct_expectation_coordinate
    (fun i : {i : ι // i ≠ k} => p i) (fun i => hpone i) ⟨j, hj⟩ (F a)
  simpa [insertSite, hj] using hh

/-- A row evaluated on the independent site configuration. -/
noncomputable def siteRowSum (K : ι → ι → A → A → ℝ) (k : ι) (x : ι → A) : ℝ :=
  ∑ j, K k j (x k) (x j)

/-- Its conditional mean after fixing the row site. -/
noncomputable def siteRowMean (p : ι → A → ℝ) (K : ι → ι → A → A → ℝ)
    (k : ι) (a : A) : ℝ :=
  ∑ j : {j : ι // j ≠ k}, finiteExpectation (p j) (fun b => K k j a b)

/-- Integrated sum of squared row entries, with the row site also averaged. -/
noncomputable def siteRowSquareMass (p : ι → A → ℝ) (K : ι → ι → A → A → ℝ)
    (k : ι) : ℝ :=
  finiteExpectation (p k) (fun a =>
    ∑ j : {j : ι // j ≠ k}, finiteExpectation (p j) (fun b => K k j a b ^ 2))

omit [Fintype A] in
theorem siteRowSum_insertSite (K : ι → ι → A → A → ℝ)
    (hdiag : ∀ i a, K i i a a = 0) (k : ι) (a : A)
    (x : {i : ι // i ≠ k} → A) :
    siteRowSum K k (insertSite k a x) =
      ∑ j : {j : ι // j ≠ k}, K k j a (x j) := by
  unfold siteRowSum
  rw [Fintype.sum_eq_add_sum_subtype_ne _ k]
  simp [hdiag]

/-- The conditional notation is exactly the integrated squared row used
in the manuscript; no stronger pointwise second-moment premise is hidden. -/
theorem siteRowSquareMass_eq_sum_entries (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (K : ι → ι → A → A → ℝ)
    (hdiag : ∀ i a, K i i a a = 0) (k : ι) :
    siteRowSquareMass p K k =
      ∑ j, finiteExpectation (siteProductMass p) (fun x => K k j (x k) (x j) ^ 2) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ k]
  have hz : finiteExpectation (siteProductMass p) (fun x => K k k (x k) (x k) ^ 2) = 0 := by
    simp [finiteExpectation, hdiag]
  rw [hz, zero_add]
  unfold siteRowSquareMass
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro j _
  exact (siteProduct_expectation_two p hpone (Ne.symm j.property)
    (fun a b => K k j a b ^ 2)).symm

/-- The integrated conditional variance is bounded by the integrated
squared entries. There is no uniform conditional second-moment assumption. -/
theorem siteRow_centered_sq_le (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0) (k : ι) :
    finiteExpectation (siteProductMass p)
      (fun x => (siteRowSum K k x - siteRowMean p K k (x k)) ^ 2) ≤
        siteRowSquareMass p K k := by
  rw [siteProduct_disintegrate p k]
  unfold siteRowSquareMass
  apply finiteExpectation_mono (p k) (hp k)
  intro a
  simp only [siteRowSum_insertSite K hdiag, insertSite_self, siteRowMean]
  exact siteProduct_sum_centered_sq_le
    (fun i : {i : ι // i ≠ k} => p i) (fun j b => K k j a b) (fun i => hpone i)

theorem siteRow_abs_centered_le (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0) (k : ι) :
    finiteExpectation (siteProductMass p)
      (fun x => |siteRowSum K k x - siteRowMean p K k (x k)|) ≤
        Real.sqrt (siteRowSquareMass p K k) := by
  exact (finiteExpectation_abs_le_sqrt_sq _ _ (siteProductMass_nonneg p hp)
    (siteProductMass_sum p hpone)).trans
      (Real.sqrt_le_sqrt (siteRow_centered_sq_le p hp hpone K hdiag k))

theorem siteRow_abs_mean_le (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0) (k : ι) :
    finiteExpectation (siteProductMass p) (fun x => |siteRowSum K k x|) ≤
      finiteExpectation (p k) (fun a => |siteRowMean p K k a|) +
        Real.sqrt (siteRowSquareMass p K k) := by
  have htriangle (x : ι → A) : |siteRowSum K k x| ≤
      |siteRowSum K k x - siteRowMean p K k (x k)| + |siteRowMean p K k (x k)| := by
    simpa using abs_add_le (siteRowSum K k x - siteRowMean p K k (x k))
      (siteRowMean p K k (x k))
  have ht := finiteExpectation_mono (siteProductMass p) (siteProductMass_nonneg p hp) htriangle
  rw [finiteExpectation_add, siteProduct_expectation_coordinate p hpone k
    (fun a => |siteRowMean p K k a|)] at ht
  have he := siteRow_abs_centered_le p hp hpone K hdiag k
  linarith

/-- The row second moment follows from its conditional mean and the
integrated square mass, even when conditional square masses are large. -/
theorem siteRow_sq_le (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0)
    (k : ι) (C : ℝ) (hmean : ∀ a, |siteRowMean p K k a| ≤ C) :
    finiteExpectation (siteProductMass p) (fun x => siteRowSum K k x ^ 2) ≤
      C ^ 2 + siteRowSquareMass p K k := by
  rw [siteProduct_disintegrate p k]
  have hb (a : A) : finiteExpectation
      (siteProductMass (fun j : {j : ι // j ≠ k} => p j))
      (fun x => siteRowSum K k (insertSite k a x) ^ 2) ≤
        C ^ 2 + ∑ j : {j : ι // j ≠ k}, finiteExpectation (p j) (fun b => K k j a b ^ 2) := by
    simp only [siteRowSum_insertSite K hdiag]
    have hs := siteProduct_sum_sq_le (fun j : {j : ι // j ≠ k} => p j)
      (fun j b => K k j a b) (fun j => hpone j)
    have hm : siteRowMean p K k a ^ 2 ≤ C ^ 2 := by
      have hC : 0 ≤ C := (abs_nonneg _).trans (hmean a)
      nlinarith [sq_abs (siteRowMean p K k a),
        (sq_le_sq₀ (abs_nonneg (siteRowMean p K k a)) hC).mpr (hmean a)]
    change _ ≤ C ^ 2 + _
    change _ ≤ siteRowMean p K k a ^ 2 + _ at hs
    linarith
  calc
    _ ≤ finiteExpectation (p k) (fun a => C ^ 2 +
        ∑ j : {j : ι // j ≠ k}, finiteExpectation (p j) (fun b => K k j a b ^ 2)) :=
      finiteExpectation_mono (p k) (hp k) hb
    _ = _ := by rw [finiteExpectation_add, finiteExpectation_const _ (hpone k)]; rfl

/-- Sum of the conditional column-mean comparisons, in the normalization
before dividing by the number of sites. -/
theorem siteRow_total_abs_mean_le (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0) :
    finiteExpectation (siteProductMass p) (fun x => ∑ k, |siteRowSum K k x|) ≤
      (∑ k, finiteExpectation (p k) (fun a => |siteRowMean p K k a|)) +
        ∑ k, Real.sqrt (siteRowSquareMass p K k) := by
  rw [finiteExpectation_sum, ← sum_add_distrib]
  exact sum_le_sum fun k _ => siteRow_abs_mean_le p hp hpone K hdiag k

theorem siteRow_multiply_test_mean (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (K : ι → ι → A → A → ℝ)
    (hdiag : ∀ i a, K i i a a = 0) (k : ι) (h : A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => siteRowSum K k x * h (x k)) =
      finiteExpectation (p k) (fun a => siteRowMean p K k a * h a) := by
  rw [siteProduct_disintegrate p k]
  congr 1
  funext a
  simp only [siteRowSum_insertSite K hdiag, insertSite_self]
  rw [finiteExpectation_mul_const,
    siteProduct_sum_mean (fun j : {j : ι // j ≠ k} => p j)
      (fun j b => K k j a b) (fun j => hpone j)]
  rfl

/-- Fixed single-site tests suffice to control the mean after the sampled
columns have been fixed. The optimizing test is the sign of the conditional
column mean, not a function of the remaining full configuration. -/
theorem siteRow_total_abs_of_tests (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0) (C : ℝ)
    (htest : ∀ h : ι → A → ℝ, (∀ i a, |h i a| ≤ 1) →
      finiteExpectation (siteProductMass p) (fun x => ∑ k, siteRowSum K k x * h k (x k)) ≤ C) :
    finiteExpectation (siteProductMass p) (fun x => ∑ k, |siteRowSum K k x|) ≤
      C + ∑ k, Real.sqrt (siteRowSquareMass p K k) := by
  let h : ι → A → ℝ := fun k a => responseSign (siteRowMean p K k a)
  have hb := htest h (fun i a => by simp [h])
  have he : finiteExpectation (siteProductMass p)
      (fun x => ∑ k, siteRowSum K k x * h k (x k)) =
        ∑ k, finiteExpectation (p k) (fun a => |siteRowMean p K k a|) := by
    rw [finiteExpectation_sum]
    apply sum_congr rfl
    intro k _
    rw [siteRow_multiply_test_mean p hpone K hdiag k (h k)]
    simp only [h, mul_responseSign]
  rw [he] at hb
  have hh := siteRow_total_abs_mean_le p hp hpone K hdiag
  linarith

end ConditionalSite

end JointDickman

end OAI
