import Mathlib

namespace OAI

noncomputable section

namespace Foulkes.PolynomialSpan
open MvPolynomial

variable {σ A : Type*} [CommRing A] [Algebra ℂ A]

def mapCoeffs (l : A →ₗ[ℂ] ℂ) (p : MvPolynomial σ A) : MvPolynomial σ ℂ :=
  ∑ d ∈ p.support, monomial d (l (p.coeff d))

@[simp] lemma coeff_mapCoeffs (l : A →ₗ[ℂ] ℂ) (p : MvPolynomial σ A) (d : σ →₀ ℕ) :
    (mapCoeffs l p).coeff d = l (p.coeff d) := by
  classical
  by_cases hd : d ∈ p.support
  · simp [mapCoeffs, coeff_monomial, hd]
  · simp [mapCoeffs, coeff_monomial, hd, notMem_support_iff.mp hd]

@[simp] lemma mapCoeffs_monomial (l : A →ₗ[ℂ] ℂ) (d : σ →₀ ℕ) (a : A) :
    mapCoeffs l (monomial d a) = monomial d (l a) := by
  classical
  ext e
  simp only [coeff_mapCoeffs, coeff_monomial]
  split_ifs <;> simp

@[simp] lemma mapCoeffs_add (l : A →ₗ[ℂ] ℂ) (p q : MvPolynomial σ A) :
    mapCoeffs l (p + q) = mapCoeffs l p + mapCoeffs l q := by
  ext d
  simp

lemma eval_mapCoeffs (l : A →ₗ[ℂ] ℂ) (p : MvPolynomial σ A) (x : σ → ℂ) :
    eval x (mapCoeffs l p) = l (eval (fun i => algebraMap ℂ A (x i)) p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial d a =>
    simp only [mapCoeffs_monomial, eval_monomial]
    have hh : d.prod (fun i k => (algebraMap ℂ A) (x i) ^ k) =
        algebraMap ℂ A (d.prod (fun i k => x i ^ k)) := by
      simp [Finsupp.prod, map_prod, map_pow]
    rw [hh, mul_comm a, ← Algebra.smul_def, map_smul]
    simp [mul_comm]

@[simp] lemma mapCoeffs_zero (l : A →ₗ[ℂ] ℂ) :
    mapCoeffs l (0 : MvPolynomial σ A) = 0 := by
  ext d
  simp

@[simp] lemma mapCoeffs_smul (l : A →ₗ[ℂ] ℂ) (c : ℂ) (p : MvPolynomial σ A) :
    mapCoeffs l (c • p) = c • mapCoeffs l p := by
  ext d
  simp

def mapCoeffsLM (l : A →ₗ[ℂ] ℂ) : MvPolynomial σ A →ₗ[ℂ] MvPolynomial σ ℂ where
  toFun := mapCoeffs l
  map_add' := mapCoeffs_add l
  map_smul' := mapCoeffs_smul l

@[simp] lemma mapCoeffs_sum {ι : Type*} (l : A →ₗ[ℂ] ℂ)
    (s : Finset ι) (p : ι → MvPolynomial σ A) :
    mapCoeffs l (∑ i ∈ s, p i) = ∑ i ∈ s, mapCoeffs l (p i) :=
  map_sum (mapCoeffsLM l) _ _

@[simp] lemma mapCoeffs_pderiv (l : A →ₗ[ℂ] ℂ) (i : σ) (p : MvPolynomial σ A) :
    mapCoeffs l (pderiv i p) = pderiv i (mapCoeffs l p) := by
  ext d
  simp only [coeff_mapCoeffs, coeff_pderiv]
  simpa [Algebra.smul_def, Nat.cast_add, mul_comm] using
    l.map_smul ((d i + 1 : ℕ) : ℂ) (p.coeff (d + Finsupp.single i 1))

@[simp] lemma mapCoeffs_X_mul (l : A →ₗ[ℂ] ℂ) (i : σ) (p : MvPolynomial σ A) :
    mapCoeffs l (X i * p) = X i * mapCoeffs l p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq]
  | monomial d a =>
    simp [X]

lemma homogeneous_mapCoeffs {M : Type*} [AddCommMonoid M]
    (l : A →ₗ[ℂ] ℂ) (w : σ → M) {p : MvPolynomial σ A} {d : M}
    (hp : p.IsWeightedHomogeneous w d) : (mapCoeffs l p).IsWeightedHomogeneous w d := by
  intro m hm
  exact hp (fun h => hm (by simp [h]))

theorem coeff_mem_of_evaluations (p : MvPolynomial σ A) (S : Submodule ℂ A)
    (h : ∀ x : σ → ℂ, eval (fun i => algebraMap ℂ A (x i)) p ∈ S)
    (d : σ →₀ ℕ) : p.coeff d ∈ S := by
  by_contra hd
  obtain ⟨l, hld, hlS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hd inferInstance
  have hl (a : A) (ha : a ∈ S) : l a = 0 := by
    have hh : l a ∈ S.map l := Submodule.mem_map.mpr ⟨a, ha, rfl⟩
    rwa [hlS, Submodule.mem_bot] at hh
  have hz : mapCoeffs l p = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [eval_mapCoeffs, hl _ (h x), map_zero]
  have hc := congrArg (fun polynomial => polynomial.coeff d) hz
  exact hld (by simpa using hc)

theorem prod_pow_mem_span_powers [Fintype σ] (a : σ → A) (d : σ →₀ ℕ)
    (n : ℕ) (hd : d.sum (fun _ k => k) = n) :
    d.prod (fun i k => a i ^ k) ∈
      Submodule.span ℂ (Set.range fun x : σ → ℂ => (∑ i, x i • a i) ^ n) := by
  classical
  let S := Submodule.span ℂ (Set.range fun x : σ → ℂ => (∑ i, x i • a i) ^ n)
  let G : MvPolynomial σ A := (∑ i, a i • X i) ^ n
  have heval (x : σ → ℂ) : eval (fun i => algebraMap ℂ A (x i)) G =
      (∑ i, x i • a i) ^ n := by
    simp [G, Algebra.smul_def, mul_comm]
  have hcoeff : G.coeff d ∈ S := coeff_mem_of_evaluations G S (fun x => by
    rw [heval]
    exact Submodule.subset_span ⟨x, rfl⟩) d
  change ((∑ i, a i • X i : MvPolynomial σ A) ^ n).coeff d ∈ S at hcoeff
  rw [coeff_linearCombination_X_pow_of_fintype, ite_eq_left hd] at hcoeff
  have hn : (d.multinomial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos (s := d.support) (f := d)))
  apply (Submodule.smul_mem_iff S hn).mp
  simpa only [Algebra.smul_def, map_natCast] using hcoeff

theorem homogeneous_eq_span_powers [Fintype σ] (n : ℕ) :
    homogeneousSubmodule σ ℂ n =
      Submodule.span ℂ (Set.range fun x : σ → ℂ => (∑ i, x i • X i) ^ n) := by
  classical
  apply le_antisymm
  · intro p hp
    induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => exact Submodule.zero_mem _
    | add p q hp hq ihp ihq => exact Submodule.add_mem _ ihp ihq
    | monomial d c hd =>
      rw [monomial_eq, ← MvPolynomial.smul_eq_C_mul]
      apply Submodule.smul_mem
      apply prod_pow_mem_span_powers
      simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using hd
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hh : (∑ i, x i • (X i : MvPolynomial σ ℂ)).IsHomogeneous 1 := by
      apply MvPolynomial.IsWeightedHomogeneous.sum
      intro i _
      exact (homogeneousSubmodule σ ℂ 1).smul_mem _ (isHomogeneous_X ℂ i)
    simpa using hh.pow n

theorem prod_mem_span_products {ι : Type*} [Fintype ι]
    {S : ι → Set A} {x : ι → A}
    (hx : ∀ i, x i ∈ Submodule.span ℂ (S i)) :
    (∏ i, x i) ∈ Submodule.span ℂ
      {p | ∃ y : ι → A, (∀ i, y i ∈ S i) ∧ ∏ i, y i = p} := by
  classical
  let T := Submodule.span ℂ
      {p | ∃ y : ι → A, (∀ i, y i ∈ S i) ∧ ∏ i, y i = p}
  have hspan : (∏ i, Submodule.span ℂ (S i)) ≤ T := by
    rw [Submodule.prod_span]
    apply Submodule.span_le.mpr
    intro p hp
    obtain ⟨y, hy, he⟩ := (Set.mem_fintype_prod S p).mp hp
    exact Submodule.subset_span ⟨y, hy, he⟩
  apply hspan
  have hprod (s : Finset ι) : (∏ i ∈ s, x i) ∈ ∏ i ∈ s, Submodule.span ℂ (S i) := by
    induction s using Finset.induction_on with
    | empty => simpa using (Submodule.algebraMap_mem (R := ℂ) (A := A) 1)
    | insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact Submodule.mul_mem_mul (hx i) ih
  exact hprod Finset.univ

theorem prod_mem_span_range {ι : Type*} [Fintype ι] {β : ι → Type*}
    (f : ∀ i, β i → A) {x : ι → A}
    (hx : ∀ i, x i ∈ Submodule.span ℂ (Set.range (f i))) :
    (∏ i, x i) ∈ Submodule.span ℂ (Set.range fun y : ∀ i, β i => ∏ i, f i (y i)) := by
  apply (Submodule.span_mono (t := Set.range fun y : ∀ i, β i => ∏ i, f i (y i))
    (by
      rintro p ⟨y, hy, rfl⟩
      choose z hz using hy
      exact ⟨z, by simp [hz]⟩)) (prod_mem_span_products hx)

end Foulkes.PolynomialSpan

end

end OAI
