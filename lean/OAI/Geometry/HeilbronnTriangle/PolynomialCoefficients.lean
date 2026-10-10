import Mathlib

namespace OAI

noncomputable section

namespace Problem355.PolynomialCoefficients

open MvPolynomial

variable {σ R : Type*}

def combine (a b c : σ →₀ ℕ) : (Fin 3 × σ) →₀ ℕ :=
  (Finsupp.equivFunOnFinite.symm ![a, b, c]).uncurry

@[simp] lemma combine_apply_zero (a b c : σ →₀ ℕ) (i : σ) :
    combine a b c (0, i) = a i := rfl

@[simp] lemma combine_apply_one (a b c : σ →₀ ℕ) (i : σ) :
    combine a b c (1, i) = b i := rfl

@[simp] lemma combine_apply_two (a b c : σ →₀ ℕ) (i : σ) :
    combine a b c (2, i) = c i := rfl

lemma combine_injective : Function.Injective
    (fun t : (σ →₀ ℕ) × (σ →₀ ℕ) × (σ →₀ ℕ) => combine t.1 t.2.1 t.2.2) := by
  intro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have ha : a = a' := by
    ext i
    exact congrArg (fun d => d (0, i)) h
  have hb : b = b' := by
    ext i
    exact congrArg (fun d => d (1, i)) h
  have hc : c = c' := by
    ext i
    exact congrArg (fun d => d (2, i)) h
  simp only [Prod.mk.injEq]
  exact ⟨ha, hb, hc⟩

def groupSwap (i j : Fin 3) : Equiv.Perm (Fin 3 × σ) :=
  Equiv.prodCongr (Equiv.swap i j) (Equiv.refl σ)

@[simp] lemma combine_map_swap01 (a b c : σ →₀ ℕ) :
    (combine a b c).mapDomain (groupSwap (σ := σ) 0 1) = combine b a c := by
  ext ⟨i, s⟩
  rw [Finsupp.mapDomain_equiv_apply]
  fin_cases i <;> simp [groupSwap, combine, Finsupp.uncurry_apply, Equiv.swap_apply_def]

@[simp] lemma combine_map_swap12 (a b c : σ →₀ ℕ) :
    (combine a b c).mapDomain (groupSwap (σ := σ) 1 2) = combine a c b := by
  ext ⟨i, s⟩
  rw [Finsupp.mapDomain_equiv_apply]
  fin_cases i <;> simp [groupSwap, combine, Finsupp.uncurry_apply, Equiv.swap_apply_def]

lemma combine_curry (d : (Fin 3 × σ) →₀ ℕ) :
    combine (d.curry 0) (d.curry 1) (d.curry 2) = d := by
  ext ⟨i, s⟩
  fin_cases i <;> rfl

lemma combine_index_injective {ι : Type*} (e : ι → σ →₀ ℕ)
    (he : Function.Injective e) : Function.Injective
      (fun t : ι × ι × ι => combine (e t.1) (e t.2.1) (e t.2.2)) := by
  intro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h' : (e a, e b, e c) = (e a', e b', e c') :=
    @combine_injective σ (e a, e b, e c) (e a', e b', e c') h
  simp only [Prod.mk.injEq] at h' ⊢
  exact ⟨he h'.1, he h'.2.1, he h'.2.2⟩

lemma curry_degree_eq_weight [Fintype σ] (d : (Fin 3 × σ) →₀ ℕ) (j : Fin 3) :
    (d.curry j).degree =
      Finsupp.weight (fun v : Fin 3 × σ => if v.1 = j then (1 : ℕ) else 0) d := by
  classical
  rw [Finsupp.degree_eq_sum, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (by intro i; simp), Fintype.sum_prod_type]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

section Expansion

variable [CommSemiring R]

lemma expansion_of_support {ι : Type*} [Fintype ι]
    (P : MvPolynomial σ R) (e : ι → σ →₀ ℕ) (he : Function.Injective e)
    (hP : ∀ d ∈ P.support, d ∈ Set.range e) :
    P = ∑ i, monomial (e i) (P.coeff (e i)) := by
  classical
  calc
    P = ∑ d ∈ P.support, monomial d (P.coeff d) := P.as_sum
    _ = ∑ d ∈ Finset.univ.image e, monomial d (P.coeff d) := by
      apply Finset.sum_subset
      · intro d hd
        obtain ⟨i, rfl⟩ := hP d hd
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · intro d _ hd
        simp [MvPolynomial.notMem_support_iff.mp hd]
    _ = _ := Finset.sum_image (fun i _ j _ hij => he hij)

lemma three_group_expansion {ι : Type*} [Fintype ι]
    (P : MvPolynomial (Fin 3 × σ) R) (e : ι → σ →₀ ℕ)
    (he : Function.Injective e)
    (hP : ∀ d ∈ P.support, ∀ j : Fin 3, d.curry j ∈ Set.range e) :
    P = ∑ a, ∑ b, ∑ c,
      monomial (combine (e a) (e b) (e c))
        (P.coeff (combine (e a) (e b) (e c))) := by
  classical
  have hsupport : ∀ d ∈ P.support, d ∈ Set.range
      (fun t : ι × ι × ι => combine (e t.1) (e t.2.1) (e t.2.2)) := by
    intro d hd
    obtain ⟨a, ha⟩ := hP d hd 0
    obtain ⟨b, hb⟩ := hP d hd 1
    obtain ⟨c, hc⟩ := hP d hd 2
    refine ⟨(a, b, c), ?_⟩
    simp only [ha, hb, hc]
    exact combine_curry d
  simpa only [Fintype.sum_prod_type] using
    expansion_of_support P _ (combine_index_injective e he) hsupport

lemma three_group_expansion_of_degree {ι : Type*} [Fintype ι] (d : ℕ)
    (P : MvPolynomial (Fin 3 × σ) R)
    (e : ι ≃ {a : σ →₀ ℕ // a.degree = d})
    (hP : ∀ a ∈ P.support, ∀ j : Fin 3, (a.curry j).degree = d) :
    P = ∑ a, ∑ b, ∑ c,
      monomial (combine (e a).val (e b).val (e c).val)
        (P.coeff (combine (e a).val (e b).val (e c).val)) := by
  apply three_group_expansion P (fun i => (e i).val)
    (Subtype.val_injective.comp e.injective)
  intro a ha j
  obtain ⟨i, hi⟩ := e.surjective ⟨a.curry j, hP a ha j⟩
  exact ⟨i, congrArg Subtype.val hi⟩

def inGroup (j : Fin 3) (a : σ →₀ ℕ) : (Fin 3 × σ) →₀ ℕ :=
  a.mapDomain (fun s => (j, s))

@[simp] lemma inGroup_apply_same (j : Fin 3) (a : σ →₀ ℕ) (s : σ) :
    inGroup j a (j, s) = a s :=
  Finsupp.mapDomain_apply_of_injective (fun _ _ h => (Prod.mk.inj h).2) _ _

lemma inGroup_apply_ne (i j : Fin 3) (hij : i ≠ j) (a : σ →₀ ℕ) (s : σ) :
    inGroup i a (j, s) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨t, ht⟩
  exact hij (Prod.mk.inj ht).1

lemma combine_eq_add (a b c : σ →₀ ℕ) :
    combine a b c = inGroup 0 a + inGroup 1 b + inGroup 2 c := by
  ext ⟨i, s⟩
  fin_cases i <;>
    simp [inGroup_apply_ne, show (0 : Fin 3) ≠ 1 by decide,
      show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide,
      show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide]

def groupMonomial (j : Fin 3) (a : σ →₀ ℕ) : MvPolynomial (Fin 3 × σ) R :=
  rename (fun s => (j, s)) (monomial a 1)

lemma groupMonomial_eq (j : Fin 3) (a : σ →₀ ℕ) :
    groupMonomial (R := R) j a = monomial (inGroup j a) 1 := by
  rw [groupMonomial, rename_monomial, inGroup]

lemma monomial_combine (a b c : σ →₀ ℕ) (r : R) :
    monomial (combine a b c) r =
      C r * groupMonomial 0 a * groupMonomial 1 b * groupMonomial 2 c := by
  rw [combine_eq_add]
  simp only [groupMonomial_eq, C_mul_monomial, monomial_mul_monomial, mul_one]

lemma eval_monomial_combine (a b c : σ →₀ ℕ) (r : R)
    (x : Fin 3 × σ → R) :
    eval x (monomial (combine a b c) r) =
      r * eval (fun s => x (0, s)) (monomial a 1) *
        eval (fun s => x (1, s)) (monomial b 1) *
        eval (fun s => x (2, s)) (monomial c 1) := by
  rw [monomial_combine]
  simp [groupMonomial, eval_rename, Function.comp_def]

lemma eval_three_group_expansion {ι : Type*} [Fintype ι]
    (P : MvPolynomial (Fin 3 × σ) R) (e : ι → σ →₀ ℕ)
    (he : Function.Injective e)
    (hP : ∀ d ∈ P.support, ∀ j : Fin 3, d.curry j ∈ Set.range e)
    (x : Fin 3 × σ → R) :
    eval x P = ∑ a, ∑ b, ∑ c,
      P.coeff (combine (e a) (e b) (e c)) *
        eval (fun s => x (0, s)) (monomial (e a) 1) *
        eval (fun s => x (1, s)) (monomial (e b) 1) *
        eval (fun s => x (2, s)) (monomial (e c) 1) := by
  conv_lhs => rw [three_group_expansion P e he hP]
  simp only [map_sum, eval_monomial_combine]

end Expansion

variable [CommRing R]

lemma coeff_mapDomain_eq_neg (e : Equiv.Perm σ) (P : MvPolynomial σ R)
    (hP : rename e P = -P) (d : σ →₀ ℕ) :
    P.coeff (d.mapDomain e) = -P.coeff d := by
  have h := coeff_rename_mapDomain e e.injective P d
  rw [hP, coeff_neg] at h
  exact neg_eq_iff_eq_neg.mp h

def tensorCoeff (P : MvPolynomial (Fin 3 × σ) R) (a b c : σ →₀ ℕ) : R :=
  P.coeff (combine a b c)

lemma tensorCoeff_swap01 (P : MvPolynomial (Fin 3 × σ) R)
    (hP : rename (groupSwap (σ := σ) 0 1) P = -P) (a b c : σ →₀ ℕ) :
    tensorCoeff P b a c = -tensorCoeff P a b c := by
  simpa [tensorCoeff] using
    coeff_mapDomain_eq_neg (groupSwap 0 1) P hP (combine a b c)

lemma tensorCoeff_swap12 (P : MvPolynomial (Fin 3 × σ) R)
    (hP : rename (groupSwap (σ := σ) 1 2) P = -P) (a b c : σ →₀ ℕ) :
    tensorCoeff P a c b = -tensorCoeff P a b c := by
  simpa [tensorCoeff] using
    coeff_mapDomain_eq_neg (groupSwap 1 2) P hP (combine a b c)

end Problem355.PolynomialCoefficients

end

end OAI
