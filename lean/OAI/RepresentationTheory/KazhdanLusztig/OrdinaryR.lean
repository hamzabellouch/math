import OAI.RepresentationTheory.KazhdanLusztig.Hecke

namespace OAI

/-!
Construction of ordinary R-polynomials, left-simple recursion, degree bounds and inverse kernels.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}

noncomputable local instance : DecidableEq W := Classical.decEq W

namespace OrdinaryR

open LaurentPolynomial

noncomputable def variableUnit : (LaurentPolynomial ℤ)ˣ :=
  (LaurentPolynomial.isUnit_T (R := ℤ) 1).unit

@[simp] theorem variableUnit_val : (variableUnit : LaurentPolynomial ℤ) = T 1 :=
  (LaurentPolynomial.isUnit_T (R := ℤ) 1).unit_spec

/-- Polynomiality of the R-values is proved from the Hecke-derived recursion. -/
theorem rValue_polynomial (cs : CoxeterSystem M W) (x y : W) :
    ∃ p : ℤ[X], p.toLaurent = HeckeQ.rValue cs variableUnit x y := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
      ∃ p : ℤ[X], p.toLaurent = HeckeQ.rValue cs variableUnit x y by
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y = 1
    · subst y
      by_cases hx : x = 1
      · subst x
        exact ⟨1, by simp⟩
      · have hn : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x = 0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        exact ⟨0, by rw [HeckeQ.rValue_zero cs _ _ _ hn]; simp⟩
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
      obtain ⟨p, hp⟩ := ih _ hlt _ rfl x
      obtain ⟨r, hr⟩ := ih _ hlt _ rfl (cs.simple i * x)
      rw [HeckeQ.rValue_recursion cs variableUnit x y i hi]
      split_ifs
      · exact ⟨r, hr⟩
      · refine ⟨(X - 1) * p + X * r, ?_⟩
        simp [hp, hr]

noncomputable def polynomial (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  LaurentPolynomial.trunc (HeckeQ.rValue cs variableUnit x y)

@[simp] theorem toLaurent_polynomial (cs : CoxeterSystem M W) (x y : W) :
    (polynomial cs x y).toLaurent = HeckeQ.rValue cs variableUnit x y := by
  obtain ⟨p, hp⟩ := rValue_polynomial cs x y
  rw [polynomial, ← hp, Polynomial.trunc_toLaurent]

@[simp] theorem polynomial_diagonal (cs : CoxeterSystem M W) (x : W) :
    polynomial cs x x = 1 := by
  apply Polynomial.toLaurent_injective
  simp

theorem polynomial_zero (cs : CoxeterSystem M W) (x y : W)
    (hxy : ¬ BruhatLE cs x y) : polynomial cs x y = 0 := by
  apply Polynomial.toLaurent_injective
  simp [HeckeQ.rValue_zero cs _ x y hxy]

theorem polynomial_recursion (cs : CoxeterSystem M W) (x y : W) (i : B)
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    polynomial cs x y =
      if cs.length (cs.simple i * x) < cs.length x then
        polynomial cs (cs.simple i * x) (cs.simple i * y)
      else (X - 1) * polynomial cs x (cs.simple i * y) +
        X * polynomial cs (cs.simple i * x) (cs.simple i * y) := by
  apply Polynomial.toLaurent_injective
  rw [toLaurent_polynomial, HeckeQ.rValue_recursion cs variableUnit x y i hy]
  split_ifs <;> simp

/-- Specializing the honest integral polynomial recovers the Hecke R-value
at every unit parameter, not just the Laurent indeterminate. -/
theorem polynomial_eval {C : Type*} [CommRing C] (cs : CoxeterSystem M W)
    (q : Cˣ) (x y : W) :
    Polynomial.eval₂ (Int.castRingHom C) (q : C) (polynomial cs x y) =
      HeckeQ.rValue cs q x y := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
      Polynomial.eval₂ (Int.castRingHom C) (q : C) (polynomial cs x y) =
        HeckeQ.rValue cs q x y by
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y = 1
    · subst y
      by_cases hx : x = 1
      · subst x; simp
      · have hn : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x = 0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        rw [polynomial_zero cs _ _ hn, HeckeQ.rValue_zero cs _ _ _ hn]
        simp
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
      rw [polynomial_recursion cs x y i hi, HeckeQ.rValue_recursion cs q x y i hi]
      split_ifs
      · exact ih _ hlt _ rfl (cs.simple i * x)
      · simp [ih _ hlt _ rfl x, ih _ hlt _ rfl (cs.simple i * x)]

/-- The degree bound needed for the classical polynomial reciprocity. -/
theorem polynomial_degree (cs : CoxeterSystem M W) (x y : W) :
    (polynomial cs x y).natDegree ≤ rankDifference cs x y := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
      (polynomial cs x y).natDegree ≤ rankDifference cs x y by
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases hxy : BruhatLE cs x y
    · by_cases heq : x = y
      · subst x; simp [rankDifference]
      · have hlen := length_lt_of_bruhat_ne cs hxy heq
        have hone : y ≠ 1 := by
          intro h; subst y; simp at hlen
        obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hone
        have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
        have hylen : cs.length y = cs.length (cs.simple i * y) + 1 := by
          have := cs.length_simple_mul y i
          omega
        rw [polynomial_recursion cs x y i hi]
        by_cases hx : cs.length (cs.simple i * x) < cs.length x
        · rw [ite_eq_left hx]
          have hxlen : cs.length x = cs.length (cs.simple i * x) + 1 := by
            have := cs.length_simple_mul x i
            omega
          have hn := ih _ hlt _ rfl (cs.simple i * x)
          simpa [rankDifference, hylen, hxlen] using hn
        · rw [ite_eq_right hx]
          have hxlen : cs.length (cs.simple i * x) = cs.length x + 1 := by
            have := cs.length_simple_mul x i
            omega
          refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
          · have hn := ih _ hlt _ rfl x
            have hp : (X - 1 : ℤ[X]).natDegree ≤ 1 := by
              exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
            refine Polynomial.natDegree_mul_le.trans ?_
            dsimp [rankDifference] at hn ⊢
            omega
          · by_cases hsy : BruhatLE cs (cs.simple i * x) (cs.simple i * y)
            · have hl := length_le_of_bruhat cs hsy
              have hn := ih _ hlt _ rfl (cs.simple i * x)
              refine Polynomial.natDegree_mul_le.trans ?_
              simp only [Polynomial.natDegree_X]
              dsimp [rankDifference] at hn ⊢
              omega
            · rw [polynomial_zero cs _ _ hsy, mul_zero]
              simp
    · rw [polynomial_zero cs _ _ hxy]
      simp

@[simp] theorem eval_variableUnit (p : ℤ[X]) :
    Polynomial.eval₂ (Int.castRingHom (LaurentPolynomial ℤ))
      (variableUnit : LaurentPolynomial ℤ) p = p.toLaurent := by
  have h : Polynomial.eval₂RingHom (Int.castRingHom (LaurentPolynomial ℤ))
      (variableUnit : LaurentPolynomial ℤ) = Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.toLaurent_C]
      exact (map_intCast (LaurentPolynomial.C : ℤ →+* LaurentPolynomial ℤ) a).symm
    · simp
  exact congrArg (fun f : ℤ[X] →+* LaurentPolynomial ℤ => f p) h

/-- Polynomial R is a kernel for the length-reflection involution. -/
theorem polynomial_kernel (cs : CoxeterSystem M W) (x y : W) :
    ∑ z ∈ lowerFinset cs y,
      polynomial cs x z * reflect (rankDifference cs z y) (polynomial cs z y) =
      if x = y then 1 else 0 := by
  classical
  apply Polynomial.toLaurent_injective
  rw [map_sum]
  have h := HeckeQ.rValue_inverse cs variableUnit x y
  have heq : ∀ z ∈ lowerFinset cs y,
      (polynomial cs x z * reflect (rankDifference cs z y) (polynomial cs z y)).toLaurent =
      HeckeQ.rValue cs variableUnit x z *
        (variableUnit : LaurentPolynomial ℤ) ^ cs.length y *
        (↑variableUnit⁻¹ : LaurentPolynomial ℤ) ^ cs.length z *
        HeckeQ.rValue cs variableUnit⁻¹ z y := by
    intro z hz
    have hle := length_le_of_bruhat cs ((mem_lowerFinset cs y z).mp hz)
    rw [map_mul, toLaurent_polynomial, ← eval_variableUnit,
      eval₂_reflect_unit _ _ _ (polynomial_degree cs z y), polynomial_eval]
    have hlen : cs.length y = rankDifference cs z y + cs.length z := by
      dsimp [rankDifference]; omega
    rw [hlen, pow_add]
    simp only [mul_assoc]
    rw [← mul_assoc ((variableUnit : LaurentPolynomial ℤ) ^ cs.length z),
      ← mul_pow, Units.mul_inv, one_pow, one_mul]
  rw [Finset.sum_congr rfl heq, h]
  split_ifs <;> simp

end OrdinaryR

noncomputable def properIntervalFinset (cs : CoxeterSystem M W) (x y : W) : Finset W := by
  classical
  exact (lowerFinset cs y).filter (fun z => BruhatLE cs x z ∧ x ≠ z)

@[simp] theorem mem_properIntervalFinset (cs : CoxeterSystem M W) (x y z : W) :
    z ∈ properIntervalFinset cs x y ↔ BruhatLE cs z y ∧ BruhatLE cs x z ∧ x ≠ z := by
  classical
  simp [properIntervalFinset]

theorem rankDifference_add (cs : CoxeterSystem M W) {x z y : W}
    (hxz : BruhatLE cs x z) (hzy : BruhatLE cs z y) :
    rankDifference cs x y = rankDifference cs x z + rankDifference cs z y := by
  have := length_le_of_bruhat cs hxz
  have := length_le_of_bruhat cs hzy
  dsimp [rankDifference]
  omega

theorem reflect_finset_sum {A : Type*} (s : Finset A) (d : ℕ) (f : A → ℤ[X]) :
    reflect d (∑ a ∈ s, f a) = ∑ a ∈ s, reflect d (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, reflect_add, ih]

namespace OrdinaryR

theorem polynomial_kernel_reverse (cs : CoxeterSystem M W) (x y : W) :
    ∑ z ∈ lowerFinset cs y,
      reflect (rankDifference cs x z) (polynomial cs x z) * polynomial cs z y =
      if x = y then 1 else 0 := by
  classical
  by_cases hxy : BruhatLE cs x y
  · have h := congrArg (reflect (rankDifference cs x y)) (polynomial_kernel cs x y)
    rw [reflect_finset_sum] at h
    have heq : ∀ z ∈ lowerFinset cs y,
        reflect (rankDifference cs x y)
          (polynomial cs x z * reflect (rankDifference cs z y) (polynomial cs z y)) =
        reflect (rankDifference cs x z) (polynomial cs x z) * polynomial cs z y := by
      intro z hz
      by_cases hxz : BruhatLE cs x z
      · rw [rankDifference_add cs hxz ((mem_lowerFinset cs y z).mp hz),
          reflect_mul _ _ (polynomial_degree cs x z)
            (Polynomial.natDegree_reflect_le.trans (max_le le_rfl (polynomial_degree cs z y))), reflect_reflect]
      · rw [polynomial_zero cs x z hxz, zero_mul, reflect_zero, reflect_zero, zero_mul]
    rw [Finset.sum_congr rfl heq] at h
    convert h using 1
    split_ifs with he
    · subst y
      simp [rankDifference]
    · simp
  · rw [ite_eq_right (by intro he; subst y; exact hxy (bruhat_refl cs x))]
    apply Finset.sum_eq_zero
    intro z hz
    have hxz : ¬BruhatLE cs x z := fun hxz =>
      hxy (bruhat_trans cs hxz ((mem_lowerFinset cs y z).mp hz))
    rw [polynomial_zero cs x z hxz, reflect_zero, zero_mul]

end OrdinaryR

theorem sum_proper_eq_sub (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) (f : W → ℤ[X])
    (hzero : ∀ z, ¬BruhatLE cs x z → f z = 0) :
    ∑ z ∈ properIntervalFinset cs x y, f z =
      (∑ z ∈ lowerFinset cs y, f z) - f x := by
  classical
  rw [← Finset.sum_erase_eq_sub ((mem_lowerFinset cs y x).mpr hxy)]
  apply Finset.sum_subset
  · intro z hz
    have hz := (mem_properIntervalFinset cs x y z).mp hz
    exact Finset.mem_erase.mpr ⟨Ne.symm hz.2.2, (mem_lowerFinset cs y z).mpr hz.1⟩
  · intro z hz hnot
    apply hzero
    intro hxz
    have hz := Finset.mem_erase.mp hz
    exact hnot ((mem_properIntervalFinset cs x y z).mpr
      ⟨(mem_lowerFinset cs y z).mp hz.2, hxz, Ne.symm hz.1⟩)


end KLInvariance
end

end OAI
