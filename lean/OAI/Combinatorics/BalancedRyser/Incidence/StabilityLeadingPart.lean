import Mathlib.Algebra.Polynomial.Homogenize
import OAI.Combinatorics.BalancedRyser.Incidence.RedeiPolynomial

namespace OAI

namespace Balanced.StabilityPolynomial

open MvPolynomial
open scoped BigOperators

variable {F σ : Type*} [Field F]

theorem homogeneousComponent_mul_of_degree_le
    (p r : MvPolynomial σ F) (m n : ℕ)
    (hp : p.totalDegree ≤ m) (hr : r.totalDegree ≤ n) :
    homogeneousComponent (m + n) (p * r) =
      homogeneousComponent m p * homogeneousComponent n r := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  by_cases hd : d.degree = m + n
  · rw [ite_eq_left hd]
    apply Finset.sum_congr rfl
    intro x hx
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases hpx : p.coeff x.1 = 0
    · simp [hpx]
    by_cases hrx : r.coeff x.2 = 0
    · simp [hrx]
    have hpm : x.1.degree ≤ m :=
      (le_totalDegree (mem_support_iff.mpr hpx)).trans hp
    have hrn : x.2.degree ≤ n :=
      (le_totalDegree (mem_support_iff.mpr hrx)).trans hr
    have hsum : x.1.degree + x.2.degree = m + n := by
      rw [← map_add, Finset.mem_antidiagonal.mp hx, hd]
    have hm : x.1.degree = m := by omega
    have hn : x.2.degree = n := by omega
    simp [hm, hn]
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    have hsum : x.1.degree + x.2.degree = d.degree := by
      rw [← map_add, Finset.mem_antidiagonal.mp hx]
    by_cases hm : x.1.degree = m
    · have hn : x.2.degree ≠ n := by omega
      simp [hn]
    · simp [hm]

theorem topHomogeneousComponent_ne_zero (p : MvPolynomial σ F) (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  have hs : p.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hp)
  obtain ⟨d, hd, heq⟩ := p.support.exists_mem_eq_sup hs Finsupp.degree
  have hdeg : d.degree = p.totalDegree := heq.symm
  intro hz
  have hc := congrArg (fun polynomial : MvPolynomial σ F => polynomial.coeff d) hz
  rw [coeff_homogeneousComponent, ite_eq_left hdeg, AddMonoidAlgebra.coeff_zero] at hc
  exact (mem_support_iff.mp hd) hc

noncomputable def dehomogenize : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval ![Polynomial.X, 1]

theorem dehomogenize_ne_zero_of_homogeneous
    {p : MvPolynomial (Fin 2) F} {n : ℕ}
    (hhom : p.IsHomogeneous n) (hp : p ≠ 0) :
    dehomogenize p ≠ 0 := by
  intro hz
  have h := Polynomial.homogenize_eq_of_isHomogeneous hhom hz
  rw [Polynomial.homogenize_zero] at h
  exact hp h.symm

theorem natDegree_dehomogenize_le (p : MvPolynomial (Fin 2) F) :
    (dehomogenize p).natDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hbound := le_totalDegree (p := p) hd
  have hmono : dehomogenize (monomial d (p.coeff d)) =
      Polynomial.C (p.coeff d) * Polynomial.X ^ d 0 := by
    simp [dehomogenize, aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]
  rw [hmono]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [Polynomial.natDegree_X_pow]
  have hsum : d.sum (fun _ e => e) = d 0 + d 1 := by
    rw [Finsupp.sum_fintype]
    · simp [Fin.sum_univ_two]
    · simp
  rw [hsum] at hbound
  omega

noncomputable def leadingSpecialization (n : ℕ) (p : MvPolynomial (Fin 2) F) :
    Polynomial F := dehomogenize (homogeneousComponent n p)

theorem natDegree_leadingSpecialization_le (n : ℕ) (p : MvPolynomial (Fin 2) F) :
    (leadingSpecialization n p).natDegree ≤ n :=
  (natDegree_dehomogenize_le _).trans (homogeneousComponent_isHomogeneous n p).totalDegree_le

theorem leadingSpecialization_ne_zero (p : MvPolynomial (Fin 2) F) (hp : p ≠ 0) :
    leadingSpecialization p.totalDegree p ≠ 0 :=
  dehomogenize_ne_zero_of_homogeneous (homogeneousComponent_isHomogeneous _ _)
    (topHomogeneousComponent_ne_zero p hp)

theorem leadingSpecialization_mul_of_degree_le
    (p r : MvPolynomial (Fin 2) F) (m n : ℕ)
    (hp : p.totalDegree ≤ m) (hr : r.totalDegree ≤ n) :
    leadingSpecialization (m + n) (p * r) =
      leadingSpecialization m p * leadingSpecialization n r := by
  simp only [leadingSpecialization,
    homogeneousComponent_mul_of_degree_le p r m n hp hr, map_mul]

theorem leadingSpecialization_redeiFactor (p : Point F) :
    leadingSpecialization 1 (redeiFactor p) = Polynomial.X + Polynomial.C p.1 := by
  have hhom : (X (R := F) 0 + C p.1 * X 1 : MvPolynomial (Fin 2) F).IsHomogeneous 1 :=
    (isHomogeneous_X F 0).add (isHomogeneous_C_mul_X p.1 1)
  simp only [leadingSpecialization, redeiFactor, map_sub,
    homogeneousComponent_eq_self hhom,
    homogeneousComponent_of_mem (isHomogeneous_C (Fin 2) p.2)]
  simp [dehomogenize]

noncomputable def redeiLeadingProduct (U : Finset (Point F)) : Polynomial F :=
  ∏ p ∈ U, (Polynomial.X + Polynomial.C p.1)

theorem leadingSpecialization_redeiPolynomial (U : Finset (Point F)) :
    leadingSpecialization U.card (redeiPolynomial U) = redeiLeadingProduct U := by
  classical
  induction U using Finset.induction_on with
  | empty => simp [leadingSpecialization, redeiPolynomial, redeiLeadingProduct, dehomogenize]
  | @insert p U hp ih =>
    rw [redeiPolynomial, Finset.prod_insert hp]
    change leadingSpecialization (insert p U).card (redeiFactor p * redeiPolynomial U) = _
    rw [Finset.card_insert_of_notMem hp, Nat.add_comm U.card 1,
      leadingSpecialization_mul_of_degree_le _ _ 1 U.card
        (redeiFactor_totalDegree_le p) (redeiPolynomial_totalDegree_le U),
      leadingSpecialization_redeiFactor, ih]
    simp [redeiLeadingProduct, hp]

theorem homogeneousComponent_grid_term (i : Fin 2) (q s : ℕ) (hq : 1 < q)
    (f : MvPolynomial (Fin 2) F) (hf : f.totalDegree ≤ s) :
    homogeneousComponent (q + s) ((X i ^ q - X i) * f) =
      X i ^ q * homogeneousComponent s f := by
  rw [sub_mul, map_sub,
    homogeneousComponent_mul_of_degree_le _ _ q s (by simp) hf,
    homogeneousComponent_eq_self (isHomogeneous_X_pow i q)]
  have hlow : (X i * f).totalDegree < q + s := by
    apply (totalDegree_mul _ _).trans_lt
    simp only [totalDegree_X]
    omega
  rw [homogeneousComponent_eq_zero _ _ hlow, sub_zero]

theorem leadingSpecialization_grid_term (i : Fin 2) (q s : ℕ) (hq : 1 < q)
    (f : MvPolynomial (Fin 2) F) (hf : f.totalDegree ≤ s) :
    leadingSpecialization (q + s) ((X i ^ q - X i) * f) =
      (dehomogenize (X i)) ^ q * leadingSpecialization s f := by
  simp only [leadingSpecialization, homogeneousComponent_grid_term i q s hq f hf,
    map_mul, map_pow]

theorem redei_leading_identity
    (U : Finset (Point F)) (a f g : MvPolynomial (Fin 2) F) (q : ℕ)
    (hq : 1 < q) (hn : q ≤ U.card + a.totalDegree)
    (hf : f.totalDegree ≤ U.card + a.totalDegree - q)
    (hg : g.totalDegree ≤ U.card + a.totalDegree - q)
    (hid : redeiPolynomial U * a = (X 0 ^ q - X 0) * f + (X 1 ^ q - X 1) * g) :
    redeiLeadingProduct U * leadingSpecialization a.totalDegree a =
      Polynomial.X ^ q * leadingSpecialization (U.card + a.totalDegree - q) f +
        leadingSpecialization (U.card + a.totalDegree - q) g := by
  have hsum : q + (U.card + a.totalDegree - q) = U.card + a.totalDegree :=
    Nat.add_sub_of_le hn
  have h := congrArg (leadingSpecialization (U.card + a.totalDegree)) hid
  rw [leadingSpecialization_mul_of_degree_le _ _ U.card a.totalDegree
    (redeiPolynomial_totalDegree_le U) le_rfl, leadingSpecialization_redeiPolynomial] at h
  have hadd (p r : MvPolynomial (Fin 2) F) (n : ℕ) :
      leadingSpecialization n (p + r) = leadingSpecialization n p + leadingSpecialization n r := by
    simp only [leadingSpecialization, map_add]
  rw [hadd, ← hsum, leadingSpecialization_grid_term 0 q _ hq f hf,
    leadingSpecialization_grid_term 1 q _ hq g hg] at h
  simpa [dehomogenize] using h

variable [Fintype F]

theorem card_le_totalDegree_of_grid_vanishing {τ : Type*} [Finite τ]
    (p : MvPolynomial τ F) (hp : p ≠ 0)
    (hvan : ∀ x : τ → F, eval x p = 0) :
    Fintype.card F ≤ p.totalDegree := by
  classical
  by_contra hn
  have hlt : p.totalDegree < Fintype.card F := Nat.lt_of_not_ge hn
  apply hp
  apply eq_zero_of_eval_zero_at_prod_finset p (fun _ => Finset.univ)
  · intro i
    simpa only [Finset.card_univ] using (degreeOf_le_totalDegree p i).trans_lt hlt
  · intro x _
    exact hvan x

theorem card_le_redei_auxiliary_degree
    (U : Finset (Point F)) (a : MvPolynomial (Fin 2) F) (ha : a ≠ 0)
    (hvan : ∀ z : Fin 2 → F,
      (∀ p ∈ U, ¬ OnLine p (some (z 1), z 0)) → eval z a = 0) :
    Fintype.card F ≤ U.card + a.totalDegree := by
  have h := card_le_totalDegree_of_grid_vanishing (redeiPolynomial U * a)
    (mul_ne_zero (redeiPolynomial_ne_zero U) ha) (redei_mul_vanishes U a hvan)
  rwa [redei_mul_totalDegree U a ha] at h

theorem exists_redei_leading_identity (U : Finset (Point F)) (d : ℕ)
    (hsize : 2 * (nonverticalSkewCodes U).card < (d + 1) * (d + 2)) :
    ∃ A f g : Polynomial F,
      A ≠ 0 ∧ A.natDegree ≤ d ∧
      f.natDegree ≤ U.card + d - Fintype.card F ∧
      g.natDegree ≤ U.card + d - Fintype.card F ∧
      redeiLeadingProduct U * A = Polynomial.X ^ Fintype.card F * f + g := by
  obtain ⟨a, ha, had, hvan⟩ := exists_redei_auxiliary U d hsize
  obtain ⟨f, g, hf, hg, hid⟩ := redei_mul_decomposition U a hvan
  let s := U.card + a.totalDegree - Fintype.card F
  refine ⟨leadingSpecialization a.totalDegree a, leadingSpecialization s f,
    leadingSpecialization s g, leadingSpecialization_ne_zero a ha,
    (natDegree_leadingSpecialization_le _ _).trans had, ?_, ?_, ?_⟩
  · exact (natDegree_leadingSpecialization_le _ _).trans
      (Nat.sub_le_sub_right (Nat.add_le_add_left had U.card) _)
  · exact (natDegree_leadingSpecialization_le _ _).trans
      (Nat.sub_le_sub_right (Nat.add_le_add_left had U.card) _)
  · exact redei_leading_identity U a f g (Fintype.card F) Fintype.one_lt_card
      (card_le_redei_auxiliary_degree U a ha hvan) hf hg hid

end Balanced.StabilityPolynomial

end OAI
