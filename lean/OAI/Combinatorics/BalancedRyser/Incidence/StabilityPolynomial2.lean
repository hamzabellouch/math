import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic

namespace OAI

namespace Balanced.StabilityPolynomial

open MvPolynomial

variable {F σ : Type*} [Field F]

theorem exists_nonzero_vanishing_with_support
    (M : Finset (σ →₀ ℕ)) (S : Finset (σ → F)) (hcard : S.card < M.card) :
    ∃ p : MvPolynomial σ F, p ≠ 0 ∧ p.support ⊆ M ∧
      ∀ x ∈ S, eval x p = 0 := by
  classical
  let V := restrictSupport F (M : Set (σ →₀ ℕ))
  let b : Module.Basis M F V := basisRestrictSupport F (M : Set (σ →₀ ℕ))
  let : Module.Finite F V := Module.Finite.of_basis b
  let E : V →ₗ[F] (S → F) :=
    { toFun := fun p x => eval x.val p.val
      map_add' := by intro p q; ext x; simp
      map_smul' := by intro a p; ext x; simp }
  have hdim : Module.finrank F (S → F) < Module.finrank F V := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis b]
    simpa using hcard
  obtain ⟨p, hp, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := E) hdim)
  refine ⟨p.val, ?_, p.property, ?_⟩
  · intro hz
    exact hne (Subtype.ext hz)
  · intro x hx
    exact congrFun (LinearMap.mem_ker.mp hp) ⟨x, hx⟩

theorem exists_nonzero_vanishing_degree_le
    (M : Finset (σ →₀ ℕ)) (S : Finset (σ → F)) (d : ℕ)
    (hcard : S.card < M.card)
    (hdegree : ∀ m ∈ M, m.sum (fun _ n => n) ≤ d) :
    ∃ p : MvPolynomial σ F, p ≠ 0 ∧ p.totalDegree ≤ d ∧
      ∀ x ∈ S, eval x p = 0 := by
  obtain ⟨p, hp, hs, hv⟩ := exists_nonzero_vanishing_with_support M S hcard
  refine ⟨p, hp, ?_, hv⟩
  apply (mem_restrictTotalDegree σ d p).mp
  intro m hm
  exact hdegree m (hs hm)

theorem eq_constant_of_derivative_zero_of_degree_lt
    (p : ℕ) [CharP F p] (hp : 0 < p) (f : Polynomial F)
    (hf : f.derivative = 0) (hdegree : f.natDegree < p) :
    f = Polynomial.C (f.coeff 0) := by
  have he : Polynomial.expand F p (Polynomial.contract p f) = f :=
    Polynomial.expand_contract p hf hp.ne'
  have hd : (Polynomial.contract p f).natDegree * p = f.natDegree := by
    rw [← Polynomial.natDegree_expand, he]
  have hc : (Polynomial.contract p f).natDegree = 0 := by
    by_contra h
    have hpos : 1 ≤ (Polynomial.contract p f).natDegree := Nat.one_le_iff_ne_zero.mpr h
    nlinarith
  apply Polynomial.eq_C_of_natDegree_eq_zero
  rw [← hd, hc, zero_mul]

noncomputable def pairExponent (a : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a.1 + Finsupp.single 1 a.2

lemma pairExponent_injective : Function.Injective pairExponent := by
  intro a b h
  have h0 := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h
  have h1 := congrArg (fun m : Fin 2 →₀ ℕ => m 1) h
  simp only [pairExponent, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
    Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), add_zero, zero_add] at h0 h1
  exact Prod.ext h0 h1

lemma sum_pairExponent (a : ℕ × ℕ) :
    (pairExponent a).sum (fun _ n => n) = a.1 + a.2 := by
  simp [pairExponent, Finsupp.sum_add_index']

def trianglePairs (d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (d + 1)).biUnion Finset.antidiagonal

lemma mem_trianglePairs (d : ℕ) (a : ℕ × ℕ) :
    a ∈ trianglePairs d ↔ a.1 + a.2 ≤ d := by
  simp only [trianglePairs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal]
  constructor
  · rintro ⟨k, hk, he⟩
    omega
  · intro h
    exact ⟨a.1 + a.2, by omega, rfl⟩

lemma twice_card_trianglePairs (d : ℕ) :
    2 * (trianglePairs d).card = (d + 1) * (d + 2) := by
  have hdis : (↑(Finset.range (d + 1)) : Set ℕ).PairwiseDisjoint
      Finset.antidiagonal := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    exact hij ((Finset.mem_antidiagonal.mp hai).symm.trans (Finset.mem_antidiagonal.mp haj))
  rw [trianglePairs, Finset.card_biUnion hdis]
  simp only [Finset.Nat.card_antidiagonal, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, mul_one]
  have hsum := Finset.sum_range_id_mul_two (d + 1)
  simp only [Nat.add_sub_cancel] at hsum
  nlinarith

theorem exists_bivariate_vanishing
    (S : Finset (Fin 2 → F)) (d : ℕ)
    (hsize : 2 * S.card < (d + 1) * (d + 2)) :
    ∃ p : MvPolynomial (Fin 2) F, p ≠ 0 ∧ p.totalDegree ≤ d ∧
      ∀ x ∈ S, eval x p = 0 := by
  classical
  let M := (trianglePairs d).image pairExponent
  apply exists_nonzero_vanishing_degree_le M S d
  · have hc : M.card = (trianglePairs d).card :=
      Finset.card_image_of_injective _ pairExponent_injective
    have ht := twice_card_trianglePairs d
    omega
  · intro m hm
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
    rw [sum_pairExponent]
    exact (mem_trianglePairs d a).mp ha

theorem exists_bivariate_vanishing_sq_degree_lt
    (S : Finset (Fin 2 → F)) (hS : S.Nonempty) :
    ∃ p : MvPolynomial (Fin 2) F, p ≠ 0 ∧ p.totalDegree ^ 2 < 2 * S.card ∧
      ∀ x ∈ S, eval x p = 0 := by
  let d := Nat.sqrt (2 * S.card - 1)
  have hpos : 0 < S.card := Finset.card_pos.mpr hS
  have hroot := Nat.lt_succ_sqrt (2 * S.card - 1)
  have hd : 2 * S.card < (d + 1) * (d + 2) := by
    have hsub : 2 * S.card - 1 + 1 = 2 * S.card := by omega
    change 2 * S.card - 1 < (d + 1) * (d + 1) at hroot
    nlinarith
  obtain ⟨p, hp, hpd, heval⟩ := exists_bivariate_vanishing S d hd
  refine ⟨p, hp, ?_, heval⟩
  have hsq : d ^ 2 ≤ 2 * S.card - 1 := Nat.sqrt_le' _
  have hmono : p.totalDegree ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hpd 2
  omega

end Balanced.StabilityPolynomial

end OAI
