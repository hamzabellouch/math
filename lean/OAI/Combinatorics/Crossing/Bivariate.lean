import OAI.Combinatorics.Crossing.Interpolation
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule

abbrev BiPoly := PolynomialModule ℝ (PolynomialModule ℝ ℝ)

def biCoeff (p : BiPoly) (a b : ℕ) : ℝ := (p.coeff a).coeff b

def biEval (u v : ℝ) : BiPoly →ₗ[ℝ] ℝ := (eval v).comp (eval u)

def BiBounded (r s : ℕ) (p : BiPoly) : Prop :=
  Bounded r p ∧ ∀ a, Bounded s (p.coeff a)

def flattenBi : BiPoly ≃ₗ[ℝ] (ℕ × ℕ →₀ ℝ) :=
  ((coeffLinearEquiv ℝ ℝ).trans
    (Finsupp.mapRange.linearEquiv (coeffLinearEquiv ℝ ℝ))).trans
    (Finsupp.curryLinearEquiv ℝ).symm

theorem flattenBi_apply (p : BiPoly) (a b : ℕ) : flattenBi p (a,b) = biCoeff p a b := rfl

def swapBi : BiPoly ≃ₗ[ℝ] BiPoly :=
  (flattenBi.trans (Finsupp.mapDomain.linearEquiv ℝ ℝ (Equiv.prodComm ℕ ℕ))).trans
    flattenBi.symm

theorem biCoeff_swap (p : BiPoly) (a b : ℕ) : biCoeff (swapBi p) a b = biCoeff p b a := by
  rw [← flattenBi_apply]
  change flattenBi (flattenBi.symm _) (a,b) = _
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.mapDomain_equiv_apply (flattenBi p) (a,b)

theorem bi_ext {p q : BiPoly} (h : ∀ a b, biCoeff p a b = biCoeff q a b) : p = q := by
  apply PolynomialModule.ext
  apply Finsupp.ext
  intro a
  apply PolynomialModule.ext
  apply Finsupp.ext
  exact h a

theorem swapBi_swapBi (p : BiPoly) : swapBi (swapBi p) = p := by
  apply bi_ext
  intro a b
  rw [biCoeff_swap, biCoeff_swap]

theorem swapBi_single (a b : ℕ) (c : ℝ) :
    swapBi (single ℝ a (single ℝ b c)) = single ℝ b (single ℝ a c) := by
  apply bi_ext
  intro i j
  rw [biCoeff_swap]
  simp [biCoeff, Finsupp.single_apply]
  split_ifs <;> simp_all

theorem biEval_swap (p : BiPoly) (u v : ℝ) : biEval u v (swapBi p) = biEval v u p := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single a q =>
    induction q using PolynomialModule.induction_linear with
    | zero => simp
    | add p q hp hq => simp only [single_add, map_add, hp, hq]
    | single b c =>
      rw [swapBi_single]
      simp [biEval, eval_single, smul_eq_mul]
      ring

theorem biBounded_swap {r s : ℕ} {p : BiPoly} (hp : BiBounded r s p) :
    BiBounded s r (swapBi p) := by
  constructor
  · intro a ha
    apply PolynomialModule.ext
    apply Finsupp.ext
    intro b
    change biCoeff (swapBi p) a b = 0
    rw [biCoeff_swap]
    exact hp.2 b a ha
  · intro a b hb
    change biCoeff (swapBi p) a b = 0
    rw [biCoeff_swap]
    simp [biCoeff, hp.1 b hb]

def boundedSpace (k : ℕ) : Submodule ℝ (PolynomialModule ℝ ℝ) where
  carrier := {p | Bounded k p}
  zero_mem' := bounded_zero k
  add_mem' := bounded_add
  smul_mem' := by
    intro c p hp n hn
    change c • p.coeff n = 0
    rw [hp n hn, smul_zero]

theorem coefficients_of_mulRoot {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Z : Submodule ℝ W) (t : ℝ) (k : ℕ) (q : PolynomialModule ℝ W)
    (hq : Bounded k q) (hc : ∀ n, (mulRoot t q).coeff n ∈ Z) :
    ∀ n, q.coeff n ∈ Z := by
  have aux : ∀ d n, k-n = d → q.coeff n ∈ Z := by
    intro d
    induction d with
    | zero =>
      intro n hn
      rw [hq n (by omega)]
      exact Z.zero_mem
    | succ d ih =>
      intro n hn
      have hh := Z.add_mem (hc (n+1)) (Z.smul_mem t (ih (n+1) (by omega)))
      simpa only [mulRoot_coeff_succ, sub_add_cancel] using hh
  intro n
  exact aux (k-n) n rfl

theorem bi_factor_row (r s : ℕ) (p : BiPoly) (hp : BiBounded (r+1) s p)
    (t : ℝ) (hz : eval t p = 0) :
    ∃ q : BiPoly, BiBounded r s q ∧ mulRoot t q = p := by
  obtain ⟨q, hq, he⟩ := exists_mulRoot_of_eval_zero t r p hp.1 hz
  refine ⟨q, ⟨hq, ?_⟩, he⟩
  apply coefficients_of_mulRoot (boundedSpace s) t r q hq
  intro n
  rw [he]
  exact hp.2 n

theorem biEval_mulRoot (t u v : ℝ) (p : BiPoly) :
    biEval u v (mulRoot t p) = (u-t) * biEval u v p := by
  change eval v (eval u (mulRoot t p)) = _
  rw [eval_mulRoot, _root_.map_smul]
  rfl

theorem bounded_eval_outer {r s : ℕ} {p : BiPoly} (hp : BiBounded r s p) (u : ℝ) :
    Bounded s (eval u p) := by
  change eval u p ∈ boundedSpace s
  change p.coeff.sum (fun a c => u^a • c) ∈ boundedSpace s
  apply Submodule.sum_mem
  intro a ha
  exact (boundedSpace s).smul_mem (u^a) (hp.2 a)

end Zarankiewicz

end

end OAI
