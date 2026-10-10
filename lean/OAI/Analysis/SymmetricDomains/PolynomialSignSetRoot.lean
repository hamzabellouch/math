import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialSignSetQuery
import OAI.Analysis.SymmetricDomains.SampleAllChambers

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination

section
open Polynomial Set Filter
open scoped Topology BigOperators Classical

theorem finite_polynomial_sign_sampler {ι : Type*} [Fintype ι]
    (Q : ι → ℝ[X]) :
    ∃ R : ℝ[X], R ≠ 0 ∧ ∀ x : ℝ, ∃ y : ℝ, R.eval y = 0 ∧
      ∀ i, SignType.sign ((Q i).eval y) = SignType.sign ((Q i).eval x) := by
  classical
  let J := {i : ι // Q i ≠ 0}
  let Q' : J → ℝ[X] := fun i => Q i.val
  let R := (∏ i, Q' i) * criticalSampler (∏ i, Q' i)
  have hh := sample_all_chambers Q' (fun i => i.property)
  refine ⟨R,hh.1,fun x => ?_⟩
  obtain ⟨y,hy,hs⟩ := hh.2 x
  refine ⟨y,hy,fun i => ?_⟩
  by_cases hi : Q i = 0
  · simp only [hi,eval_zero]
  · exact hs ⟨i,hi⟩

end

open Polynomial Set Finset
open scoped Classical BigOperators

lemma support_eq_of_coeff_sign_eq {P Q : ℝ[X]}
    (h : ∀ k, SignType.sign (P.coeff k) = SignType.sign (Q.coeff k)) :
    P.support = Q.support := by
  ext k
  simp only [mem_support_iff]
  apply not_congr
  simpa only [sign_eq_zero_iff] using (show SignType.sign (P.coeff k) = 0 ↔
    SignType.sign (Q.coeff k) = 0 by rw [h k])

lemma degree_data_of_coeff_sign_eq {P Q : ℝ[X]}
    (h : ∀ k, SignType.sign (P.coeff k) = SignType.sign (Q.coeff k)) :
    (P = 0 ↔ Q = 0) ∧ P.natDegree = Q.natDegree := by
  have hs := support_eq_of_coeff_sign_eq h
  constructor
  · rw [← support_eq_empty,← support_eq_empty,hs]
  · simp only [natDegree,degree,hs]

lemma coeff_sign_ext_of_bound {P Q : ℝ[X]} {N : ℕ}
    (hP : P.natDegree ≤ N) (hQ : Q.natDegree ≤ N)
    (h : ∀ k : Fin (N+1), SignType.sign (P.coeff k) = SignType.sign (Q.coeff k)) :
    ∀ k, SignType.sign (P.coeff k) = SignType.sign (Q.coeff k) := by
  intro k
  by_cases hk : k ≤ N
  · exact h ⟨k,Nat.lt_succ_of_le hk⟩
  · rw [coeff_eq_zero_of_natDegree_lt (hP.trans_lt (Nat.lt_of_not_ge hk)),
      coeff_eq_zero_of_natDegree_lt (hQ.trans_lt (Nat.lt_of_not_ge hk))]

lemma degree_stratum_signSet {X ι : Type*} {c : X → ι → ℝ} {S : Set X}
    (hS : PolynomialSignSet c S) (P : X → ℝ[X]) (N n : ℕ)
    (hP : ∀ k, RationalOn c S (fun x => (P x).coeff k))
    (hd : ∀ x ∈ S, (P x).natDegree ≤ N) :
    PolynomialSignSet c (S ∩ {x | P x ≠ 0 ∧ (P x).natDegree = n}) := by
  apply polynomialSignSet_of_sign_invariant hS
    (fun k : Fin (N+1) => fun x => (P x).coeff k) (fun k => hP k)
  intro x hx y hy he
  have hh := degree_data_of_coeff_sign_eq (coeff_sign_ext_of_bound (hd x hx) (hd y hy) he)
  simp only [ne_eq,hh.1,hh.2]

lemma zero_stratum_signSet {X ι : Type*} {c : X → ι → ℝ} {S : Set X}
    (hS : PolynomialSignSet c S) (P : X → ℝ[X]) (N : ℕ)
    (hP : ∀ k, RationalOn c S (fun x => (P x).coeff k))
    (hd : ∀ x ∈ S, (P x).natDegree ≤ N) :
    PolynomialSignSet c (S ∩ {x | P x = 0}) := by
  apply polynomialSignSet_of_sign_invariant hS
    (fun k : Fin (N+1) => fun x => (P x).coeff k) (fun k => hP k)
  intro x hx y hy he
  exact (degree_data_of_coeff_sign_eq (coeff_sign_ext_of_bound (hd x hx) (hd y hy) he)).1

theorem polynomialSignSet_query_bounded {X ι α : Type*} [Fintype α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (N : ℕ) (d : α → ℕ) (P : X → ℝ[X]) (Q : α → X → ℝ[X])
    (hP : ∀ k, RationalOn c S (fun x => (P x).coeff k))
    (hQ : ∀ a k, RationalOn c S (fun x => (Q a x).coeff k))
    (hp : ∀ x ∈ S, P x ≠ 0 ∧ (P x).natDegree ≤ N)
    (hq : ∀ a x, x ∈ S → (Q a x).degree < d a)
    (W : (α → ℝ) → Prop) :
    PolynomialSignSet c (S ∩ {x | W (fun a => tarskiQuery (P x) (Q a x))}) := by
  have hh (n : Fin (N+1)) := polynomialSignSet_query_predicate
    (degree_stratum_signSet hS P N n hP (fun x hx => (hp x hx).2)) n d P Q
    (fun k => (hP k).mono inter_subset_left)
    (fun a k => (hQ a k).mono inter_subset_left)
    (fun x hx => hx.2) (fun a x hx => hq a x hx.1) W
  have hh' := PolynomialSignSet.exists_finite _ hh
  convert hh' using 1
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq]
  constructor
  · rintro ⟨hx,hw⟩
    exact ⟨⟨(P x).natDegree,Nat.lt_succ_of_le (hp x hx).2⟩,⟨hx,(hp x hx).1,rfl⟩,hw⟩
  · rintro ⟨n,⟨hx,_⟩,hw⟩
    exact ⟨hx,hw⟩

def RationalPolynomialOn {X ι : Type*} (c : X → ι → ℝ) (S : Set X)
    (P : X → ℝ[X]) : Prop := ∀ k, RationalOn c S (fun x => (P x).coeff k)

namespace RationalPolynomialOn
variable {X ι : Type*} {c : X → ι → ℝ} {S T : Set X} {P Q : X → ℝ[X]}
lemma mono (h : RationalPolynomialOn c S P) (hT : T ⊆ S) : RationalPolynomialOn c T P :=
  fun k => (h k).mono hT
lemma congr (h : RationalPolynomialOn c S P) (he : ∀ x ∈ S, P x = Q x) :
    RationalPolynomialOn c S Q := fun k => (h k).congr (fun x hx => congrArg (fun p => p.coeff k) (he x hx))
lemma const (P : ℝ[X]) : RationalPolynomialOn c S (fun _ => P) := fun _ => RationalOn.const _
lemma add (hP : RationalPolynomialOn c S P) (hQ : RationalPolynomialOn c S Q) :
    RationalPolynomialOn c S (fun x => P x + Q x) := by
  intro k
  simpa only [coeff_add] using (hP k).add (hQ k)
lemma neg (hP : RationalPolynomialOn c S P) : RationalPolynomialOn c S (fun x => -P x) := by
  intro k
  simpa only [coeff_neg] using (hP k).neg
lemma sub (hP : RationalPolynomialOn c S P) (hQ : RationalPolynomialOn c S Q) :
    RationalPolynomialOn c S (fun x => P x - Q x) := by
  simpa only [sub_eq_add_neg] using hP.add hQ.neg
lemma mul (hP : RationalPolynomialOn c S P) (hQ : RationalPolynomialOn c S Q) :
    RationalPolynomialOn c S (fun x => P x * Q x) := by
  intro k
  simpa only [coeff_mul] using RationalOn.sum (Finset.HasAntidiagonal.antidiagonal k)
    (fun a x => (P x).coeff a.1 * (Q x).coeff a.2) (fun a _ => (hP a.1).mul (hQ a.2))
lemma pow (hP : RationalPolynomialOn c S P) (n : ℕ) :
    RationalPolynomialOn c S (fun x => P x ^ n) := by
  induction n with
  | zero => simpa using (const (c := c) (S := S) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hP
lemma prod {α : Type*} (s : Finset α) (P : α → X → ℝ[X])
    (hP : ∀ a ∈ s, RationalPolynomialOn c S (P a)) :
    RationalPolynomialOn c S (fun x => ∏ a ∈ s, P a x) := by
  induction s using Finset.induction_on with
  | empty => simpa using (const (c := c) (S := S) 1)
  | @insert a s ha ih =>
    simpa only [Finset.prod_insert ha] using
      (hP a (by simp)).mul (ih (fun b hb => hP b (by simp [hb])))
lemma derivative (hP : RationalPolynomialOn c S P) :
    RationalPolynomialOn c S (fun x => (P x).derivative) := by
  intro k
  simpa only [coeff_derivative] using (hP (k+1)).mul (RationalOn.const (k+1))
lemma criticalSampler (hP : RationalPolynomialOn c S P) (n : ℕ)
    (hn : ∀ x ∈ S, (P x).natDegree = n) :
    RationalPolynomialOn c S (fun x => SignElimination.criticalSampler (P x)) := by
  have hh := hP.derivative.add ((const Polynomial.X).mul
    (((const Polynomial.X).mul hP.derivative).sub ((const (Polynomial.C (n+1 : ℝ))).mul hP)))
  apply hh.congr
  intro x hx
  simp only [SignElimination.criticalSampler,hn x hx]
end RationalPolynomialOn

lemma degree_lt_bound {P : ℝ[X]} {N : ℕ} (h : P.natDegree ≤ N) : P.degree < (N+1 : ℕ) :=
  degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le h)

theorem polynomialSignSet_root_signs {X ι α : Type*} [Fintype α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (N : ℕ) (d : α → ℕ) (P : X → ℝ[X]) (Q : α → X → ℝ[X])
    (hP : RationalPolynomialOn c S P) (hQ : ∀ a, RationalPolynomialOn c S (Q a))
    (hp : ∀ x ∈ S, P x ≠ 0 ∧ (P x).natDegree ≤ N)
    (hq : ∀ a x, x ∈ S → (Q a x).natDegree ≤ d a)
    (σ : α → SignType) :
    PolynomialSignSet c (S ∩ {x | ∃ y : ℝ, (P x).eval y = 0 ∧
      ∀ a, SignType.sign ((Q a x).eval y) = σ a}) := by
  let R := fun e : α → Fin 3 => fun x => ∏ a, (Q a x) ^ (e a).val
  have hr (e : α → Fin 3) : RationalPolynomialOn c S (R e) :=
    RationalPolynomialOn.prod univ _ (fun a _ => (hQ a).pow _)
  have hd (e : α → Fin 3) (x : X) (hx : x ∈ S) :
      (R e x).degree < ((∑ a, (e a).val * d a)+1 : ℕ) := by
    apply degree_lt_bound
    exact (natDegree_prod_le _ _).trans (sum_le_sum (fun a _ =>
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hq a x hx))))
  have hh := polynomialSignSet_query_bounded hS N (fun e => (∑ a, (e a).val*d a)+1)
    P R hP hr hp hd (fun t => 0 < ∑ e, (∏ a, signCoefficient (σ a) (e a))*t e)
  convert hh using 1
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq]
  apply and_congr_right
  intro hx
  exact exists_root_sign_pattern_iff (hp x hx).1 (fun a => Q a x) σ

end Release061.SignElimination

end

end OAI
