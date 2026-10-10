import Mathlib
import OAI.Analysis.SymmetricDomains.TarskiQueryCharpoly
import OAI.Analysis.SymmetricDomains.PolynomialSignSetFinite

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
open Polynomial Matrix Finset Set
open scoped Classical BigOperators

lemma signVariations_congr_coeff {P Q : ℝ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hd : P.natDegree = Q.natDegree)
    (hs : ∀ k ≤ P.natDegree, SignType.sign (P.coeff k) = SignType.sign (Q.coeff k)) :
    P.signVariations = Q.signVariations := by
  have he : P.coeffList.map SignType.sign = Q.coeffList.map SignType.sign := by
    simp only [coeffList,withBotSucc_degree_eq_natDegree_add_one hP,
      withBotSucc_degree_eq_natDegree_add_one hQ,← hd,List.map_map]
    apply List.map_congr_left
    intro k hk
    exact hs k (by simpa only [List.mem_reverse,List.mem_range,Nat.lt_succ_iff] using hk)
  change P.coeffList.signVariations = Q.coeffList.signVariations
  simpa only [List.signVariations_map_sign] using congrArg List.signVariations he

lemma signVariations_neg_congr_coeff {P Q : ℝ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hd : P.natDegree = Q.natDegree)
    (hs : ∀ k ≤ P.natDegree, SignType.sign (P.coeff k) = SignType.sign (Q.coeff k)) :
    (P.comp (-X)).signVariations = (Q.comp (-X)).signVariations := by
  apply signVariations_congr_coeff (by simpa using hP) (by simpa using hQ)
    (by simpa only [natDegree_comp_neg] using hd)
  intro k hk
  simp only [natDegree_comp_neg] at hk
  rw [coeff_comp_neg,coeff_comp_neg,sign_mul,sign_mul,hs k hk]

noncomputable def charpolyCoefficient {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ) :
    MvPolynomial (n × n) ℝ :=
  (Matrix.charpoly (fun i j : n => (MvPolynomial.X (i,j) : MvPolynomial (n × n) ℝ))).coeff k

lemma eval_charpolyCoefficient {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (k : ℕ) :
    MvPolynomial.eval (fun p : n × n => A p.1 p.2) (charpolyCoefficient (n := n) k) =
      A.charpoly.coeff k := by
  let M : Matrix n n (MvPolynomial (n × n) ℝ) := fun i j => MvPolynomial.X (i,j)
  let f := MvPolynomial.eval (fun p : n × n => A p.1 p.2)
  have he : Matrix.map M f = A := by
    ext i j
    change MvPolynomial.eval _ (MvPolynomial.X (i,j)) = _
    exact MvPolynomial.eval_X _
  have hc := congrArg (fun p : ℝ[X] => p.coeff k) (Matrix.charpoly_map M f)
  rw [he,Polynomial.coeff_map] at hc
  exact hc.symm

lemma rationalOn_charpoly_coefficient {X ι n : Type*} [Fintype n] [DecidableEq n]
    {c : X → ι → ℝ} {S : Set X} (A : X → Matrix n n ℝ)
    (hA : ∀ i j, RationalOn c S (fun x => A x i j)) (k : ℕ) :
    RationalOn c S (fun x => (A x).charpoly.coeff k) := by
  simpa only [eval_charpolyCoefficient] using RationalOn.eval
    (charpolyCoefficient (n := n) k) (fun p x => A x p.1 p.2) (fun p => hA p.1 p.2)

lemma polynomialSignSet_of_sign_invariant {X ι α : Type*} [Finite α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (f : α → X → ℝ) (hf : ∀ a, RationalOn c S (f a)) (W : X → Prop)
    (hW : ∀ x ∈ S, ∀ y ∈ S,
      (∀ a, SignType.sign (f a x) = SignType.sign (f a y)) → (W x ↔ W y)) :
    PolynomialSignSet c (S ∩ {x | W x}) := by
  have hh := polynomialSignSet_finite_signs hS f hf
    (fun σ => ∃ y ∈ S, W y ∧ ∀ a, SignType.sign (f a y) = σ a)
  convert hh using 1
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq]
  apply and_congr_right
  intro hx
  constructor
  · intro hw
    exact ⟨x,hx,hw,fun _ => rfl⟩
  · rintro ⟨y,hy,hw,hs⟩
    exact (hW y hy x hx hs).mp hw

noncomputable def coefficientHermiteMatrix (n d : ℕ) (P Q : ℝ[X]) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k : Fin d, Q.coeff k.val *
    MvPolynomial.eval (fun l : Fin n => (-1)^(l.val+1)*P.coeff (n-(l.val+1))/P.coeff n)
      (powerSumPolynomial n (k.val+i.val+j.val))

lemma coefficientHermiteMatrix_eq {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X])
    {d : ℕ} (hQ : Q.degree < d) :
    coefficientHermiteMatrix P.natDegree d P Q = hermiteMatrix P Q := by
  ext i j
  rw [hermiteMatrix_coefficients hP Q hQ]
  rfl

lemma rationalOn_coefficientHermite {X ι : Type*} {c : X → ι → ℝ} {S : Set X}
    (n d : ℕ) (P Q : X → ℝ[X])
    (hP : ∀ k, RationalOn c S (fun x => (P x).coeff k))
    (hQ : ∀ k, RationalOn c S (fun x => (Q x).coeff k))
    (hn : ∀ x ∈ S, (P x).coeff n ≠ 0) (i j : Fin n) :
    RationalOn c S (fun x => coefficientHermiteMatrix n d (P x) (Q x) i j) := by
  apply RationalOn.sum
  intro k _
  apply (hQ k.val).mul
  apply RationalOn.eval
  intro l
  exact ((RationalOn.const _).mul (hP (n-(l.val+1)))).div (hP n) hn

lemma tarskiQuery_coefficient_charpoly {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X])
    {n d : ℕ} (hn : P.natDegree = n) (hQ : Q.degree < d) :
    tarskiQuery P Q =
      ((coefficientHermiteMatrix n d P Q).charpoly.signVariations : ℝ) -
      (((coefficientHermiteMatrix n d P Q).charpoly.comp (-X)).signVariations : ℝ) := by
  subst n
  rw [coefficientHermiteMatrix_eq hP Q hQ]
  exact tarskiQuery_charpoly hP Q

theorem polynomialSignSet_query_predicate {X ι α : Type*} [Fintype α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (n : ℕ) (d : α → ℕ) (P : X → ℝ[X]) (Q : α → X → ℝ[X])
    (hP : ∀ k, RationalOn c S (fun x => (P x).coeff k))
    (hQ : ∀ a k, RationalOn c S (fun x => (Q a x).coeff k))
    (hp : ∀ x ∈ S, P x ≠ 0 ∧ (P x).natDegree = n)
    (hq : ∀ a x, x ∈ S → (Q a x).degree < d a)
    (W : (α → ℝ) → Prop) :
    PolynomialSignSet c (S ∩ {x | W (fun a => tarskiQuery (P x) (Q a x))}) := by
  let A := fun a x => coefficientHermiteMatrix n (d a) (P x) (Q a x)
  have hra (a : α) (i j : Fin n) : RationalOn c S (fun x => A a x i j) := by
    apply rationalOn_coefficientHermite n (d a) P (Q a) hP (hQ a)
    intro x hx
    rw [← (hp x hx).2]
    exact leadingCoeff_ne_zero.mpr (hp x hx).1
  let f : (α × Fin (n+1)) → X → ℝ := fun a x => (A a.1 x).charpoly.coeff a.2.val
  have hrf (a : α × Fin (n+1)) : RationalOn c S (f a) :=
    rationalOn_charpoly_coefficient (A a.1) (hra a.1) a.2.val
  apply polynomialSignSet_of_sign_invariant hS f hrf
  intro x hx y hy he
  have ht (a : α) : tarskiQuery (P x) (Q a x) = tarskiQuery (P y) (Q a y) := by
    rw [tarskiQuery_coefficient_charpoly (hp x hx).1 _ (hp x hx).2 (hq a x hx),
      tarskiQuery_coefficient_charpoly (hp y hy).1 _ (hp y hy).2 (hq a y hy)]
    have hdeg : (A a x).charpoly.natDegree = (A a y).charpoly.natDegree := by
      simp only [Matrix.charpoly_natDegree_eq_dim]
    have hs : ∀ k ≤ (A a x).charpoly.natDegree,
        SignType.sign ((A a x).charpoly.coeff k) = SignType.sign ((A a y).charpoly.coeff k) := by
      intro k hk
      have hk' : k < n+1 := by simpa using Nat.lt_succ_of_le hk
      exact he (a,⟨k,hk'⟩)
    rw [signVariations_congr_coeff (A a x).charpoly_monic.ne_zero (A a y).charpoly_monic.ne_zero hdeg hs,
      signVariations_neg_congr_coeff (A a x).charpoly_monic.ne_zero (A a y).charpoly_monic.ne_zero hdeg hs]
  rw [funext ht]

end Release061.SignElimination

end

end OAI
