import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialSignSetSigns

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
namespace Release061.PolynomialSignSet
open Set
open scoped Classical

theorem finite_sign_description {X ι : Type*} {c : X → ι → ℝ} {S : Set X}
    (hS : PolynomialSignSet c S) :
    ∃ (s : Finset (MvPolynomial ι ℝ)) (W : (s → SignType) → Prop),
      ∀ x, x ∈ S ↔ W (fun p => SignType.sign (MvPolynomial.eval (c x) p.val)) := by
  induction hS with
  | zero p =>
    refine ⟨{p},fun σ => σ ⟨p,by simp⟩ = 0,fun x => ?_⟩
    simp only [mem_ofPred_eq,sign_eq_zero_iff]
  | positive p =>
    refine ⟨{p},fun σ => σ ⟨p,by simp⟩ = 1,fun x => ?_⟩
    simp only [mem_ofPred_eq,sign_eq_one_iff]
  | @compl S _ ih =>
    obtain ⟨s,W,h⟩ := ih
    exact ⟨s,fun σ => ¬ W σ,fun x => by simp only [mem_compl_iff,h x]⟩
  | @union S T _ _ ihS ihT =>
    obtain ⟨s,W,hs⟩ := ihS
    obtain ⟨t,V,ht⟩ := ihT
    refine ⟨s ∪ t,fun σ =>
      W (fun p => σ ⟨p.val,Finset.mem_union_left _ p.property⟩) ∨
      V (fun p => σ ⟨p.val,Finset.mem_union_right _ p.property⟩),fun x => ?_⟩
    simp only [mem_union,hs x,ht x]

end Release061.PolynomialSignSet

namespace Release061.SignElimination
open Polynomial Set
open scoped Classical BigOperators

lemma eval_optionEquivLeft {ι : Type*} (p : MvPolynomial (Option ι) ℝ)
    (x : ι → ℝ) (y : ℝ) :
    (((MvPolynomial.optionEquivLeft ℝ ι) p).map (MvPolynomial.eval x)).eval y =
      MvPolynomial.eval (fun o => Option.elim o y x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add,Polynomial.map_add,eval_add,hp,hq]
  | mul_X p a hp =>
    cases a with
    | none => simp only [map_mul,Polynomial.map_mul,MvPolynomial.optionEquivLeft_X_none,map_X,eval_mul,eval_X,
        hp,MvPolynomial.eval_X,Option.elim_none]
    | some a => simp only [map_mul,Polynomial.map_mul,MvPolynomial.optionEquivLeft_X_some,map_C,eval_mul,eval_C,
        hp,MvPolynomial.eval_X,Option.elim_some]

theorem polynomialSignSet_projection_one {X ι : Type*} {c : X → ι → ℝ}
    {A : Set (X × ℝ)}
    (hA : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) A) :
    PolynomialSignSet c {x | ∃ y : ℝ, (x,y) ∈ A} := by
  classical
  obtain ⟨s,W,hW⟩ := hA.finite_sign_description
  let Q : s → X → ℝ[X] := fun p x =>
    (((MvPolynomial.optionEquivLeft ℝ ι) p.val).map (MvPolynomial.eval (c x)))
  let d : s → ℕ := fun p => ((MvPolynomial.optionEquivLeft ℝ ι) p.val).natDegree
  have hQ (p : s) : RationalPolynomialOn c univ (Q p) := by
    intro k
    simpa only [Q,coeff_map] using RationalOn.polynomial
      (((MvPolynomial.optionEquivLeft ℝ ι) p.val).coeff k)
  have hd (p : s) (x : X) (_hx : x ∈ (univ : Set X)) : (Q p x).natDegree ≤ d p := natDegree_map_le
  have hσ (σ : s → SignType) : PolynomialSignSet c
      {x | W σ ∧ ∃ y : ℝ, ∀ p : s, SignType.sign ((Q p x).eval y) = σ p} := by
    have hh := polynomialSignSet_exists_signs (PolynomialSignSet.univ (c := c)) d Q hQ hd σ
    simpa only [univ_inter,← ofPred_and] using (PolynomialSignSet.const (c := c) (W σ)).inter hh
  have hh := PolynomialSignSet.exists_finite _ hσ
  convert hh using 1
  ext x
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨fun p => SignType.sign ((Q p x).eval y),?_,y,fun _ => rfl⟩
    simpa only [Q,eval_optionEquivLeft] using (hW (x,y)).mp hy
  · rintro ⟨σ,hσ,y,hy⟩
    refine ⟨y,(hW (x,y)).mpr ?_⟩
    have he : (fun p : s => SignType.sign (MvPolynomial.eval (fun o => Option.elim o y (c x)) p.val)) = σ := by
      funext p
      simpa only [Q,eval_optionEquivLeft] using hy p
    rwa [he]

end Release061.SignElimination

end

end OAI
