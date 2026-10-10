import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialSignSetRoot

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
open Polynomial Set Finset
open scoped Classical BigOperators

lemma criticalSampler_natDegree_le (P : ℝ[X]) :
    (criticalSampler P).natDegree ≤ P.natDegree+2 := by
  have hd : P.derivative.natDegree ≤ P.natDegree := (natDegree_derivative_le P).trans (Nat.sub_le _ _)
  unfold criticalSampler
  apply natDegree_add_le_of_degree_le (hd.trans (by omega))
  apply natDegree_mul_le.trans
  rw [natDegree_X]
  have hh : (X * P.derivative - C (P.natDegree+1 : ℝ)*P).natDegree ≤ P.natDegree+1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by simpa only [natDegree_X,Nat.add_comm] using Nat.add_le_add_left hd 1)
    · exact (natDegree_C_mul_le _ _).trans (by omega)
  omega

lemma polynomialSignSet_nonzero_mask {X ι α : Type*} [Fintype α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (d : α → ℕ) (Q : α → X → ℝ[X])
    (hQ : ∀ a, RationalPolynomialOn c S (Q a))
    (hq : ∀ a x, x ∈ S → (Q a x).natDegree ≤ d a) (J : Finset α) :
    PolynomialSignSet c (S ∩ {x | ∀ a, Q a x ≠ 0 ↔ a ∈ J}) := by
  apply polynomialSignSet_of_sign_invariant hS
    (fun a : Σ a : α, Fin (d a+1) => fun x => (Q a.1 x).coeff a.2)
    (fun a => hQ a.1 a.2)
  intro x hx y hy he
  apply forall_congr'
  intro a
  have hh := degree_data_of_coeff_sign_eq (coeff_sign_ext_of_bound
    (hq a x hx) (hq a y hy) (fun k => he ⟨a,k⟩))
  simp only [ne_eq,hh.1]

theorem polynomialSignSet_exists_signs {X ι α : Type*} [Fintype α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (d : α → ℕ) (Q : α → X → ℝ[X])
    (hQ : ∀ a, RationalPolynomialOn c S (Q a))
    (hq : ∀ a x, x ∈ S → (Q a x).natDegree ≤ d a)
    (σ : α → SignType) :
    PolynomialSignSet c (S ∩ {x | ∃ y : ℝ, ∀ a, SignType.sign ((Q a x).eval y) = σ a}) := by
  classical
  let T := fun J : Finset α => S ∩ {x | ∀ a, Q a x ≠ 0 ↔ a ∈ J}
  have hT (J : Finset α) : PolynomialSignSet c (T J) :=
    polynomialSignSet_nonzero_mask hS d Q hQ hq J
  have hJ (J : Finset α) : PolynomialSignSet c
      (T J ∩ {x | ∃ y : ℝ, ∀ a, SignType.sign ((Q a x).eval y) = σ a}) := by
    let P := fun x => ∏ a : J, Q a.val x
    let N := ∑ a : J, d a.val
    have hp : RationalPolynomialOn c (T J) P :=
      RationalPolynomialOn.prod univ _ (fun a _ => (hQ a.val).mono inter_subset_left)
    have hpn (x : X) (hx : x ∈ T J) : P x ≠ 0 :=
      prod_ne_zero_iff.mpr (fun a _ => (hx.2 a.val).mpr a.property)
    have hpd (x : X) (hx : x ∈ T J) : (P x).natDegree ≤ N :=
      (natDegree_prod_le _ _).trans (sum_le_sum (fun a _ => hq a.val x hx.1))
    let U := fun n : Fin (N+1) => T J ∩ {x | P x ≠ 0 ∧ (P x).natDegree = n.val}
    have hU (n : Fin (N+1)) : PolynomialSignSet c (U n) :=
      degree_stratum_signSet (hT J) P N n hp hpd
    have hn (n : Fin (N+1)) : PolynomialSignSet c
        (U n ∩ {x | ∃ y : ℝ, ∀ a, SignType.sign ((Q a x).eval y) = σ a}) := by
      let R := fun x => P x * criticalSampler (P x)
      have hrp : RationalPolynomialOn c (U n) P := hp.mono inter_subset_left
      have hrr : RationalPolynomialOn c (U n) R :=
        hrp.mul (hrp.criticalSampler n (fun x hx => hx.2.2))
      have hrs (x : X) (hx : x ∈ U n) : R x ≠ 0 ∧ ∀ y : ℝ, ∃ z : ℝ,
          (R x).eval z = 0 ∧ ∀ a, SignType.sign ((Q a x).eval z) = SignType.sign ((Q a x).eval y) := by
        have hs := sample_all_chambers (fun a : J => Q a.val x)
          (fun a => (hx.1.2 a.val).mpr a.property)
        refine ⟨hs.1,fun y => ?_⟩
        obtain ⟨z,hz,hsg⟩ := hs.2 y
        refine ⟨z,hz,fun a => ?_⟩
        by_cases ha : a ∈ J
        · exact hsg ⟨a,ha⟩
        · have ha0 : Q a x = 0 := by simpa only [not_ne_iff] using mt (hx.1.2 a).mp ha
          simp only [ha0,eval_zero]
      have hrd (x : X) (hx : x ∈ U n) : (R x).natDegree ≤ 2*n.val+2 := by
        have hb := natDegree_mul_le (p := P x) (q := criticalSampler (P x))
        have hc := criticalSampler_natDegree_le (P x)
        rw [hx.2.2] at hb hc
        change (P x * criticalSampler (P x)).natDegree ≤ _
        omega
      have hh := polynomialSignSet_root_signs (hU n) (2*n.val+2) d R Q hrr
        (fun a => (hQ a).mono (inter_subset_left.trans inter_subset_left))
        (fun x hx => ⟨(hrs x hx).1,hrd x hx⟩) (fun a x hx => hq a x hx.1.1) σ
      convert hh using 1
      ext x
      simp only [mem_inter_iff,mem_ofPred_eq]
      apply and_congr_right
      intro hx
      constructor
      · rintro ⟨y,hy⟩
        obtain ⟨z,hz,hs⟩ := (hrs x hx).2 y
        exact ⟨z,hz,fun a => (hs a).trans (hy a)⟩
      · rintro ⟨y,_,hy⟩
        exact ⟨y,hy⟩
    have hh := PolynomialSignSet.exists_finite _ hn
    convert hh using 1
    ext x
    simp only [mem_inter_iff,mem_ofPred_eq]
    constructor
    · rintro ⟨hx,hy⟩
      exact ⟨⟨(P x).natDegree,Nat.lt_succ_of_le (hpd x hx)⟩,⟨hx,hpn x hx,rfl⟩,hy⟩
    · rintro ⟨n,⟨hx,_⟩,hy⟩
      exact ⟨hx,hy⟩
  have hh := PolynomialSignSet.exists_finite _ hJ
  convert hh using 1
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq]
  constructor
  · rintro ⟨hx,hy⟩
    refine ⟨univ.filter (fun a => Q a x ≠ 0),⟨hx,fun a => ?_⟩,hy⟩
    simp
  · rintro ⟨J,⟨hx,_⟩,hy⟩
    exact ⟨hx,hy⟩

end Release061.SignElimination

end

end OAI
