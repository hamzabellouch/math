import Mathlib
import OAI.Probability.SKBarriers.Replicas.ReplicaSampling
import OAI.Probability.SKBarriers.Dynamics.BankCoverage

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

theorem iid_gibbs_oriented_permuted_replica {n d : ℕ} (β : ℝ) (J : Disorder n)
    (ε : Fin d → Bool) (e : Equiv.Perm (Fin d)) (S : Finset (ReplicaConfig n d)) :
    ((gibbsFiniteLaw β J).iid (Fin d)).prob (fun z => (fun i => orient (ε i) (z (e i)))∈S)=replicaGibbsMass β J S := by
  have H := (gibbsFiniteLaw β J).iid_expect_equiv e.symm
    (fun z => if (fun i => orient (ε i) (z i))∈S then 1 else 0)
  simp only [Equiv.symm_symm,Function.comp_def,FiniteLaw.expect_indicator_eq_prob] at H
  exact H.trans (iid_gibbs_oriented_replica β J ε S)

theorem bank_pair_vertex_permuted {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (J : Disorder n) (a b : I) (hab : a≠b)
    (ε : Fin 3 → Bool) (e : Equiv.Perm (Fin 3)) (S : Finset (ReplicaConfig n 3)) :
    ((gibbsFiniteLaw β J).iid I).expect (fun z => (gibbsFiniteLaw β J).prob (fun x =>
      (fun i => orient (ε i) ((![z a,z b,x] : ReplicaConfig n 3) (e i)))∈S))=
      replicaGibbsMass β J S := by
  have H := (gibbsFiniteLaw β J).iid_two_then_one a b hab
    (fun z => if (fun i => orient (ε i) (z (e i)))∈S then 1 else 0)
  simp only [FiniteLaw.expect_indicator_eq_prob] at H
  exact H.trans (iid_gibbs_oriented_permuted_replica β J ε e S)

namespace FiniteLaw
variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]
theorem expect_prob_exists_le (P : FiniteLaw X) (Q : FiniteLaw Y) (E : A → X → Y → Prop) :
    P.expect (fun x => Q.prob (fun y => ∃ a,E a x y)) ≤ ∑ a, P.expect (fun x => Q.prob (E a x)) := by
  rw [← P.expect_sum]
  exact P.expect_mono (fun x => Q.prob_exists (fun a y => E a x y))
end FiniteLaw

def bankTripleBad {n : ℕ} {I : Type*} (level : I → ℕ) (S : Finset (ReplicaConfig n 3))
    (z : I → Config n) : Prop :=
  ∃ v : I × I × I × (Fin 3 → Bool),
    (level v.1≠level v.2.1 ∧ level v.1≠level v.2.2.1 ∧ level v.2.1≠level v.2.2.1) ∧
    (![orient (v.2.2.2 0) (z v.1),orient (v.2.2.2 1) (z v.2.1),orient (v.2.2.2 2) (z v.2.2.1)] : ReplicaConfig n 3)∈S

def bankVertexBad {n : ℕ} {I : Type*} (level : I → ℕ) (S : Finset (ReplicaConfig n 3))
    (z : I → Config n) (x : Config n) : Prop :=
  ∃ v : I × I × (Fin 3 → Bool) × Equiv.Perm (Fin 3),
    level v.1≠level v.2.1 ∧
    (fun i => orient (v.2.2.1 i) ((![z v.1,z v.2.1,x] : ReplicaConfig n 3) (v.2.2.2 i)))∈S

theorem bankTripleBad_prob {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (J : Disorder n) (level : I → ℕ) (S : Finset (ReplicaConfig n 3)) :
    ((gibbsFiniteLaw β J).iid I).prob (bankTripleBad level S) ≤
      8*(Fintype.card I:ℝ)^3*replicaGibbsMass β J S := by
  classical
  refine (FiniteLaw.prob_exists _ _).trans ?_
  calc
    _ ≤ ∑ _v : I × I × I × (Fin 3 → Bool), replicaGibbsMass β J S := by
      apply Finset.sum_le_sum
      rintro ⟨a,b,c,ε⟩ _
      by_cases h : level a≠level b ∧ level a≠level c ∧ level b≠level c
      · refine (FiniteLaw.prob_mono _ (fun z hz => hz.2)).trans ?_
        exact (bank_triple_oriented β J a b c
          (fun he => h.1 (congrArg level he)) (fun he => h.2.1 (congrArg level he)) (fun he => h.2.2 (congrArg level he))
          (ε 0) (ε 1) (ε 2) S).le
      · simp only [h,false_and,FiniteLaw.prob_false]
        exact replicaGibbsMass_nonneg β J S
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]; ring

theorem expected_bankVertexBad {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (β : ℝ) (J : Disorder n) (level : I → ℕ) (S : Finset (ReplicaConfig n 3)) :
    ((gibbsFiniteLaw β J).iid I).expect (fun z => (gibbsFiniteLaw β J).prob (bankVertexBad level S z)) ≤
      48*(Fintype.card I:ℝ)^2*replicaGibbsMass β J S := by
  classical
  refine (FiniteLaw.expect_prob_exists_le _ _ _).trans ?_
  calc
    _ ≤ ∑ _v : I × I × (Fin 3 → Bool) × Equiv.Perm (Fin 3), replicaGibbsMass β J S := by
      apply Finset.sum_le_sum
      rintro ⟨a,b,ε,e⟩ _
      by_cases h : level a≠level b
      · refine ((gibbsFiniteLaw β J).iid I).expect_mono (fun z => (gibbsFiniteLaw β J).prob_mono (fun x hx => hx.2)) |>.trans ?_
        exact (bank_pair_vertex_permuted β J a b (fun he => h (congrArg level he)) ε e S).le
      · simp only [h,false_and,FiniteLaw.prob_false,FiniteLaw.expect_const]
        exact replicaGibbsMass_nonneg β J S
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Fintype.card_perm,nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]; norm_num [Nat.factorial]; ring_nf; simp

theorem exists_fixed_good_bank {n p : ℕ} (β : ℝ) (J : Disorder n) (K : Fin p → ℕ)
    (pred : Fin p → Finset (Fin p)) (hpred : ∀ j, j∉pred j) (t q : ℝ) (a δ : Fin p → ℝ)
    (ha : ∀ j,0≤a j) (S : Finset (ReplicaConfig n 3))
    (hcov : ∀ j, ∀ w : BankPrior pred j → Config n,
      (gibbsFiniteLaw β J).prob (fun x => (∀i,|overlap (w i) x|≤3*t) ∧
        (gibbsFiniteLaw β J).prob (fun y => (∀i,|overlap (w i) y|≤3*t) ∧ q≤|overlap x y|)<a j)≤δ j)
    (E : ℝ)
    (hE : (8*(Fintype.card (BankIndex K):ℝ)^3+48*(Fintype.card (BankIndex K):ℝ)^2)*replicaGibbsMass β J S+
      (∑ j, Fintype.card (BankTuple K pred j)*(δ j+Real.exp (-(a j)*(K j)))) ≤ E)
    (hE1 : E<1) :
    ∃ z : BankIndex K → Config n,
      ¬bankTripleBad (fun i : BankIndex K => i.1.val) S z ∧
      (gibbsFiniteLaw β J).prob (fun x => bankCoverageBad K pred t q z x ∨
        bankVertexBad (fun i : BankIndex K => i.1.val) S z x) ≤ E := by
  classical
  let P := gibbsFiniteLaw β J
  let Q := P.iid (BankIndex K)
  let level (i : BankIndex K) := i.1.val
  let V (z : BankIndex K → Config n) (x : Config n) := bankCoverageBad K pred t q z x ∨ bankVertexBad level S z x
  let f (z : BankIndex K → Config n) : ℝ := (if bankTripleBad level S z then 1 else 0)+P.prob (V z)
  have H : Q.expect f ≤ E := by
    rw [show Q.expect f=Q.prob (bankTripleBad level S)+Q.expect (fun z => P.prob (V z)) from by
      dsimp only [f]; rw [FiniteLaw.expect_add,FiniteLaw.expect_indicator_eq_prob]]
    have HV : Q.expect (fun z => P.prob (V z)) ≤
        Q.expect (fun z => P.prob (bankCoverageBad K pred t q z))+Q.expect (fun z => P.prob (bankVertexBad level S z)) := by
      rw [← FiniteLaw.expect_add]
      exact Q.expect_mono (fun z => P.prob_or _ _)
    have HC := expected_bank_coverage_bad P K pred hpred t q a δ ha hcov
    have HT := bankTripleBad_prob β J level S
    have HB := expected_bankVertexBad β J level S
    dsimp only [P,Q] at HC HV ⊢
    nlinarith only [HV,HC,HT,HB,hE]
  obtain ⟨z,hz⟩ := Q.exists_le_expect f
  have hzE : f z≤E := hz.trans H
  have hnot : ¬bankTripleBad level S z := by
    intro hbad
    have H0 := P.prob_nonneg (V z)
    simp only [f,ite_eq_left hbad] at hzE
    linarith only [hzE,hE1,H0]
  refine ⟨z,hnot,?_⟩
  simpa only [f,ite_eq_right hnot,zero_add] using hzE

end SK.Analytic

end
end

end OAI
