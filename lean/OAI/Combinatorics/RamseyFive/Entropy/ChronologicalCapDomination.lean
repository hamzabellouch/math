import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.TwoPublicCaps
import OAI.Combinatorics.RamseyFive.Decoding.ProducedCapExclusion

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma adaptive_event_first (p : Law α) (next : α→Law β) (P : α→Prop) :
    eventMass (adaptiveLaw p next) (Finset.univ.filter fun ab=>P ab.1)=
    eventMass p (Finset.univ.filter P) := by
  simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,adaptiveLaw]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a
  · simp only [h,ite_true,←Finset.mul_sum,(next a).sum_one,mul_one]
  · simp [h]

lemma adaptive_event_second (p : Law α) (next : α→Law β) (P : β→Prop) :
    eventMass (adaptiveLaw p next) (Finset.univ.filter fun ab=>P ab.2)=
    ∑a,p a*eventMass (next a) (Finset.univ.filter P) := by
  simp only [eventMass,Finset.sum_filter,Fintype.sum_prod_type,adaptiveLaw,
    Finset.mul_sum,mul_ite,mul_zero]

lemma adaptive_event_second_le (p : Law α) (next : α→Law β) (P : β→Prop)
    (B : ℝ) (h : ∀a,eventMass (next a) (Finset.univ.filter P)≤B) :
    eventMass (adaptiveLaw p next) (Finset.univ.filter fun ab=>P ab.2)≤B := by
  rw [adaptive_event_second]
  calc
    _ ≤ ∑a,p a*B := Finset.sum_le_sum fun a _=>mul_le_mul_of_nonneg_left (h a) (p.nonneg a)
    _ = B := by rw [←Finset.sum_mul,p.sum_one,one_mul]
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical
lemma excludes_pure_none {A : Type*} [Fintype A] (a : A) :
    eventMass (pureLaw (none : Option (Finset A))) (Finset.univ.filter (Excludes a))=0 := by
  unfold eventMass
  apply Finset.sum_eq_zero
  intro Y hY
  have h := (Finset.mem_filter.mp hY).2
  cases Y <;> simp_all [Excludes,pureLaw]
end SharpRamseyFive.ReverseCap
namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem nextCapLaw_domination {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (A UA : Finset (ℙ K V)) (hA : A.Nonempty) (hAU : A⊆UA)
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤(9:ℝ)/10*A.card*B.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((UA.card:ℝ)/A.card)≤n)
    (MB : ℝ) (Y : Option (Finset (ℙ K (Dual K V))))
    (a : ℙ K V) (ha : a∈UA) :
    eventMass (nextCapLaw A UA B UB hB n (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^(d+1)/B.card) MB Y)
      (Finset.univ.filter (Excludes a))≤
    (50*(Nat.card K:ℝ)/(9*((9:ℝ)/10)))*(((B.filter (Incident a)).card:ℝ)/B.card) := by
  have hq0 : (0:ℝ)<Nat.card K := lt_of_lt_of_le (by norm_num : (0:ℝ)<3) (by exact_mod_cast hq)
  cases Y with
  | none =>
    change eventMass (pureLaw (none : Option (Finset (ℙ K V))))
      (Finset.univ.filter (Excludes a))≤_
    rw [excludes_pure_none]
    positivity
  | some Y =>
    dsimp only [nextCapLaw]
    split_ifs with hY
    · have hC := hY.source_nonempty hB
      exact publicCapLaw_domination Incident A UA (B∩Y) B Y hC
        (hC.mono Finset.inter_subset_right) Finset.inter_subset_right Finset.inter_subset_left
        n hn (Nat.card K) (9/10) _ hq0 (by norm_num) hY.2.2
        (geometric_validation_mass hdim hd hq A UA hA hAU B (B∩Y) hC
          Finset.inter_subset_left (9/10) (by norm_num) (by norm_num) hY.2.2 hsparse n hn hlen) a ha
    · rw [excludes_pure_none]
      positivity

theorem second_cap_unconditioned {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (A UA : Finset (ℙ K V)) (hA : A.Nonempty) (hAU : A⊆UA)
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤(9:ℝ)/10*A.card*B.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((UA.card:ℝ)/A.card)≤n)
    (MB : ℝ) (p : Law (Option (Finset (ℙ K (Dual K V)))))
    (a : ℙ K V) (ha : a∈UA) :
    eventMass (adaptiveLaw p (nextCapLaw A UA B UB hB n (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^(d+1)/B.card) MB))
      (Finset.univ.filter (fun caps=>Excludes a caps.2))≤
    (50*(Nat.card K:ℝ)/(9*((9:ℝ)/10)))*(((B.filter (Incident a)).card:ℝ)/B.card) := by
  apply adaptive_event_second_le
  intro Y
  exact nextCapLaw_domination hdim hd hq A UA hA hAU B UB hB hsparse n hn hlen MB Y a ha

end SharpRamseyFive.ProjectiveIncidence

end OAI
