import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedDeletion
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedSupportTrim

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] {α : I→Type*}

def readyFailure (choose : ∀ i,α i→Domains A B→Option C)
    (S : Finset A) (T : Finset B) (bad : Prop)
    (i : I) (V : Domains A B) (x : α i) : ℝ :=
  if ¬((S∩V.1).card:ℝ)<(9/10:ℝ)*S.card ∧
      ¬((T∩V.2).card:ℝ)<(9/10:ℝ)*T.card ∧ ¬bad
    then trialFailure choose i V x else 0

theorem failure_partition (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (i : I)
    (S : Finset A) (T : Finset B) (bad : Prop) (t : BinaryTree I) (U : Domains A B) :
    produced choose read i (trialFailure choose i) t U z≤
      (if firstTrim choose read S i t U z then (1:ℝ) else 0)+
      (if secondTrim choose read T i t U z then (1:ℝ) else 0)+
      (if bad then (1:ℝ) else 0)+
      produced choose read i (readyFailure choose S T bad i) t U z := by
  unfold produced
  cases ha : arrive choose read z i t U with
  | none=>
    by_cases hb : bad <;> simp [firstTrim,secondTrim,ha,hb]
  | some V=>
    have hS : firstTrim choose read S i t U z ↔
        ((S∩V.1).card:ℝ)<(9/10:ℝ)*S.card := by simp [firstTrim,ha]
    have hT : secondTrim choose read T i t U z ↔
        ((T∩V.2).card:ℝ)<(9/10:ℝ)*T.card := by simp [secondTrim,ha]
    rw [hS,hT]
    by_cases hs : ((S∩V.1).card:ℝ)<(9/10:ℝ)*S.card <;>
      by_cases ht : ((T∩V.2).card:ℝ)<(9/10:ℝ)*T.card <;>
      by_cases hb : bad <;> by_cases hc : choose i (z i) V=none <;>
      norm_num [readyFailure,trialFailure,hs,ht,hb,hc]

variable [Fintype I] [Fintype Ω] [∀ i,Fintype (α i)]

theorem averaged_failure_budget (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C) (i : I)
    (S : Ω→Finset A) (T : Ω→Finset B) (bad : Ω→Prop)
    (t : BinaryTree I) (U : Domains A B) (F G D ρ : ℝ) (hρ : 0≤ρ)
    (hfirst : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (if firstTrim (choose ω) (read ω) (S ω) i t U z then (1:ℝ) else 0)))≤F)
    (hsecond : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (if secondTrim (choose ω) (read ω) (T ω) i t U z then (1:ℝ) else 0)))≤G)
    (hdensity : (∑ ω,μ.mass ω*(if bad ω then (1:ℝ) else 0))≤D)
    (hready : ∀ ω V,(∑ x,(p i).mass x*readyFailure (choose ω) (S ω) (T ω) (bad ω) i V x)≤ρ) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      produced (choose ω) (read ω) i (trialFailure (choose ω) i) t U z))≤F+G+D+ρ := by
  have hprodω (ω : Ω) : (∑ z,(piLaw p).mass z*
      produced (choose ω) (read ω) i (readyFailure (choose ω) (S ω) (T ω) (bad ω) i) t U z)≤ρ :=
    produced_bound p (choose ω) (read ω) i (dummy i) _ t U ρ hρ (hready ω)
  have hprod : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      produced (choose ω) (read ω) i (readyFailure (choose ω) (S ω) (T ω) (bad ω) i) t U z))≤ρ := by
    calc
      _ ≤ ∑ ω,μ.mass ω*ρ := sum_le_sum (fun ω _=>mul_le_mul_of_nonneg_left (hprodω ω) (μ.nonneg ω))
      _ = ρ := by rw [←sum_mul,μ.total,one_mul]
  have hpart : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      produced (choose ω) (read ω) i (trialFailure (choose ω) i) t U z))≤
      ∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*((if firstTrim (choose ω) (read ω) (S ω) i t U z then (1:ℝ) else 0)+
        (if secondTrim (choose ω) (read ω) (T ω) i t U z then (1:ℝ) else 0)+
        (if bad ω then (1:ℝ) else 0)+produced (choose ω) (read ω) i
          (readyFailure (choose ω) (S ω) (T ω) (bad ω) i) t U z)) := by
    apply sum_le_sum
    intro ω _
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg ω)
    apply sum_le_sum
    intro z _
    exact mul_le_mul_of_nonneg_left
      (failure_partition (choose ω) (read ω) z i (S ω) (T ω) (bad ω) t U) ((piLaw p).nonneg z)
  simp_rw [mul_add,sum_add_distrib] at hpart
  simp only [←sum_mul,(piLaw p).total,one_mul] at hpart
  simp_rw [mul_add,sum_add_distrib] at hpart
  linarith

theorem original_deletion_quadratic (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C)
    (S : Ω→I→Finset A) (T : Ω→I→Finset B) (bad : Ω→I→Prop)
    (target : I) (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (ε D ρ : ℝ) (hε : 0≤ε) (hD : 0≤D) (hρ : 0≤ρ)
    (hfirst : ∀ i∈plannedPath target t,(∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (if firstTrim (choose ω) (read ω) (S ω i) i t U z then (1:ℝ) else 0)))≤10*t.height*ε)
    (hsecond : ∀ i∈plannedPath target t,(∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (if secondTrim (choose ω) (read ω) (T ω i) i t U z then (1:ℝ) else 0)))≤10*t.height*ε)
    (hdensity : ∀ i∈plannedPath target t,(∑ ω,μ.mass ω*(if bad ω i then (1:ℝ) else 0))≤D)
    (hready : ∀ i∈plannedPath target t,∀ ω V,
      (∑ x,(p i).mass x*readyFailure (choose ω) (S ω i) (T ω i) (bad ω i) i V x)≤ρ) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*(1-pivotSuccess (choose ω) (read ω) target t U z)))≤
      20*ε*t.height^2+(D+ρ)*t.height := by
  have hloc (i : I) (hi : i∈plannedPath target t) :
      (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
        produced (choose ω) (read ω) i (trialFailure (choose ω) i) t U z))≤
        20*t.height*ε+D+ρ := by
    have h:=averaged_failure_budget μ p dummy choose read i (fun ω=>S ω i) (fun ω=>T ω i)
      (fun ω=>bad ω i) t U (10*t.height*ε) (10*t.height*ε) D ρ hρ
      (hfirst i hi) (hsecond i hi) (hdensity i hi) (hready i hi)
    linarith
  have he (ω : Ω) :
      (∑ z,(piLaw p).mass z*(1-pivotSuccess (choose ω) (read ω) target t U z))=
      ∑ i∈plannedPath target t,(∑ z,(piLaw p).mass z*
        produced (choose ω) (read ω) i (trialFailure (choose ω) i) t U z) := by
    simp_rw [deletion_eq_path (choose ω) (read ω) _ target t U ht hmem,mul_sum]
    rw [sum_comm]
  simp_rw [he,mul_sum]
  rw [sum_comm]
  simp_rw [mul_sum] at hloc
  calc
    _ ≤ ∑ _i∈plannedPath target t,(20*t.height*ε+D+ρ) := sum_le_sum (fun i hi=>hloc i hi)
    _ = ((plannedPath target t).card:ℝ)*(20*t.height*ε+D+ρ) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ (t.height:ℝ)*(20*t.height*ε+D+ρ) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast plannedPath_card target t)
      positivity
    _ = _ := by ring

end
end SharpLogRamsey.FreshExecution

end

end OAI
