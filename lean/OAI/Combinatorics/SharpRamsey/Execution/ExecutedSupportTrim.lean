import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedSecondTrim

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] [Fintype I] [Fintype Ω]
  {α : I→Type*} [∀ i,Fintype (α i)]

theorem averaged_path_bound (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C)
    (loss : Ω→∀ i,Domains A B→α i→ℝ)
    (t : BinaryTree I) (U : Domains A B) (J : Finset I)
    (M : Ω→ℝ) (hM : ∀ ω,0≤M ω) (budget : Ω→I→ℝ)
    (hb : ∀ ω,∀ i∈J,0≤budget ω i)
    (hlocal : ∀ ω,∀ i∈J,∀ V,(∑ x,(p i).mass x*loss ω i V x)≤budget ω i)
    (ε : ℝ) (hmean : ∀ i∈J,(∑ ω,μ.mass ω*(budget ω i/M ω))≤ε) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      ((∑ j∈J,produced (choose ω) (read ω) j (loss ω j) t U z)/M ω)))≤J.card*ε := by
  have hω (ω : Ω) : (∑ z,(piLaw p).mass z*
      ((∑ j∈J,produced (choose ω) (read ω) j (loss ω j) t U z)/M ω))≤
      ∑ j∈J,budget ω j/M ω := by
    simp_rw [←mul_div_assoc,←sum_div,mul_sum]
    rw [sum_comm]
    apply div_le_div_of_nonneg_right _ (hM ω)
    apply sum_le_sum
    intro j hj
    exact produced_bound p (choose ω) (read ω) j (dummy j) (loss ω j) t U
      (budget ω j) (hb ω j hj) (hlocal ω j hj)
  calc
    _ ≤ ∑ ω,μ.mass ω*(∑ j∈J,budget ω j/M ω) := by
      apply sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (hω ω) (μ.nonneg ω)
    _ = ∑ j∈J,∑ ω,μ.mass ω*(budget ω j/M ω) := by
      simp_rw [mul_sum]
      rw [sum_comm]
    _ ≤ ∑ _j∈J,ε := sum_le_sum (fun j hj=>hmean j hj)
    _ = _ := by simp only [sum_const,nsmul_eq_mul]

theorem averaged_charge_bound (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C)
    (loss : Ω→∀ i,Domains A B→α i→ℝ)
    (t : BinaryTree I) (U : Domains A B) (J : Finset I)
    (M : Ω→ℝ) (hM : ∀ ω,0≤M ω) (budget : Ω→I→ℝ)
    (hb : ∀ ω,∀ i∈J,0≤budget ω i)
    (hlocal : ∀ ω,∀ i∈J,∀ V,(∑ x,(p i).mass x*loss ω i V x)≤budget ω i)
    (ε : ℝ) (hmean : ∀ i∈J,(∑ ω,μ.mass ω*(budget ω i/M ω))≤ε)
    (E : Ω→(∀ i,α i)→Prop)
    (hcharge : ∀ ω z,(if E ω z then (1:ℝ) else 0)≤
      (10/M ω)*∑ j∈J,produced (choose ω) (read ω) j (loss ω j) t U z) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*(if E ω z then (1:ℝ) else 0)))≤10*J.card*ε := by
  have hpath:=averaged_path_bound μ p dummy choose read loss t U J M hM budget hb hlocal ε hmean
  calc
    _ ≤ ∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*((10/M ω)*
        ∑ j∈J,produced (choose ω) (read ω) j (loss ω j) t U z)) := by
      apply sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (μ.nonneg ω)
      apply sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (hcharge ω z) ((piLaw p).nonneg z)
    _ = 10*(∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
        ((∑ j∈J,produced (choose ω) (read ω) j (loss ω j) t U z)/M ω))) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro ω _
      have hh : (∑ z,(piLaw p).mass z*((10/M ω)*
          ∑ j∈J,produced (choose ω) (read ω) j (loss ω j) t U z))=
          10*(∑ z,(piLaw p).mass z*((∑ j∈J,
            produced (choose ω) (read ω) j (loss ω j) t U z)/M ω)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro z _
        ring
      rw [hh]
      ring
    _ ≤ 10*(J.card*ε) := mul_le_mul_of_nonneg_left hpath (by norm_num)
    _ = _ := by ring

theorem original_first_trim (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read mask : Ω→∀ i,α i→CapReader A B C)
    (hread : ∀ ω i x U c,(read ω i x U c).1=U.1∩(mask ω i x U c).1)
    (target : I) (Y : Ω→Finset A) (hY : ∀ ω,(Y ω).Nonempty)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (hYU : ∀ ω,Y ω⊆U.1)
    (budget : Ω→I→ℝ) (hb : ∀ ω,∀ i∈leftPath target t,0≤budget ω i)
    (hlocal : ∀ ω,∀ i∈leftPath target t,∀ V,
      (∑ x,(p i).mass x*firstLoss (choose ω) (mask ω) (Y ω) i V x)≤budget ω i)
    (ε : ℝ) (hε : 0≤ε)
    (hmean : ∀ i∈leftPath target t,(∑ ω,μ.mass ω*(budget ω i/(Y ω).card))≤ε) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (if firstTrim (choose ω) (read ω) (Y ω) target t U z then (1:ℝ) else 0)))≤
      10*t.height*ε := by
  apply (averaged_charge_bound μ p dummy choose read
    (fun ω=>firstLoss (choose ω) (mask ω) (Y ω)) t U (leftPath target t)
    (fun ω=>((Y ω).card:ℝ)) (fun ω=>Nat.cast_nonneg _) budget hb hlocal ε hmean
    (fun ω=>firstTrim (choose ω) (read ω) (Y ω) target t U)
    (fun ω z=>reached_first_trim_charge (choose ω) (read ω) (mask ω) (hread ω)
      z target (Y ω) (hY ω) t U ht hmem (hYU ω))).trans
  have hh : ((leftPath target t).card:ℝ)≤t.height := by exact_mod_cast leftPath_card target t
  gcongr

theorem original_second_trim (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read mask : Ω→∀ i,α i→CapReader A B C)
    (hread : ∀ ω i x U c,(read ω i x U c).2=U.2∩(mask ω i x U c).2)
    (target : I) (Y : Ω→Finset B) (hY : ∀ ω,(Y ω).Nonempty)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (hYU : ∀ ω,Y ω⊆U.2)
    (budget : Ω→I→ℝ) (hb : ∀ ω,∀ i∈rightPath target t,0≤budget ω i)
    (hlocal : ∀ ω,∀ i∈rightPath target t,∀ V,
      (∑ x,(p i).mass x*secondLoss (choose ω) (mask ω) (Y ω) i V x)≤budget ω i)
    (ε : ℝ) (hε : 0≤ε)
    (hmean : ∀ i∈rightPath target t,(∑ ω,μ.mass ω*(budget ω i/(Y ω).card))≤ε) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (if secondTrim (choose ω) (read ω) (Y ω) target t U z then (1:ℝ) else 0)))≤
      10*t.height*ε := by
  apply (averaged_charge_bound μ p dummy choose read
    (fun ω=>secondLoss (choose ω) (mask ω) (Y ω)) t U (rightPath target t)
    (fun ω=>((Y ω).card:ℝ)) (fun ω=>Nat.cast_nonneg _) budget hb hlocal ε hmean
    (fun ω=>secondTrim (choose ω) (read ω) (Y ω) target t U)
    (fun ω z=>reached_second_trim_charge (choose ω) (read ω) (mask ω) (hread ω)
      z target (Y ω) (hY ω) t U ht hmem (hYU ω))).trans
  have hh : ((rightPath target t).card:ℝ)≤t.height := by exact_mod_cast rightPath_card target t
  gcongr

end
end SharpLogRamsey.FreshExecution

end

end OAI
