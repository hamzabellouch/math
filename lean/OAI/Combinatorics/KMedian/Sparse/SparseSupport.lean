import Mathlib
import OAI.Combinatorics.KMedian.Geometry.TrimIntegerLaw
import OAI.Combinatorics.KMedian.Sparse.SparseIntegerLaw
import OAI.Combinatorics.KMedian.Sparse.SparseAlgorithm

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem trim_positive (μ : SparseIntegerLaw α) (a : Fin μ.trim.length) :
    0 < μ.trim.law.rational.weight a := by
  change Fin μ.law.support.card at a
  change 0 < μ.law.trim.rational.weight a
  rw [IntegerLaw.trim_weight]
  unfold IntegerLaw.rational
  apply div_pos
  · have hh := (μ.law.mem_support _).mp (orderEmbOfFin_mem μ.law.support rfl a)
    exact_mod_cast lt_of_le_of_ne (μ.law.numerator_nonneg _) (Ne.symm hh)
  · exact_mod_cast μ.law.denominator_pos

theorem compressAuto_positive {d : ℕ} (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ)
    (a : Fin (μ.compressAuto v).length) : 0 < (μ.compressAuto v).law.rational.weight a := by
  exact (⟨μ.length,μ.states,μ.law.compressAuto (fun i => v μ.states[i.val])⟩ :
    SparseIntegerLaw α).trim_positive a

theorem zero_indicator (μ : SparseIntegerLaw α) (P : α → Prop) [DecidablePred P]
    (hz : μ.moment (fun x => if P x then 1 else 0)=0)
    (a : Fin μ.length) (ha : 0 < μ.law.rational.weight a) : ¬P μ.states[a.val] := by
  intro hpa
  have hs := single_le_sum (s := univ)
    (f := fun i : Fin μ.length => μ.law.rational.weight i*(if P μ.states[i.val] then 1 else 0))
    (fun i _ => mul_nonneg (μ.law.rational.nonneg _) (by split_ifs <;> norm_num)) (mem_univ a)
  change _ ≤ μ.moment (fun x => if P x then 1 else 0) at hs
  rw [hz,ite_eq_left hpa,mul_one] at hs
  exact (not_lt_of_ge hs) ha

theorem one_indicator (μ : SparseIntegerLaw α) (P : α → Prop) [DecidablePred P]
    (hz : μ.moment (fun x => if P x then 1 else 0)=1)
    (a : Fin μ.length) (ha : 0 < μ.law.rational.weight a) : P μ.states[a.val] := by
  by_contra hn
  have hs := single_le_sum (s := univ)
    (f := fun i : Fin μ.length => μ.law.rational.weight i*(if P μ.states[i.val] then 0 else 1))
    (fun i _ => mul_nonneg (μ.law.rational.nonneg _) (by split_ifs <;> norm_num)) (mem_univ a)
  have hsum : (∑ i : Fin μ.length, μ.law.rational.weight i*(if P μ.states[i.val] then 0 else 1))=0 := by
    have hh : ∀ i : Fin μ.length,
        μ.law.rational.weight i*(if P μ.states[i.val] then 0 else 1)=
          μ.law.rational.weight i-μ.law.rational.weight i*(if P μ.states[i.val] then 1 else 0) := by
      intro i
      split_ifs <;> ring
    simp_rw [hh]
    rw [sum_sub_distrib,μ.law.rational.total]
    change 1-μ.moment (fun x => if P x then 1 else 0)=0
    rw [hz,sub_self]
  rw [hsum,ite_eq_right hn,mul_one] at hs
  exact (not_lt_of_ge hs) ha

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
