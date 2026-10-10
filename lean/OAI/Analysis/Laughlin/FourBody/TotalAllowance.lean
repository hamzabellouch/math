import OAI.Analysis.Laughlin.FourBody.Basic
import OAI.Analysis.Laughlin.FourBody.HaarAllowance

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators

theorem source_allowance_count_fin :
    (∑ n : Fin 23, ((n.val+2)/2) * ((n.val+2)^2/4)) = 10946 := by
  have he (n : ℕ) (f : ℕ → ℕ) :
      (∑ i ∈ Finset.range n, f i) = ((List.range n).map f).sum := by
    induction n with
    | zero => simp
    | succ n ih => simp only [Finset.sum_range_succ,List.range_succ,List.map_append,
        List.sum_append,List.map_singleton,List.sum_singleton,ih]
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => ((n+2)/2) * ((n+2)^2/4)) 23,he]
  exact Certificate.allowance_count

theorem physical_fourBody_total_haar_allowance (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (∑ d : Fin 23, ∑ i : Fin ((d.val+2)/2),
      (2*Q-2+1 : ℕ) * (∫ g, occupationNormSq Q
        (physicalFourCopyEnd Q (Certificate.copyLabel (D := d.val+1) i) (d.val+1) (by omega)
          (exteriorRotation Q g⁻¹ x)) ∂sourceHaar)) ≤
      10946 * sourceFockEnergy Q x := by
  calc
    _ ≤ ∑ d : Fin 23, ∑ _i : Fin ((d.val+2)/2),
        ((d.val+2)^2/4 : ℕ) * sourceFockEnergy Q x := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro i hi
      exact physical_fourBody_haar_allowance_retained Q (Certificate.copyLabel (D := d.val+1) i) (d.val+1)
        (by unfold Certificate.copyLabel; have := i.isLt; omega)
        (by exact ⟨i.val,by unfold Certificate.copyLabel; omega⟩) hQ (by omega) x
    _ = 10946 * sourceFockEnergy Q x := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← mul_assoc,
        ← Nat.cast_mul,← Finset.sum_mul,← Nat.cast_sum,source_allowance_count_fin,Nat.cast_ofNat]

end Laughlin.Fock

end OAI
