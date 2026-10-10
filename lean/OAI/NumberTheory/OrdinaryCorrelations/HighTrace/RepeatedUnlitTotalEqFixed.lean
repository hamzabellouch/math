import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeSplit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.NumericalLine
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TiltedListLocalMean
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LinePrimeCode

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma repeatedUnlitTotal_eq_fixed (w : ClosedLine h ℓ) (r : S.Residues) :
    repeatedUnlitTotal w r=repeatedCenterUnlitCount w ((S.binarySplit w r).1) := by
  apply sum_congr rfl
  intro p hp
  by_cases hc : S.IsCore p
  · simp only [repeatedUnlitLocal,hc,not_true_eq_false,false_and,ite_false,ite_true]
  · simp only [hc,ite_false,repeatedUnlitLocal,not_false_eq_true,true_and]
    by_cases hm : 2 ≤ S.occurrenceCount w p
    · have hf : S.IsFixed w p := by
        have hne : (univ.filter (fun i : Fin ℓ => (p:ℕ) ∣ w.label i)).Nonempty := by
          rw [←card_pos]; exact lt_of_lt_of_le (by norm_num) hm
        obtain ⟨i,hi⟩ := hne
        exact ⟨⟨i,(mem_filter.mp hi).2⟩,Or.inr hm⟩
      simp only [hm,ite_true,fixedUnlitCount,dite_eq_left hf]
      rfl
    · have hf : ¬S.IsFixed w p := fun hf => hf.2.elim hc hm
      simp only [hm,ite_false,fixedUnlitCount,dite_eq_right hf]

namespace NumericalLine

def unlitTailSum {T : ℝ} (D : S.DivisorFamily B τ C₀) (h ℓ L : ℕ) (cut : S.Cutoffs T) (t : ℕ) : ℝ :=
  ∑ w : NumericalLine D h ℓ, avg (fun r : S.Residues => if t ≤ repeatedUnlitTotal w.line r then
    |S.chronologicalKernel w.line cut r*allowedIndicator w.line D L r| else 0)

def unlitPrefactor (S : PrimeSystem) (ℓ J : ℕ) : ℝ :=
  A^(ℓ*J)*((ℓ:ℝ)+2)^(ℓ*J)*lineMassBound S ℓ J

lemma unlit_tail_sum_bound {T : ℝ} (D : S.DivisorFamily B τ C₀) (cut : S.Cutoffs T)
    (z : ℝ) (hz : 1 ≤ z) (hzp : ∀ p : S.Index,z^2 ≤ (p:ℝ)) (t : ℕ) :
    unlitTailSum D h ℓ L cut t * z^t ≤ unlitPrefactor S ℓ ⌈C₀*Real.log B⌉₊ := by
  have hp (w : NumericalLine D h ℓ) :
      (avg (fun r : S.Residues => if t ≤ repeatedUnlitTotal w.line r then
        |S.chronologicalKernel w.line cut r*allowedIndicator w.line D L r| else 0))*z^t ≤
      (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*w.lineReciprocalWeight := by
    have hh := repeated_unlit_tail_integral w.line w.labels cut
      ([] : List (AttachedSpec w.line D 0)) z hz hzp t
    have hc : (fullUsedIndices w.line ([] : List (AttachedSpec w.line D 0))).card ≤ ℓ*⌈C₀*Real.log B⌉₊ := by
      simpa using fullUsedIndices_card_le w.line ([] : List (AttachedSpec w.line D 0)) w.labels
    calc
      _ ≤ (avg (fun r : S.Residues => if t ≤ repeatedUnlitTotal w.line r then
          |S.kernel w.line cut r| *listIndicator w.line ([] : List (AttachedSpec w.line D 0)) r else 0))*z^t := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hz) _)
        apply avg_mono
        intro r
        split_ifs with ht
        · rw [chronologicalKernel_eq]
          have hi : listIndicator w.line ([] : List (AttachedSpec w.line D 0)) r=1 := by simp [listIndicator]
          rw [hi,mul_one]
          unfold allowedIndicator
          split_ifs <;> simp
        · exact le_rfl
      _ ≤ _ := hh
      _ ≤ _ := by
        rw [lineReciprocalWeight,linePrimeCode_support]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg A_pos.le _)
        exact pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg ℓ : (0:ℝ) ≤ (ℓ:ℝ))] : 1 ≤ (ℓ:ℝ)+2) hc
  unfold unlitTailSum unlitPrefactor
  rw [sum_mul]
  calc
    _ ≤ ∑ w : NumericalLine D h ℓ,
        (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*w.lineReciprocalWeight :=
      sum_le_sum (fun w hw => hp w)
    _ = (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*
        ∑ w : NumericalLine D h ℓ,w.lineReciprocalWeight := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left sum_lineReciprocalWeight_le
      (mul_nonneg (pow_nonneg A_pos.le _) (by positivity))

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
