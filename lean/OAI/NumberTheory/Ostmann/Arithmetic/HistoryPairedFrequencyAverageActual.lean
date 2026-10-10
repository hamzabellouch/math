import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageCount

namespace OAI

open Erdos970

noncomputable section
open Filter
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Characters FrequencyExposure FrequencyTreeSum BinaryExposure
open PairedFrequencyActualBudget Conclusion

theorem actual_frequency_average_eventually {Bs BD Bz : ℝ}
    (hBs : 0≤Bs) (hBD : 0≤BD) (hBz : 0≤Bz) {k : ℕ} (hk : 0<k)
    {ρ : ℝ} (hρ : 0<ρ) :
    ∀ᶠ L : ℝ in atTop, ∀ l≤k,
      ∀ Q : Assignment (pairedRanges Bs BD Bz k L l) l [] → ℕ,
      ∀ [∀x,NeZero (Q x)],
      ∀ hx : ∀x,LabelsDivide (pairedRanges Bs BD Bz k L l) (Q x) x,
      ∀ H : Assignment (pairedRanges Bs BD Bz k L l) l [] → Type,
      ∀ a : ∀x q,Coefficients (H x)
        (localData (pairedRanges Bs BD Bz k L l) (Q x) x (hx x) q),
      ∀ left right : ∀x,List Bool → H x → (ZMod (Q x))ˣ → (ZMod (Q x))ˣ → H x,
      ∀ h : ∀x,H x,
      ∀ guard : ∀x,BinaryHaar.Leaves (ZMod (Q x))ˣ l → Prop,
      (∑x : Assignment (pairedRanges Bs BD Bz k L l) l [],
        localGuardedAverage (pairedRanges Bs BD Bz k L l) x (Q x) (hx x)
          (H x) (a x) (left x) (right x) (h x) (guard x)) ≤
        Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ)) := by
  obtain ⟨ε,δ,hε,hδ,C,hC,D,hD,hcount,htotal,hscale⟩ :=
    exists_actual_paired_frequency_bound hBs hBD hBz hk hρ
  filter_upwards [hscale] with L hL
  intro l hl Q _ hx H a left right h guard
  exact (sum_localGuardedAverage_le_total hcount (pairedRanges Bs BD Bz k L l)
    l [] Q hx H a left right h guard).trans (hL l hl).2

theorem assignment_precision_admissible {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {l : ℕ}
    (x : Assignment (pairedRanges Bs BD Bz k L l) l []) (n : ℕ) (hn : 0<n) :
    assignmentModulus (pairedRanges Bs BD Bz k L l) x ^ n ≠ 0 ∧
      LabelsDivide (pairedRanges Bs BD Bz k L l)
        (assignmentModulus (pairedRanges Bs BD Bz k L l) x ^ n) x := by
  have hS : ∀p s,s∈pairedRanges Bs BD Bz k L l p→s.1≠0∧s.2≠0 := by
    intro p s hs
    have h := (mem_pairedRanges Bs BD Bz k L l p s).mp hs
    exact ⟨h.1.1,h.2.1⟩
  refine ⟨pow_ne_zero _ (assignmentModulus_ne_zero _ hS x),?_⟩
  exact labelsDivide_mono _ (dvd_pow_self _ hn.ne') x (labelsDivide_assignmentModulus _ x)

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
