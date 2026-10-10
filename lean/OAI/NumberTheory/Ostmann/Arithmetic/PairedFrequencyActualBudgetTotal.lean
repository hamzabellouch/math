import OAI.NumberTheory.Ostmann.Arithmetic.PairedFrequencyActualBudget

namespace OAI

noncomputable section
open Filter
open scoped BigOperators
namespace Ostmann.Arithmetic.PairedFrequencyActualBudget
open Conclusion Characters

def LeafCountConstant (ε : ℝ) (C : NNReal) : Prop :=
  ∀ Q : ℕ, ∀ [NeZero Q], ∀ H : Type,
    ∀ d : List Bool→FrequencyExposure.Data Q,
    ∀ a : ∀p,FrequencyExposure.Coefficients H (d p),
    ∀ left right : List Bool→H→(ZMod Q)ˣ→(ZMod Q)ˣ→H, ∀ j p h,
    (Nat.card {z : BinaryHaar.Leaves (ZMod Q)ˣ j //
      BinaryExposure.leafAdmissible (FrequencyExposure.constraint d a)
        (FrequencyExposure.update false left) (FrequencyExposure.update true right) j (p,h) z}:ℝ)/
      Nat.card (BinaryHaar.Leaves (ZMod Q)ˣ j) ≤
        ((FrequencyExposure.budget C ε d j p).value:ℝ)

theorem exists_actual_paired_frequency_bound {Bs BD Bz : ℝ}
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz)
    {k : ℕ} (hk : 0 < k) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∃ C : NNReal, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ LeafCountConstant ε C ∧
        (∀ L : ℝ, ∀ l : ℕ,
          FrequencyTreeSum.total (pairedRanges Bs BD Bz k L l)
            (PairedFrequencyTreeSum.factor (C:ℝ) ε) l [] ≤
              actualBudget (C:ℝ) D ε δ Bs BD Bz k L l) ∧
        (∀ᶠ L : ℝ in atTop, ∀ l ≤ k,
          actualBudget (C:ℝ) D ε δ Bs BD Bz k L l ≤
              Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ)) ∧
          FrequencyTreeSum.total (pairedRanges Bs BD Bz k L l)
            (PairedFrequencyTreeSum.factor (C:ℝ) ε) l [] ≤
              Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ))) := by
  obtain ⟨ε,δ,hε,hδ,hscale⟩ := exists_eventually_actualBudget_le hBs hBD hBz hk hρ
  obtain ⟨C,hC,hcount⟩ := FrequencyExposure.paired_frequency_leaf_count ε hε
  obtain ⟨D,hD,hlocal⟩ := PairedFrequencyTreeSum.total_le δ hδ
  have hsum (L : ℝ) (l : ℕ) :
      FrequencyTreeSum.total (pairedRanges Bs BD Bz k L l)
        (PairedFrequencyTreeSum.factor (C:ℝ) ε) l [] ≤
          actualBudget (C:ℝ) D ε δ Bs BD Bz k L l := by
    apply hlocal (C:ℝ) ε C.property hε.le
      (pairedRanges Bs BD Bz k L l) (addressBound Bs BD Bz k L l)
    · exact addressBound_pos hBs hBD hBz hk L l
    · intro p s hs
      exact (mem_pairedRanges Bs BD Bz k L l p s).mp hs
  refine ⟨ε,δ,hε,hδ,C,hC,D,hD,hcount,hsum,?_⟩
  filter_upwards [hscale (C:ℝ) D C.property hD] with L hL
  intro l hl
  exact ⟨hL l hl,(hsum L l).trans (hL l hl)⟩

end Ostmann.Arithmetic.PairedFrequencyActualBudget

end

end OAI
