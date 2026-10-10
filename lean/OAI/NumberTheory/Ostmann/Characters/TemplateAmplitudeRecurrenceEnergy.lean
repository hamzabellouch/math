import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceElimination
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceRetained

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.RetainedRow
open Construction HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

section
variable {α γ : Type*} [Fintype α] [Fintype γ]
    (k j : ℕ) (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (μ : FinitePrior α) (ν : FinitePrior γ) (h : α → CopiedState k j)
    (y : γ → OutsideState k j) (S : List Bool → Finset ℤ) (path : List Bool)
    (R : Finset ℕ+) (phase : γ → ℕ+ → α → SupportedHistory S j path → ℂ)

def energy : ℝ := ν.mean (fun a => ∑P∈R,∑u,
  ‖grouped k j B V extra mask X Δ W μ h (y a) S path P (phase a P) u‖^2)

def diagonal : ℝ := ν.mean (fun a => ∑P∈R,
  (historyRowDiagonal k j μ h (y a) S path mask X Δ W P
    (fun x z => guardPhase k j B V extra P (h x) (y a) z.val (phase a P x z))).re)

def offDiagonal : ℂ := ν.cmean (fun a => ∑P∈R,
  historyRowOffDiagonal k j μ h (y a) S path mask X Δ W P
    (fun x z => guardPhase k j B V extra P (h x) (y a) z.val (phase a P x z)))

theorem diagonal_nonneg : 0≤diagonal k j B V extra mask X Δ W μ ν h y S path R phase := by
  apply FinitePrior.mean_nonneg
  intro a
  exact Finset.sum_nonneg fun P hP => historyRowDiagonal_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _

theorem energy_split (hj:j<k) (hprod : ∀x,(∏i,h x i)≠0) :
    energy k j B V extra mask X Δ W μ ν h y S path R phase =
      diagonal k j B V extra mask X Δ W μ ν h y S path R phase+
        (offDiagonal k j B V extra mask X Δ W μ ν h y S path R phase).re := by
  have hp (a:γ) (P:ℕ+) :
      (∑u,‖grouped k j B V extra mask X Δ W μ h (y a) S path P (phase a P) u‖^2)=
      (historyRowDiagonal k j μ h (y a) S path mask X Δ W P
        (fun x z => guardPhase k j B V extra P (h x) (y a) z.val (phase a P x z))).re+
      (historyRowOffDiagonal k j μ h (y a) S path mask X Δ W P
        (fun x z => guardPhase k j B V extra P (h x) (y a) z.val (phase a P x z))).re := by
    have hh := historyGroupedRow_split k j μ h (y a) S path mask X Δ W P
      (fun x z => guardPhase k j B V extra P (h x) (y a) z.val (phase a P x z)) hprod
      (by
        intro x z hz
        apply term_source_unit k j B V extra mask X Δ W hj P (h x) (y a) z.val (phase a P x z)
        simpa only [term_eq] using hz)
    simpa only [grouped_eq,Complex.add_re,Complex.ofReal_re] using congrArg Complex.re hh
  simp only [energy,diagonal,offDiagonal,FinitePrior.mean,FinitePrior.cmean,
    Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hp,
    Finset.sum_add_distrib,mul_add]

theorem energy_le_diagonal_add_norm (hj:j<k) (hprod : ∀x,(∏i,h x i)≠0) :
    energy k j B V extra mask X Δ W μ ν h y S path R phase ≤
      diagonal k j B V extra mask X Δ W μ ν h y S path R phase+
        ‖offDiagonal k j B V extra mask X Δ W μ ν h y S path R phase‖ := by
  rw [energy_split k j B V extra mask X Δ W μ ν h y S path R phase hj hprod]
  exact add_le_add le_rfl (Complex.re_le_norm _)

end
end Ostmann.Characters.Template.RetainedRow

end

end OAI
