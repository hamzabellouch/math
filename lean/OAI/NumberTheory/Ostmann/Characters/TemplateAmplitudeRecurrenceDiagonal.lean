import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceRows
import OAI.NumberTheory.Ostmann.Construction.RowDiagonal

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

def historyExactTag (k j : ℕ) (h : CopiedState k j) (v : ℤ) : ℚ :=
  (v:ℚ)/((∏i,h i:ℤ):ℚ)

theorem historyExactTag_eq_iff (k j : ℕ) (hL hR : CopiedState k j) (v w : ℤ)
    (hL0 : (∏i,hL i)≠0) (hR0 : (∏i,hR i)≠0) :
    historyExactTag k j hL v=historyExactTag k j hR w ↔
      v*(∏i,hR i)-w*(∏i,hL i)=0 := by
  unfold historyExactTag
  rw [div_eq_div_iff (by exact_mod_cast hL0) (by exact_mod_cast hR0)]
  rw [sub_eq_zero]
  exact_mod_cast Iff.rfl

section
variable {α : Type*} [Fintype α] (k j : ℕ)
    (μ : FinitePrior α) (h : α → CopiedState k j) (y : OutsideState k j)
    (S : List Bool → Finset ℤ) (path : List Bool)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ) (P : ℕ+)
    (phase : α → SupportedHistory S j path → ℂ)

def historyRowDiagonal : ℂ :=
  refinedRowDiagonal (fun a:α×SupportedHistory S j path => μ.mass a.1)
    (fun a => historyExactTag k j (h a.1) a.2.val.1)
    (fun a => historyRowTerm k j mask X Δ W P (h a.1) y a.2.val (phase a.1 a.2))

def historyRowOffDiagonal : ℂ :=
  refinedRowOffDiagonal (fun a:α×SupportedHistory S j path => μ.mass a.1)
    (fun a => historyRowTag k j P (h a.1) a.2.val.1)
    (fun a => historyExactTag k j (h a.1) a.2.val.1)
    (fun a => historyRowTerm k j mask X Δ W P (h a.1) y a.2.val (phase a.1 a.2))

theorem historyRowDiagonal_nonneg :
    0≤(historyRowDiagonal k j μ h y S path mask X Δ W P phase).re :=
  refinedRowDiagonal_nonneg _ _ _

theorem historyRowDiagonal_real :
    (historyRowDiagonal k j μ h y S path mask X Δ W P phase).im=0 :=
  refinedRowDiagonal_real _ _ _

theorem historyGroupedRow_split
    (hprod : ∀x,(∏i,h x i)≠0)
    (hunit : ∀x z,historyRowTerm k j mask X Δ W P (h x) y z.val (phase x z)≠0 →
      IsUnit ((∏i,h x i:ℤ):ZMod (P:ℕ))) :
    ((∑u,‖historyGroupedRow k j μ h y S path mask X Δ W P phase u‖^2:ℝ):ℂ) =
      historyRowDiagonal k j μ h y S path mask X Δ W P phase+
        historyRowOffDiagonal k j μ h y S path mask X Δ W P phase := by
  apply refinedRow_split
  intro x x' hx hx' he
  apply (historyRowTag_eq_iff k j P (h x'.1) (h x.1) x'.2.val.1 x.2.val.1
    (hunit _ _ hx') (hunit _ _ hx)).mpr
  have hz := (historyExactTag_eq_iff k j (h x'.1) (h x.1) x'.2.val.1 x.2.val.1
    (hprod _) (hprod _)).mp he
  rw [hz]
  exact dvd_zero _

end
end Ostmann.Characters.Template

end

end OAI
