import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabelsBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceStates
import OAI.NumberTheory.Ostmann.Construction.CountedRows
import OAI.NumberTheory.Ostmann.Construction.RowCongruence

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

def historyRowTag (k j : ℕ) (P : ℕ+) (h : CopiedState k j) (v : ℤ) : ZMod (P:ℕ) :=
  (v : ZMod (P:ℕ)) * ((∏i,h i : ℤ) : ZMod (P:ℕ))⁻¹

theorem historyRowTag_eq_iff (k j : ℕ) (P : ℕ+) (hL hR : CopiedState k j)
    (v w : ℤ) (hLunit : IsUnit ((∏i,hL i : ℤ) : ZMod (P:ℕ)))
    (hRunit : IsUnit ((∏i,hR i : ℤ) : ZMod (P:ℕ))) :
    historyRowTag k j P hL v = historyRowTag k j P hR w ↔
      (P:ℤ) ∣ v*(∏i,hR i)-w*(∏i,hL i) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub,Int.cast_mul,sub_eq_zero,historyRowTag]
  exact unit_fraction_eq_iff _ _ _ _ _ _
    (ZMod.mul_inv_of_unit _ hLunit) (ZMod.mul_inv_of_unit _ hRunit)

def historyRowTerm (k j : ℕ) (mask : (j:ℕ) → ℤ → State k j → Prop)
    (X Δ W : ℝ) (P : ℕ+) (h : CopiedState k j) (y : OutsideState k j)
    (z : ℤ × HistoryReconstruction.Tree j) (phase : ℂ) : ℂ :=
  weight k mask X Δ W j z.1 (sourceState k j (P:ℤ) h y) z.2 * phase

def historyGroupedRow {α : Type*} [Fintype α] (k j : ℕ)
    (μ : FinitePrior α) (h : α → CopiedState k j) (y : OutsideState k j)
    (S : List Bool → Finset ℤ) (path : List Bool)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ) (P : ℕ+)
    (phase : α → SupportedHistory S j path → ℂ) (u : ZMod (P:ℕ)) : ℂ :=
  countedGroupedRow μ (fun x z => historyRowTag k j P (h x) z.val.1)
    (fun x z => historyRowTerm k j mask X Δ W P (h x) y z.val (phase x z)) u

theorem historyGroupedRow_pairing {α : Type*} [Fintype α] (k j : ℕ)
    (μ : FinitePrior α) (h : α → CopiedState k j) (y : OutsideState k j)
    (S : List Bool → Finset ℤ) (path : List Bool)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ) (P : ℕ+)
    (phase : α → SupportedHistory S j path → ℂ) (G : ZMod (P:ℕ) → ℂ) :
    (∑u,G u*historyGroupedRow k j μ h y S path mask X Δ W P phase u) =
      μ.cmean (fun x => ∑z:SupportedHistory S j path,
        G (historyRowTag k j P (h x) z.val.1)*
          historyRowTerm k j mask X Δ W P (h x) y z.val (phase x z)) :=
  countedGroupedRow_pairing μ _ _ G

theorem historyGroupedRow_square {α : Type*} [Fintype α] (k j : ℕ)
    (μ : FinitePrior α) (h : α → CopiedState k j) (y : OutsideState k j)
    (S : List Bool → Finset ℤ) (path : List Bool)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ) (P : ℕ+)
    (phase : α → SupportedHistory S j path → ℂ) :
    ((∑u,‖historyGroupedRow k j μ h y S path mask X Δ W P phase u‖^2 : ℝ):ℂ) =
      μ.cmean (fun x => μ.cmean (fun x' =>
        ∑z:SupportedHistory S j path,∑z':SupportedHistory S j path,
          if historyRowTag k j P (h x') z'.val.1 = historyRowTag k j P (h x) z.val.1 then
            historyRowTerm k j mask X Δ W P (h x) y z.val (phase x z)*
              conj (historyRowTerm k j mask X Δ W P (h x') y z'.val (phase x' z'))
          else 0)) := countedGroupedRow_square μ _ _

end Ostmann.Characters.Template

end

end OAI
