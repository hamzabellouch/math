import OAI.NumberTheory.Ostmann.Characters.MixedIndicator
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateInitialUnary

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem norm_historyUnary (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (κ : (schedule k 0).Constituent width → ℂ)
    (hκ : ∀ i, ‖κ i‖=1) (j : ℕ) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : HistoryFrequencyUnits p j s t) (i : (schedule k j).Constituent width) :
    ‖historyUnary k width χ κ j s t i‖=1 := by
  induction j generalizing s with
  | zero =>
    simp only [historyUnary,norm_mul,norm_zpow,hκ,norm_character_of_ne_zero χ ht,
      one_zpow,one_mul]
  | succ j ih =>
    rcases i with ⟨i,a⟩
    cases i with
    | inl ib =>
      rcases ib with ⟨i,b⟩
      have hchild := ht.child b
      have hfreq : (signedChildFrequency t.1.1 t.1.2 b:ZMod p)≠0 := by
        cases b
        · simpa [signedChildFrequency] using ht.2.2.root
        · exact ht.2.1.root
      rw [historyUnary,norm_mul,norm_zpow,ih _ _ hchild _,one_zpow,one_mul,
        norm_zpow,norm_character_of_ne_zero χ (div_ne_zero hfreq ht.1),one_zpow]
    | inr i =>
      rw [historyUnary,norm_div,ih _ _ ht.2.1 _,ih _ _ ht.2.2 _,div_self one_ne_zero]

theorem norm_historyRegularKappa (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (κ : (schedule k 0).Constituent width → ℂ)
    (hκ : ∀ i, ‖κ i‖=1) (j : ℕ) (i : (schedule k j).Constituent width) :
    ‖historyRegularKappa k width χ κ j i‖=1 := by
  induction j with
  | zero => exact hκ i
  | succ j ih =>
    rcases i with ⟨i,a⟩
    cases i with
    | inl ib =>
      rcases ib with ⟨i,b⟩
      have hsign : (copySign b:ZMod p)≠0 := by cases b <;> simp [copySign]
      rw [historyRegularKappa,norm_mul,norm_zpow,ih,one_zpow,one_mul,
        norm_zpow,norm_character_of_ne_zero χ hsign,one_zpow]
    | inr i => simp only [historyRegularKappa,norm_one]

def actualHistoryUnary (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (j : ℕ) (s : ℤ) (t : HistoryReconstruction.Tree j) :
    (schedule k j).Constituent width → ℂ :=
  historyUnary k width χ (fun _ => initialKappa χ) j s t

theorem norm_actualHistoryUnary (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ≠1) (j : ℕ) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : HistoryFrequencyUnits p j s t) (i : (schedule k j).Constituent width) :
    ‖actualHistoryUnary k width χ j s t i‖=1 :=
  norm_historyUnary k width χ _ (fun _ => norm_initialKappa χ hχ) j s t ht i

theorem norm_supportedHistoryUnary (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ≠1) (S : List Bool → Finset ℤ)
    (hS : ∀ path f, f∈S path → (f:ZMod p)≠0) (j : ℕ) (path : List Bool)
    (h : HistoryFrequencyLabels.SupportedHistory S j path) (i : (schedule k j).Constituent width) :
    ‖supportedHistoryUnary k width χ (fun _ => initialKappa χ) S j path h i‖=1 :=
  norm_actualHistoryUnary k width χ hχ j h.val.1 h.val.2
    (historyFrequencyUnits_of_range S hS h.property) i

end Ostmann.Characters.Template

end

end OAI
