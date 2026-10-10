import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryNorm

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

def actualHistoryUnaryUnit (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ≠1) (j : ℕ) (s : ℤ)
    (t : HistoryReconstruction.Tree j) (ht : HistoryFrequencyUnits p j s t)
    (i : (schedule k j).Constituent width) : ℂˣ :=
  Units.mk0 (actualHistoryUnary k width χ j s t i) (by
    have hn := norm_actualHistoryUnary k width χ hχ j s t ht i
    intro he
    simp [he] at hn)

@[simp] theorem actualHistoryUnaryUnit_coe (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ≠1) (j : ℕ) (s : ℤ)
    (t : HistoryReconstruction.Tree j) (ht : HistoryFrequencyUnits p j s t)
    (i : (schedule k j).Constituent width) :
    (actualHistoryUnaryUnit k width χ hχ j s t ht i:ℂ)=actualHistoryUnary k width χ j s t i := rfl

abbrev UnaryOutputIndex (k j : ℕ) (width : Role → ℕ) :=
  OutputPrimeIndex (CopiedConstituent (schedule k j) j width)
    (OutsideConstituent (schedule k j) j width)

def historyCopiedUnaryUnits (k j : ℕ) (width : Role → ℕ)
    (p : UnaryOutputIndex k j width → ℕ) [∀ i, Fact (p i).Prime]
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) (hχ : ∀ i, χ i≠1)
    (s : ℤ) (t : HistoryReconstruction.Tree (j+1))
    (ht : ∀ i, HistoryFrequencyUnits (p i) (j+1) s t) :
    CopiedConstituent (schedule k j) j width × Bool → ℂˣ := fun ib =>
  actualHistoryUnaryUnit k width (χ (.inl ib)) (hχ _) j
    (unaryChildFrequency t ib.2) (unaryChildTree t ib.2) ((ht _).child ib.2)
    (copiedConstituentOld (schedule k j) j width ib.1)

def historyOutsideUnaryUnits (k j : ℕ) (width : Role → ℕ)
    (p : UnaryOutputIndex k j width → ℕ) [∀ i, Fact (p i).Prime]
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) (hχ : ∀ i, χ i≠1)
    (s : ℤ) (t : HistoryReconstruction.Tree (j+1))
    (ht : ∀ i, HistoryFrequencyUnits (p i) (j+1) s t) :
    OutsideConstituent (schedule k j) j width → Bool → ℂˣ := fun i b =>
  actualHistoryUnaryUnit k width (χ (.inr i)) (hχ _) j
    (unaryChildFrequency t b) (unaryChildTree t b) ((ht _).child b)
    (outsideConstituentOld (schedule k j) j width i)

theorem transferredUnary_eq_actualHistoryUnary (k j : ℕ) (hj : j<k) (width : Role → ℕ)
    (p : UnaryOutputIndex k j width → ℕ) [∀ i, Fact (p i).Prime]
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) (hχ : ∀ i, χ i≠1)
    (s : ℤ) (t : HistoryReconstruction.Tree (j+1))
    (ht : ∀ i, HistoryFrequencyUnits (p i) (j+1) s t) (i : UnaryOutputIndex k j width) :
    transferredUnary p χ
      (collapsedConstituentGraph (schedule k j) j width (pivotSlot k j hj) (graph k j) (intraGraph k j))
      (historyCopiedUnaryUnits k j width p χ hχ s t ht)
      (historyOutsideUnaryUnits k j width p χ hχ s t ht) s t.1.1 t.1.2 i =
    actualHistoryUnary k width (χ i) (j+1) s t
      ((nextConstituentEquiv (schedule k j) j width).symm i) := by
  rcases i with ⟨⟨i,a⟩,b⟩ | ⟨i,a⟩
  · change _ = actualHistoryUnary k width (χ (.inl (⟨i,a⟩,b))) (j+1) s t ⟨.inl (i,b),a⟩
    simp only [transferredUnary,historyCopiedUnaryUnits,actualHistoryUnaryUnit_coe,
      actualHistoryUnary,historyUnary,copiedConstituentOld,
      collapsedConstituentGraph,unaryPivotColumn,dite_eq_left hj]
  · rfl

end Ostmann.Characters.Template

end

end OAI
