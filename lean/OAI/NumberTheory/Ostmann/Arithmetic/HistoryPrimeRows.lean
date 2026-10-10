import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFieldIndependence
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPatternRows
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryResidueRegular
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeLineFamiliesProbability

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrimeRows
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryOccurrenceRows HistoryPatternRows HistoryRepeatedRenaming ClearedCoefficientFlags
open MvPolynomial

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def AncestorUnits {K : Type*} [Zero K] (h : History l) (i : InternalKey h)
    (x : PatternKey h → K) : Prop :=
  ∀ j : Fin h.root.small.length ⊕ InternalKey h,
    internalLevel h i < keyLevel h (Sum.inr j) → x (patternMap h (Sum.inr j)) ≠ 0

theorem row_regular_nonzero_field {K : Type*} [Field K]
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) (x : PatternKey h → K)
    (hx : AncestorUnits h i x) (hf : ∀ s ∈ h.frequencies, (s:K) ≠ 0) :
    (row h hs i).1.FieldRegularAt x ∧ (row h hs i).2.FieldRegularAt x ∧
      ((row h hs i).1.fieldEval x ≠ 0 ∨ (row h hs i).2.fieldEval x ≠ 0) := by
  have hr := HistoryFieldIndependence.canonical_regular h hs i (x ∘ patternMap h) hx hf
  have hn := HistoryFieldIndependence.canonical_nonzero h hs i (x ∘ patternMap h) hx hf
  simpa only [row,Expr.fieldRegularAt_rename,Expr.fieldEval_rename] using
    And.intro hr.1 (And.intro hr.2 hn)

theorem flags_nonzero_field {K : Type*} [Field K]
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) (x : PatternKey h → K)
    (hx : AncestorUnits h i x) (hf : ∀ s ∈ h.frequencies, (s:K) ≠ 0) :
    eval₂ (Int.castRingHom K) x (leftFlag h hs i) ≠ 0 ∨
      eval₂ (Int.castRingHom K) x (rightFlag h hs i) ≠ 0 := by
  obtain ⟨ha,hb,hn⟩ := row_regular_nonzero_field h hs i x hx hf
  exact (row_nonzero_iff _ _ x ha hb).mpr hn

theorem frequency_units (h : History l) (hs : h.Supported V outside)
    (p : ℕ) (hV : ∀ j ≤ l, V j < p) : ∀ s ∈ h.frequencies, (s:ZMod p) ≠ 0 := by
  intro s hmem
  obtain ⟨hs0,j,hjl,hj⟩ := History.supported_frequency_bounds hs s hmem
  exact HistoryResidueRegular.intCast_ne_zero_of_natAbs_lt hs0 (hj.trans_lt (hV j hjl))

theorem family_probability_le (h : History l) (hs : h.Supported V outside)
    (p : ℕ) [Fact p.Prime] (x : PatternKey h → ZMod p)
    {J : Type*} (occurrence : J → InternalKey h) (j₀ : J)
    (hx : AncestorUnits h (occurrence j₀) x) (hV : ∀ j ≤ l, V j < p) :
    PrimeLineFamilies.probability p
      (fun j => eval₂ (Int.castRingHom (ZMod p)) x (leftFlag h hs (occurrence j)))
      (fun j => eval₂ (Int.castRingHom (ZMod p)) x (rightFlag h hs (occurrence j))) ≤
        ((p-1:ℕ):ℝ)⁻¹ := by
  apply PrimeLineFamilies.probability_le_unit_line
  intro hz
  have hn := flags_nonzero_field h hs (occurrence j₀) x hx (frequency_units h hs p hV)
  exact hn.elim (fun hn => hn (hz j₀).1) (fun hn => hn (hz j₀).2)

def RepeatedFiber (h : History l) (i : InternalKey h) :=
  {j : InternalKey h // (internalSlot h j).value = (internalSlot h i).value ∧
    internalLevel h j = internalLevel h i}

theorem repeated_probability_le (h : History l) (hs : h.Supported V outside)
    (i : InternalKey h) [Fact (internalSlot h i).value.Prime]
    (x : PatternKey h → ZMod (internalSlot h i).value)
    (hx : AncestorUnits h i x) (hV : ∀ j ≤ l, V j < (internalSlot h i).value) :
    PrimeLineFamilies.probability (internalSlot h i).value
      (fun j : RepeatedFiber h i => eval₂ (Int.castRingHom _) x (leftFlag h hs j.val))
      (fun j : RepeatedFiber h i => eval₂ (Int.castRingHom _) x (rightFlag h hs j.val)) ≤
        (((internalSlot h i).value-1:ℕ):ℝ)⁻¹ :=
  family_probability_le h hs _ x Subtype.val ⟨i,rfl,rfl⟩ hx hV

theorem line_zero_iff (h : History l) (hs : h.Supported V outside)
    (p : ℕ) [Fact p.Prime] (i : InternalKey h) (x : PatternKey h → ZMod p)
    (hx : AncestorUnits h i x) (hV : ∀ j ≤ l, V j < p) (X Y : ZMod p) :
    eval₂ (Int.castRingHom (ZMod p)) x (leftFlag h hs i)*X+
      eval₂ (Int.castRingHom (ZMod p)) x (rightFlag h hs i)*Y=0 ↔
        (row h hs i).1.fieldEval x*X+(row h hs i).2.fieldEval x*Y=0 := by
  obtain ⟨ha,hb,_⟩ := row_regular_nonzero_field h hs i x hx (frequency_units h hs p hV)
  exact linear_zero_iff _ _ x ha hb X Y

end Ostmann.Arithmetic.HistoryPrimeRows

end

end OAI
