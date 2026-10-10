import OAI.NumberTheory.PiExponent.Jets.FormalLogJet
import OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet
import OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryAuxiliaryJet

theorem formalJet_pderiv {n : ℕ} (c : Fin n → ℂ) (i : Fin n)
    (p : MvPolynomial (Fin n) ℂ) :
    formalJet c (MvPolynomial.pderiv i p) = MvPowerSeries.pderiv i (formalJet c p) := by
  apply FormalLogJet.derivation_map_of_X (formalJet c) (MvPolynomial.pderiv i)
    (MvPowerSeries.pderiv i) _ p
  intro j
  by_cases hij : i = j
  · subst j
    simp [formalJet]
  · simp [formalJet, MvPowerSeries.pderiv_X_of_ne, Ne.symm hij]

theorem formalJet_word_vanishing {n : ℕ} (c : Fin n → ℂ)
    (v : Fin n → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin n)) :
    formalJet c (OrdinaryDerivatives.word n word p) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  induction word with
  | nil => simpa only [OrdinaryDerivatives.word_nil, List.map_nil, List.sum_nil, sub_zero] using hp
  | cons i word ih =>
    rw [OrdinaryDerivatives.word_cons, formalJet_pderiv]
    have h := FormalJetDerivatives.pderiv_mem_rationalWeightedIdeal v hv
      (H - (word.map v).sum) (formalJet c (OrdinaryDerivatives.word n word p)) ih i
    simpa only [List.map_cons, List.sum_cons, sub_sub, add_comm] using h

theorem formalJet_word_vanishing_of_cost {n : ℕ} (c : Fin n → ℂ)
    (v : Fin n → ℚ) (hv : ∀ i, 0 ≤ v i) (H delta : ℚ)
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin n)) (hword : (word.map v).sum ≤ delta) :
    formalJet c (OrdinaryDerivatives.word n word p) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - delta) := by
  intro d hd
  apply formalJet_word_vanishing c v hv H p hp word d
  exact lt_of_lt_of_le hd (by linarith)

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
