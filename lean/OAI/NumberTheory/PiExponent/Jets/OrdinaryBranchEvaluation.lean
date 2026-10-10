import OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational
import OAI.NumberTheory.PiExponent.Jets.OrdinaryJetDerivatives

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryAuxiliaryJet

open MvPowerSeries

def branchCoordinates {n : ℕ} (c : Fin n → ℂ) (x : Fin n → PowerSeries ℂ) :
    Fin n → PowerSeries ℂ := fun i => x i - PowerSeries.C (c i)

theorem branchCoordinates_hasSubst {n : ℕ} (c : Fin n → ℂ)
    (x : Fin n → PowerSeries ℂ) (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i) :
    HasSubst (branchCoordinates c x) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  change PowerSeries.constantCoeff (x i - PowerSeries.C (c i)) = 0
  rw [map_sub, hx i, PowerSeries.constantCoeff_C, sub_self]

theorem formalJet_subst_branch {n : ℕ} (c : Fin n → ℂ)
    (x : Fin n → PowerSeries ℂ) (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (p : MvPolynomial (Fin n) ℂ) :
    subst (branchCoordinates c x) (formalJet c p) = MvPolynomial.aeval x p := by
  let ha := branchCoordinates_hasSubst c x hx
  have heq : (substAlgHom ha).comp (formalJet c) = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, formalJet, MvPolynomial.aeval_X, map_add]
    rw [substAlgHom_X, substAlgHom_apply, subst_C]
    change PowerSeries.C (c i) + (x i - PowerSeries.C (c i)) = x i
    ring
  simpa only [AlgHom.comp_apply, substAlgHom_apply] using AlgHom.congr_fun heq p

theorem ordinaryWord_branch_order {n : ℕ}
    (c : Fin n → ℂ) (x : Fin n → PowerSeries ℂ)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (v : Fin n → ℚ) (hv : ∀ i, 0 ≤ v i) (mu H : ℚ) (hmu : 0 ≤ mu)
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (branchCoordinates c x i).order = (k : ℕ∞) →
      mu * v i ≤ (k : ℚ)) (word : List (Fin n)) :
    (⌈mu * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤
      PowerSeries.order (MvPolynomial.aeval x (OrdinaryDerivatives.word n word p)) := by
  have h := FormalBranchOrder.rational_powerSeries_order_subst_of_mem_weightedIdeal
    v hv mu (H - (word.map v).sum) hmu
    (formalJet c (OrdinaryDerivatives.word n word p)) (branchCoordinates c x)
    (branchCoordinates_hasSubst c x hx)
    (formalJet_word_vanishing c v hv H p hp word) hcontact
  rwa [formalJet_subst_branch c x hx] at h

theorem ordinaryWord_branch_order_toNat {n : ℕ}
    (c : Fin n → ℂ) (x : Fin n → PowerSeries ℂ)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (v : Fin n → ℚ) (hv : ∀ i, 0 ≤ v i) (mu H : ℚ) (hmu : 0 ≤ mu)
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (branchCoordinates c x i).order = (k : ℕ∞) →
      mu * v i ≤ (k : ℚ)) (word : List (Fin n))
    (hne : MvPolynomial.aeval x (OrdinaryDerivatives.word n word p) ≠ 0) :
    mu * (H - (word.map v).sum) ≤
      ((PowerSeries.order (MvPolynomial.aeval x
        (OrdinaryDerivatives.word n word p))).toNat : ℚ) := by
  have h := ordinaryWord_branch_order c x hx v hv mu H hmu p hp hcontact word
  have hn := PowerSeries.order_eq_top.not.mpr hne
  have hh := ENat.toNat_le_toNat h hn
  exact Nat.ceil_le.mp (by simpa using hh)

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
