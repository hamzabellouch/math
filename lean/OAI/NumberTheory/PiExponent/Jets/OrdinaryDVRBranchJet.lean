import OAI.NumberTheory.PiExponent.Jets.BranchContact
import OAI.NumberTheory.PiExponent.Jets.DVRBranch
import OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryDVRBranchJet
open OrdinaryAuxiliaryJet

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem expansion_aeval {n : ℕ} (x : Fin n → A) (p : MvPolynomial (Fin n) ℂ) :
    DVRBranch.expansion ℂ A (MvPolynomial.aeval x p) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) p := by
  have h : (DVRBranch.expansion ℂ A).comp (MvPolynomial.aeval x) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact AlgHom.congr_fun h p

def coordinates {n : ℕ} (c : Fin n → ℂ) (x : Fin n → A) :
    Fin n → PowerSeries ℂ :=
  branchCoordinates c (fun i => DVRBranch.expansion ℂ A (x i))

theorem coordinates_centered {n : ℕ} (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i) :
    ∀ i, PowerSeries.constantCoeff (coordinates c x i) = 0 := by
  intro i
  change PowerSeries.constantCoeff
    (DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i)) = 0
  rw [map_sub, DVRBranch.expansion_constantCoeff, hx i,
    PowerSeries.constantCoeff_C, sub_self]

theorem coordinates_nonzero {n : ℕ} (c : Fin n → ℂ) (x : Fin n → A)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    ∃ i, coordinates c x i ≠ 0 := by
  obtain ⟨i, hi⟩ := hnc
  refine ⟨i, ?_⟩
  intro hz
  apply hi
  apply DVRBranch.expansion_injective ℂ A
  rw [AlgHom.commutes]
  change DVRBranch.expansion ℂ A (x i) = PowerSeries.C (c i)
  exact sub_eq_zero.mp hz

def contact {n : ℕ} (v : Fin n → ℚ) (c : Fin n → ℂ) (x : Fin n → A)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) : ℚ :=
  BranchContact.contact v (coordinates c x) (coordinates_nonzero c x hnc)

theorem contact_pos {n : ℕ} (v : Fin n → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    0 < contact v c x hnc :=
  BranchContact.contact_pos v hv _ _ (coordinates_centered c x hx)

theorem ordinaryWord_addVal_lower {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n)) :
    (⌈contact v c x hnc * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤
      IsDiscreteValuationRing.addVal A
        (MvPolynomial.aeval x (OrdinaryDerivatives.word n word p)) := by
  have h := ordinaryWord_branch_order c (fun i => DVRBranch.expansion ℂ A (x i))
    (fun i => by simpa using hx i) v (fun i => (hv i).le)
    (contact v c x hnc) H (contact_pos v hv c x hx hnc).le p hp
    (BranchContact.contact_bound v hv _ _) word
  rwa [← expansion_aeval, DVRBranch.expansion_order] at h

theorem ordinaryWord_addVal_toNat_lower {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n))
    (hne : MvPolynomial.aeval x (OrdinaryDerivatives.word n word p) ≠ 0) :
    contact v c x hnc * (H - (word.map v).sum) ≤
      ((IsDiscreteValuationRing.addVal A
        (MvPolynomial.aeval x (OrdinaryDerivatives.word n word p))).toNat : ℚ) := by
  have h := ordinaryWord_addVal_lower v hv H c x hx hnc p hp word
  have hn := IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hne
  have hh := ENat.toNat_le_toNat h hn
  exact Nat.ceil_le.mp (by simpa using hh)

theorem ordinaryWord_colength_lower {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n))
    (hne : MvPolynomial.aeval x (OrdinaryDerivatives.word n word p) ≠ 0) :
    contact v c x hnc * (H - (word.map v).sum) ≤
      ((Module.length A (A ⧸ Ideal.span {
        MvPolynomial.aeval x (OrdinaryDerivatives.word n word p)})).toNat : ℚ) := by
  rw [CurveLocalOrder.length_quotient_span_eq_addVal hne]
  exact ordinaryWord_addVal_toNat_lower v hv H c x hx hnc p hp word hne

end PiExponent.OrdinaryDVRBranchJet
end

end OAI
