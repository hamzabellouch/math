import OAI.NumberTheory.PiExponent.Jets.BranchContact
import OAI.NumberTheory.PiExponent.Jets.DVRBranch
import OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation

namespace OAI

noncomputable section
namespace PiExponent.DVRBranchJet
open PiExponentApprox FormalBranchEvaluation

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

def coordinates {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A) :
    Fin (m+1) → PowerSeries ℂ :=
  branchCoordinates c (DVRBranch.expansion ℂ A y)
    (fun i => DVRBranch.expansion ℂ A (x i))

theorem coordinates_centered {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i) :
    ∀ i, PowerSeries.constantCoeff (coordinates c y x i) = 0 := by
  intro i
  have ht : MvPowerSeries.constantCoeff (DVRBranch.expansion ℂ A y - 1) = 0 := by
    change PowerSeries.constantCoeff (DVRBranch.expansion ℂ A y - 1) = 0
    simp [hy]
  cases i using Fin.cases with
  | zero => exact ht
  | succ i =>
    change PowerSeries.constantCoeff
      (DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i) -
        PowerSeries.subst (DVRBranch.expansion ℂ A y - 1) (PowerSeries.log ℂ)) = 0
    change MvPowerSeries.constantCoeff
      (DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i) -
        PowerSeries.subst (DVRBranch.expansion ℂ A y - 1) (PowerSeries.log ℂ)) = 0
    rw [map_sub, PowerSeries.constantCoeff_subst_eq_zero ht _ PowerSeries.constantCoeff_log,
      sub_zero, map_sub]
    change PowerSeries.constantCoeff (DVRBranch.expansion ℂ A (x i)) -
      PowerSeries.constantCoeff (PowerSeries.C (c i)) = 0
    rw [DVRBranch.expansion_constantCoeff, hx i, PowerSeries.constantCoeff_C, sub_self]

theorem coordinates_nonzero {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    ∃ i, coordinates c y x i ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hy : y = 1 := by
    apply DVRBranch.expansion_injective ℂ A
    have h0 := hn 0
    change DVRBranch.expansion ℂ A y - 1 = 0 at h0
    simpa only [map_one] using sub_eq_zero.mp h0
  rcases hnc with hnc | ⟨i, hi⟩
  · exact hnc hy
  · apply hi
    apply DVRBranch.expansion_injective ℂ A
    have hs := hn i.succ
    change DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i) -
      PowerSeries.subst (DVRBranch.expansion ℂ A y - 1) (PowerSeries.log ℂ) = 0 at hs
    rw [hy, map_one, sub_self,
      PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log, sub_zero] at hs
    rw [AlgHom.commutes]
    change DVRBranch.expansion ℂ A (x i) = PowerSeries.C (c i)
    exact sub_eq_zero.mp hs

def contact {m : ℕ} (v : Fin (m+1) → ℚ) (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i)) : ℚ :=
  BranchContact.contact v (coordinates c y x) (coordinates_nonzero c y x hnc)

theorem contact_pos {m : ℕ} (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    0 < contact v c y x hnc :=
  BranchContact.contact_pos v hv _ _ (coordinates_centered c y x hy hx)

theorem frameWord_addVal_lower {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : FramePolynomial m)
    (hp : FormalLogJet.formalJet c p ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p) ≠ 0) :
    contact v c y x hnc * (H - (word.map v).sum) ≤
      ((IsDiscreteValuationRing.addVal A
        (MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p))).toNat : ℚ) := by
  have heval (q : FramePolynomial m) :
      DVRBranch.expansion ℂ A (MvPolynomial.aeval (Fin.cases y x) q) =
      MvPolynomial.aeval (Fin.cases (DVRBranch.expansion ℂ A y)
        (fun i => DVRBranch.expansion ℂ A (x i))) q := by
    rw [expansion_aeval]
    apply congrArg (fun z => MvPolynomial.aeval z q)
    funext i
    cases i using Fin.cases <;> rfl
  have hne' : MvPolynomial.aeval (Fin.cases (DVRBranch.expansion ℂ A y)
      (fun i => DVRBranch.expansion ℂ A (x i))) (polynomialFrameWord m word p) ≠ 0 := by
    rw [← heval]
    exact (map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hne
  have hb := polynomialFrameWord_branch_order_toNat c (DVRBranch.expansion ℂ A y)
    (fun i => DVRBranch.expansion ℂ A (x i))
    (by simpa using hy) (fun i => by simpa using hx i)
    v (fun i => (hv i).le) (contact v c y x hnc) H
    (contact_pos v hv c y x hy hx hnc).le p hp
    (BranchContact.contact_bound v hv _ _) word hne'
  rw [← heval, DVRBranch.expansion_order] at hb
  exact hb

theorem frameWord_colength_lower {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : FramePolynomial m)
    (hp : FormalLogJet.formalJet c p ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p) ≠ 0) :
    contact v c y x hnc * (H - (word.map v).sum) ≤
      ((Module.length A (A ⧸ Ideal.span {
        MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p)})).toNat : ℚ) := by
  rw [CurveLocalOrder.length_quotient_span_eq_addVal hne]
  exact frameWord_addVal_lower v hv H c y x hy hx hnc p hp word hne

end PiExponent.DVRBranchJet

end

end OAI
