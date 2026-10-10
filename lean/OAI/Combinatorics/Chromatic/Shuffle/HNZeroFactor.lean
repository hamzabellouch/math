import Mathlib
import OAI.Combinatorics.Chromatic.Walls.HNTorusFactor
import OAI.Combinatorics.Chromatic.Shuffle.HNZeroRows
import OAI.Combinatorics.Chromatic.QuantumTorus.TorusProjection

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits
open PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

def zeroBlockCoefficient (θ : ℝ) (d : I → ℕ) : LaurentSeries ℚ := by
  classical
  exact if hd : d=0 then 1 else if slopeValue c η θ d=0 then
    series (blockRowsEnergy a κ c η hc d) (blockRowsEnergy_admissible a κ c η hc d hd) else 0

lemma zeroBlockCoefficient_eq (θ : ℝ) (d : I → ℕ) :
    zeroBlockCoefficient a κ c η hc θ d=
      if slopeValue c η θ d=0 then lowSeries a κ c η hc θ d else 0 := by
  classical
  unfold zeroBlockCoefficient
  by_cases hd : d=0
  · subst d
    simp only [dite_eq_left trivial,slopeValue_zero,ite_true,lowSeries_zero]
  · rw [dite_eq_right hd]
    by_cases hz : slopeValue c η θ d=0
    · rw [ite_eq_left hz,ite_eq_left hz]
      exact (lowSeries_on_slope a κ c η hc θ d hd
        ((slopeValue_eq_zero_iff c η hc θ d hd).mp hz)).symm
    · rw [ite_eq_right hz,ite_eq_right hz]

variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
variable (hΩ : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
variable (h : M →+ ℝ) (θ : ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)

include hh in
lemma zeroBlockCoeff_project (n : ℕ) :
    coeff n (push w LaurentRay.vUnit Ω P (zeroBlockCoefficient a κ c η hc θ))=
      zeroProject LaurentRay.vUnit Ω h (coeff n (push w LaurentRay.vUnit Ω P (lowSeries a κ c η hc θ))) := by
  classical
  simp only [push,coeff_mk,pushCoeff,map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [zeroProject_monomial,zeroBlockCoefficient_eq,hh]
  split_ifs <;> simp only [Torus.monomial_zero]

include hΩ hh in

theorem hnTorus_zeroFactor :
    push w LaurentRay.vUnit Ω P (zeroBlockCoefficient a κ c η hc θ)=
      PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h) (push w LaurentRay.vUnit Ω P (hnSeries a κ c η hc)) := by
  apply PowerSeries.ext
  intro n
  rw [zeroFactor_coeff_projection,←(hnTorus_canonical_factors a κ c η hc w Ω P hΩ h θ hh).2]
  exact zeroBlockCoeff_project a κ c η hc w Ω P h θ hh n

include hΩ hh in
theorem literalInput_zeroFactor (ε : I → Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) :
    push w LaurentRay.vUnit Ω P (zeroBlockCoefficient a κ c η hc θ)=
      PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h) (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε)) := by
  have he : literalInputCoefficient a κ ε=hnSeries a κ c η hc :=
    funext (literalInput_hnSeries a κ c η hc ε ha)
  rw [he]
  exact hnTorus_zeroFactor a κ c η hc w Ω P hΩ h θ hh

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [hχ : Fact (∀θ,SlopeEulerSymmetric a c η θ)]
local instance (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩

lemma primitiveCountsSeries_vanish (θ : ℝ) (d : I → ℕ) (hd : ¬OnSlopeOrZero c η θ d) :
    primitiveCountsSeries a κ c η hc θ d=0 := by
  let : IsEmpty (PrimitiveCounts a c η hc θ d) :=
    ⟨fun x=>hd (primitiveCounts_onSlope a c η hc θ d x)⟩
  ext j
  rw [primitiveCountsSeries,series_coeff]
  simp

lemma primitiveCountsSeries_support (θ : ℝ) (d : I → ℕ)
    (hd : primitiveCountsSeries a κ c η hc θ d≠0) : OnSlopeOrZero c η θ d := by
  by_contra H
  exact hd (primitiveCountsSeries_vanish a κ c η hc θ d H)

lemma primitiveCountsSeries_eq_zeroBlock (θ : ℝ) (d : I → ℕ) :
    primitiveCountsSeries a κ c η hc θ d=zeroBlockCoefficient a κ c η hc θ d := by
  by_cases hd : d=0
  · subst d
    rw [primitiveCountsSeries_zero]
    simp only [zeroBlockCoefficient,dite_eq_left trivial]
  · rw [zeroBlockCoefficient,dite_eq_right hd]
    by_cases hz : slopeValue c η θ d=0
    · rw [ite_eq_left hz]
      have hs := (slopeValue_eq_zero_iff c η hc θ d hd).mp hz
      subst θ
      exact series_equiv _ _ (primitiveCountsRows a c η hc d)
        (primitiveCountsRows_energy a κ c η hc d)
    · rw [ite_eq_right hz]
      apply primitiveCountsSeries_vanish
      intro H
      apply hz
      exact (slopeValue_eq_zero_iff c η hc θ d hd).mpr (H.resolve_left hd)

open QuantumTorus WeightedTorusSeries WallUnits
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
variable (hΩ : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
variable (h : M →+ ℝ) (θ : ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)

include hΩ hh in

theorem literalInput_primitiveFactor (ε : I → Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) :
    push w LaurentRay.vUnit Ω P (primitiveCountsSeries a κ c η hc θ)=
      PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h)
        (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε)) := by
  rw [funext (primitiveCountsSeries_eq_zeroBlock a κ c η hc θ)]
  exact literalInput_zeroFactor a κ c η hc w Ω P hΩ h θ hh ε ha

end
end ElementaryPositivity.RawShuffle

end

end OAI
