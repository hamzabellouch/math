import OAI.NumberTheory.TwoPoint.Halasz.HalaszTrianglePoisson

namespace OAI

/-! Counting the nonzero integer Fourier modes near a stationary point. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszNearModes (R : ℝ) : Finset ℤ :=
  (Icc (-⌊R⌋) ⌊R⌋).erase 0

lemma halasz_mem_near_modes (R : ℝ) (k : ℤ) :
    k ∈ halaszNearModes R ↔ k ≠ 0 ∧ |(k:ℝ)| ≤ R := by
  unfold halaszNearModes
  simp only [mem_erase, mem_Icc]
  constructor
  · rintro ⟨hk,hlo,hhi⟩
    refine ⟨hk,abs_le.mpr ⟨?_,Int.le_floor.mp hhi⟩⟩
    have hh : -k ≤ ⌊R⌋ := by omega
    have hr := Int.le_floor.mp hh
    push_cast at hr
    linarith
  · rintro ⟨hk,hr⟩
    have hh := abs_le.mp hr
    refine ⟨hk,?_,Int.le_floor.mpr hh.2⟩
    have hneg : ((-k:ℤ):ℝ) ≤ R := by push_cast; linarith [hh.1]
    have hi := Int.le_floor.mpr hneg
    omega

lemma halasz_near_modes_card (R : ℝ) (hR : 0 ≤ R) :
    ((halaszNearModes R).card:ℝ) ≤ 2*R := by
  have hm : (0:ℤ) ≤ ⌊R⌋ := Int.floor_nonneg.mpr hR
  have hz : (0:ℤ) ∈ Icc (-⌊R⌋) ⌊R⌋ := mem_Icc.mpr ⟨by omega,hm⟩
  have he := card_erase_add_one hz
  have hc := Int.card_Icc_of_le (a := -⌊R⌋) (b := ⌊R⌋) (by omega)
  have heR : ((halaszNearModes R).card:ℝ)+1 = ((Icc (-⌊R⌋) ⌊R⌋).card:ℝ) := by
    exact_mod_cast he
  have hcR : ((Icc (-⌊R⌋) ⌊R⌋).card:ℝ) = 2*(⌊R⌋:ℝ)+1 := by
    have hc' : ((Icc (-⌊R⌋) ⌊R⌋).card:ℤ) = 2*⌊R⌋+1 := by omega
    exact_mod_cast hc'
  have hf := Int.floor_le R
  linarith

end TwoPointCorrelations

end OAI
