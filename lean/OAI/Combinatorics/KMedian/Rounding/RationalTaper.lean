import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalTaperCandidates

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

def rationalMarginal (P d r : ℚ) : ℚ := min 1 (max (1-r*d) 0/P)

def rationalMass (g P : ℚ) (d : I → ℚ) (r : ℚ) : ℚ :=
  ∑ i, g*rationalMarginal P (d i) r

theorem cast_rationalMarginal (P d r : ℚ) :
    (rationalMarginal P d r:ℝ)=marginal P d r := by
  simp only [rationalMarginal,marginal,Rat.cast_min,Rat.cast_max,
    Rat.cast_div,Rat.cast_sub,Rat.cast_mul,Rat.cast_one,Rat.cast_zero]

theorem cast_rationalMass (g P : ℚ) (d : I → ℚ) (r : ℚ) :
    (rationalMass g P d r:ℝ)=mass g P (fun i => (d i:ℝ)) r := by
  simp only [rationalMass,mass,Rat.cast_sum,Rat.cast_mul,cast_rationalMarginal]

def rootCandidates (g P : ℚ) (d : I → ℚ) : Finset ℚ :=
  (candidates g P d).filter (fun q => 0 < q ∧ rationalMass g P d q=1)

def inverseRadius (g P : ℚ) (d : I → ℚ) : ℚ :=
  if h : (rootCandidates g P d).Nonempty then (rootCandidates g P d).max' h else 0

theorem rootCandidates_card (g P : ℚ) (d : I → ℚ) :
    (rootCandidates g P d).card ≤ (2*Fintype.card I+2)+(2*Fintype.card I+2)^2 :=
  (card_filter_le _ _).trans (candidates_card g P d)

theorem inverseRadius_spec (g P : ℚ) (d : I → ℚ)
    (hg : 0 < (g:ℝ)) (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i, 0 ≤ d i) (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hcol : colocatedMass g (fun i => (d i:ℝ)) < 1) :
    0 < inverseRadius g P d ∧ rationalMass g P d (inverseRadius g P d)=1 ∧
      ∀ u : ℝ, 1 ≤ mass g P (fun i => (d i:ℝ)) u → u ≤ (inverseRadius g P d:ℝ) := by
  obtain ⟨r,hr,he,hmax⟩ := exists_minimal_radius (fun i => (d i:ℝ)) hg hP hP1
    (fun i => by exact_mod_cast hd i) htotal hcol
  obtain ⟨q,hq,hqr⟩ := maximal_root_in_candidates g P d hg hP hP1 hd hcol r hr he hmax
  have hqpos : 0 < q := by exact_mod_cast (hqr ▸ hr)
  have hqe : rationalMass g P d q=1 := by
    have hh : (rationalMass g P d q:ℝ)=1 := by rw [cast_rationalMass,hqr,he]
    exact_mod_cast hh
  have hmem : q ∈ rootCandidates g P d := mem_filter.mpr ⟨hq,hqpos,hqe⟩
  have hne : (rootCandidates g P d).Nonempty := ⟨q,hmem⟩
  have hm : inverseRadius g P d ∈ rootCandidates g P d := by
    unfold inverseRadius
    rw [dite_eq_left hne]
    exact max'_mem _ hne
  obtain ⟨_,hpos,hroot⟩ := mem_filter.mp hm
  refine ⟨hpos,hroot,?_⟩
  have hle : q ≤ inverseRadius g P d := by
    unfold inverseRadius
    rw [dite_eq_left hne]
    exact le_max' _ _ hmem
  have hleR : r ≤ (inverseRadius g P d:ℝ) := by rw [← hqr]; exact_mod_cast hle
  intro u hu
  exact (hmax u hu).trans hleR

theorem positive_data (g P : ℚ) (d : I → ℚ) (Δ : ℕ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i, 0 ≤ d i) (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hcol : colocatedMass g (fun i => (d i:ℝ)) < 1) :
    let r := inverseRadius g P d
    let q := fun i => rationalMarginal P (d i) r
    0 < 1/r ∧ (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) ∧
      (∑ i, g*q i=1) ∧ (∑ i, q i=Δ) ∧
      (∀ i, d i=0 → q i=1) ∧
      (∀ i, q i < 1 → (1/r)*(1-P*q i) ≤ d i) ∧
      (∀ i, 0 < q i → d i ≤ (1/r)*(1-P*q i)) ∧
      (∀ R : ℝ, 0 < R → 1 ≤ mass g P (fun i => (d i:ℝ)) (1/R) → (1/r:ℚ) ≤ R) := by
  dsimp only
  let r := inverseRadius g P d
  let q := fun i => rationalMarginal P (d i) r
  obtain ⟨hr,he,hmax⟩ := inverseRadius_spec g P d hg hP hP1 hd htotal hcol
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hq : ∀ i, (q i:ℝ)=marginal P (d i) r := fun i => cast_rationalMarginal P (d i) r
  have hsum : (∑ i, q i)=(Δ:ℚ) := by
    apply mul_left_cancel₀ (show g ≠ 0 by exact_mod_cast hg.ne')
    rw [mul_sum]
    change rationalMass g P d r=g*(Δ:ℚ)
    rw [he]
    exact_mod_cast hunit.symm
  refine ⟨one_div_pos.mpr hr,?_,?_,he,hsum,?_,?_,?_,?_⟩
  · intro i
    have hh := marginal_nonneg (d := (d i:ℝ)) (r := (r:ℝ)) hP
    rw [← hq] at hh
    exact_mod_cast hh
  · intro i
    have hh := marginal_le_one (P:ℝ) (d i:ℝ) (r:ℝ)
    rw [← hq] at hh
    exact_mod_cast hh
  · intro i hi
    have hh : (q i:ℝ)=1 := by
      rw [hq,hi,Rat.cast_zero]
      exact marginal_at_zero_distance hP (by linarith)
    exact_mod_cast hh
  · intro i hi
    have hiR : marginal P (d i) r < 1 := by rw [← hq]; exact_mod_cast hi
    have hh := lower_comparison hP hiR
    have hres : (1/(r:ℝ))*(1-(P:ℝ)*(q i:ℝ)) ≤ (d i:ℝ) := by
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ hrR).mpr
      rw [hq]
      nlinarith only [hh]
    exact_mod_cast hres
  · intro i hi
    have hiR : 0 < marginal P (d i) r := by rw [← hq]; exact_mod_cast hi
    have hh := upper_comparison hP hiR
    have hres : (d i:ℝ) ≤ (1/(r:ℝ))*(1-(P:ℝ)*(q i:ℝ)) := by
      rw [one_div_mul_eq_div]
      apply (le_div_iff₀ hrR).mpr
      rw [hq]
      nlinarith only [hh]
    exact_mod_cast hres
  · intro R hR hm
    have hh := (div_le_iff₀ hR).mp (hmax (1/R) hm)
    change ((1/r:ℚ):ℝ) ≤ R
    push_cast
    exact (div_le_iff₀ hrR).mpr (by nlinarith only [hh])

end MetricKMedian.Taper
end
end

end OAI
