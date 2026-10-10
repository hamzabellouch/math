import OAI.Probability.GammaPassage.GridMeshes

namespace OAI

/-! Finite supersets of grid intervals and transverse bins, with cardinality
bounds independent of the characteristic scale. -/
namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Finset Set

noncomputable def gridIndexRange (x : ℝ) : Finset ℤ :=
  Finset.Icc (-(⌈x⌉₊ : ℤ)) ⌈x⌉₊

lemma gridIndexRange_card (x : ℝ) : (gridIndexRange x).card=2*⌈x⌉₊+1 := by
  rw [gridIndexRange,Int.card_Icc]
  omega

lemma mem_gridIndexRange_of_abs_le (x : ℝ) (i : ℤ) (hi : |(i : ℝ)| ≤ x) :
    i ∈ gridIndexRange x := by
  have hn := hi.trans (Nat.le_ceil x)
  have hn' : |i| ≤ (⌈x⌉₊ : ℤ) := by exact_mod_cast hn
  exact Finset.mem_Icc.mpr (abs_le.mp hn')

noncomputable def gridTestIndices (A R L s l w : ℝ) : Finset (ℤ × ℤ) :=
  gridIndexRange ((A+4)*L/l) ×ˢ gridIndexRange (R*s/w+1)

noncomputable def gridIndexConstant (A R : ℝ) : ℝ :=
  2*(2*(A+4)+3)*(2*R+5)

lemma gridIndexConstant_pos (A R : ℝ) (hA : 0 < A) (hR : 0 < R) :
    0 < gridIndexConstant A R := by unfold gridIndexConstant; positivity

lemma gridTestIndices_card (A R L s l w : ℝ) (hA : 0 < A) (hR : 0 < R)
    (hl : 0 < l) (hw : 0 < w) (hLl : 1 ≤ L/l) (hsw : 1 ≤ s/w) :
    ((gridTestIndices A R L s l w).card : ℝ) ≤
      (2*(A+4)+3)*(2*R+5)*(L/l)*(s/w) := by
  have hL : 0 ≤ L := by have hh := (le_div_iff₀ hl).mp hLl; linarith
  have hs : 0 ≤ s := by have hh := (le_div_iff₀ hw).mp hsw; linarith
  have hc₁ := Nat.ceil_lt_add_one (show 0 ≤ (A+4)*L/l by positivity)
  have hc₂ := Nat.ceil_lt_add_one (show 0 ≤ R*s/w+1 by positivity)
  have hc₁' : 2*(⌈(A+4)*L/l⌉₊ : ℝ)+1 ≤ (2*(A+4)+3)*(L/l) := by
    simp only [mul_div_assoc] at hc₁ ⊢
    nlinarith
  have hc₂' : 2*(⌈R*s/w+1⌉₊ : ℝ)+1 ≤ (2*R+5)*(s/w) := by
    simp only [mul_div_assoc] at hc₂ ⊢
    nlinarith
  rw [gridTestIndices,Finset.card_product,gridIndexRange_card,gridIndexRange_card]
  push_cast
  have hh := mul_le_mul hc₁' hc₂' (by positivity) (by positivity)
  nlinarith

lemma gridTestIndices_level_card (A R : ℝ) (hA : 0 < A) (hR : 0 < R)
    (k m j : ℕ) (hj : j ≤ k) :
    ((gridTestIndices A R ((2 : ℝ)^m) ((2 : ℝ)^k)
      (gridMesh m j) (gridWidth k j)).card : ℝ) ≤ gridIndexConstant A R*(2 : ℝ)^(5*j) := by
  have hl : (0 : ℝ) < gridMesh m j := by exact_mod_cast gridMesh_pos m j
  have hw : (0 : ℝ) < gridWidth k j := by exact_mod_cast gridWidth_pos k j
  have hLl : 1 ≤ (2 : ℝ)^m/(gridMesh m j : ℝ) := by
    apply (le_div_iff₀ hl).mpr
    simp only [one_mul,gridMesh,Int.cast_pow,Int.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hsw : 1 ≤ (2 : ℝ)^k/(gridWidth k j : ℝ) := by
    rw [gridWidth_ratio k j hj]
    exact one_le_pow₀ (by norm_num)
  apply (gridTestIndices_card A R _ _ _ _ hA hR hl hw hLl hsw).trans
  rw [gridWidth_ratio k j hj]
  calc
    _ ≤ (2*(A+4)+3)*(2*R+5)*(2 : ℝ)^(4*j+1)*(2 : ℝ)^j := by
      gcongr
      exact gridMesh_count_ratio m j
    _ = _ := by
      rw [mul_assoc ((2*(A+4)+3)*(2*R+5)),← pow_add,
        show 4*j+1+j=5*j+1 by omega,pow_succ]
      unfold gridIndexConstant
      ring

lemma grid_interval_index_mem (A R L s : ℝ) (l w : ℤ) (hl : 0 < l) (hw : 0 < w)
    (i : ℤ) (r₀ : ℝ)
    (hi : -(A+4)*L ≤ ((l*i : ℤ) : ℝ) ∧ ((l*i : ℤ) : ℝ) ≤ (A+4)*L)
    (hr : |r₀| ≤ R*s) :
    (i,⌊r₀/(w : ℝ)⌋) ∈ gridTestIndices A R L s l w := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  apply Finset.mem_product.mpr
  constructor
  · apply mem_gridIndexRange_of_abs_le
    rw [le_div_iff₀ hl']
    have hh : |((l*i : ℤ) : ℝ)| ≤ (A+4)*L := abs_le.mpr (by simpa only [neg_mul] using hi)
    rw [Int.cast_mul,abs_mul,abs_of_pos hl'] at hh
    nlinarith
  · apply mem_gridIndexRange_of_abs_le
    have hf := Int.floor_le (r₀/(w : ℝ))
    have hf' := Int.lt_floor_add_one (r₀/(w : ℝ))
    have hr' : |r₀/(w : ℝ)| ≤ R*s/w := by
      rw [abs_div,abs_of_pos hw']
      exact div_le_div_of_nonneg_right hr hw'.le
    have hh := abs_le.mp hr'
    apply abs_le.mpr
    constructor <;> linarith [hh.1,hh.2]

lemma grid_bin_floor (w : ℤ) (hw : 0 < w) (r : ℝ) :
    (⌊r/(w : ℝ)⌋ : ℝ)*w ≤ r ∧ r ≤ ((⌊r/(w : ℝ)⌋ : ℝ)+1)*w := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  exact ⟨(le_div_iff₀ hw').mp (Int.floor_le _),
    ((div_lt_iff₀ hw').mp (Int.lt_floor_add_one _)).le⟩

end GammaFPP.CrossingBridge

end OAI
