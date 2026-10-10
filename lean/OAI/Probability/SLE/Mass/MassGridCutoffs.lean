import OAI.Probability.SLE.Mass.MassGridOverlap
import OAI.Probability.SLE.Mass.LevelRadonMoments

namespace OAI

/-! Compact spatial test functions adapted to the mass grid. A fixed
compact cutoff keeps every enlarged grid cell inside the open half-plane. -/

noncomputable section
open Set Metric Filter MeasureTheory Classical
open scoped ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

lemma exists_unit_compact_test_cutoff (K : Set upperHalfPlane) (hK : IsCompact K) :
    ∃ f : C_c(upperHalfPlane,ℝ), (∀ z, 0 ≤ f z ∧ f z ≤ 1) ∧ ∀ z ∈ K, f z = 1 := by
  let : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace
  obtain ⟨f,hf,hfc,_,h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    hK isOpen_univ (subset_univ K)
  exact ⟨⟨f,hfc⟩,h01,fun z hz => hf hz⟩

def massGridBump (r : ℝ) (i : ℤ×ℤ) : C(upperHalfPlane,ℝ) :=
  ⟨fun z => max 0 (min 1 ((3*r-dist (z:ℂ) (coverGridCenter r i))/r)), by fun_prop⟩

def massGridCutoff (χ : C_c(upperHalfPlane,ℝ)) (r : ℝ) (i : ℤ×ℤ) :
    C_c(upperHalfPlane,ℝ) := massGridBump r i • χ

lemma massGridBump_bounds (r : ℝ) (i : ℤ×ℤ) (z : upperHalfPlane) :
    0 ≤ massGridBump r i z ∧ massGridBump r i z ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma massGridBump_eq_one {r : ℝ} (hr : 0 < r) (i : ℤ×ℤ) (z : upperHalfPlane)
    (hz : dist (z:ℂ) (coverGridCenter r i) ≤ 2*r) : massGridBump r i z = 1 := by
  have hh : 1 ≤ (3*r-dist (z:ℂ) (coverGridCenter r i))/r := (le_div_iff₀ hr).mpr (by linarith)
  simp only [massGridBump,ContinuousMap.coe_mk,min_eq_left hh,max_eq_right (by norm_num : (0:ℝ)≤1)]

lemma massGridBump_eq_zero {r : ℝ} (hr : 0 < r) (i : ℤ×ℤ) (z : upperHalfPlane)
    (hz : 3*r < dist (z:ℂ) (coverGridCenter r i)) : massGridBump r i z = 0 := by
  have hh : (3*r-dist (z:ℂ) (coverGridCenter r i))/r ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
  apply max_eq_left
  exact (min_le_right _ _).trans hh

lemma massGridCutoff_bounds (χ : C_c(upperHalfPlane,ℝ))
    (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) (r : ℝ) (i : ℤ×ℤ) (z : upperHalfPlane) :
    0 ≤ massGridCutoff χ r i z ∧ massGridCutoff χ r i z ≤ 1 := by
  have hb := massGridBump_bounds r i z
  change 0 ≤ massGridBump r i z * χ z ∧ massGridBump r i z * χ z ≤ 1
  exact ⟨mul_nonneg hb.1 (hχ z).1,(mul_le_mul_of_nonneg_right hb.2 (hχ z).1).trans (by simpa only [one_mul] using (hχ z).2)⟩

lemma massGridCutoff_eq_one (χ : C_c(upperHalfPlane,ℝ)) {r : ℝ} (hr : 0 < r)
    (i : ℤ×ℤ) (z : upperHalfPlane) (hχ : χ z = 1)
    (hz : dist (z:ℂ) (coverGridCenter r i) ≤ 2*r) : massGridCutoff χ r i z = 1 := by
  change massGridBump r i z * χ z = 1
  rw [massGridBump_eq_one hr i z hz,hχ,one_mul]

lemma massGridCutoff_support (χ : C_c(upperHalfPlane,ℝ)) {r : ℝ} (hr : 0 < r)
    (i : ℤ×ℤ) (z : ℂ) (hz : extendHalfPlaneTest (massGridCutoff χ r i) z ≠ 0) :
    dist z (coverGridCenter r i) ≤ 3*r := by
  by_cases hH : z ∈ upperHalfPlane
  · by_contra h
    have he := massGridBump_eq_zero hr i ⟨z,hH⟩ (lt_of_not_ge h)
    apply hz
    rw [show z = (⟨z,hH⟩ : upperHalfPlane).val from rfl,extendHalfPlaneTest_apply]
    change massGridBump r i ⟨z,hH⟩ * χ ⟨z,hH⟩ = 0
    rw [he,zero_mul]
  · exact False.elim (hz (extendHalfPlaneTest_of_not_mem _ z hH))

lemma massGridCutoff_common_support (χ : C_c(upperHalfPlane,ℝ)) (r : ℝ) (i : ℤ×ℤ)
    (z : ℂ) (hz : z ∉ (Subtype.val : upperHalfPlane → ℂ) '' tsupport χ) :
    extendHalfPlaneTest (massGridCutoff χ r i) z = 0 := by
  by_cases hH : z ∈ upperHalfPlane
  · let x : upperHalfPlane := ⟨z,hH⟩
    have hχ : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz ⟨x,h,rfl⟩)
    change extendHalfPlaneTest (massGridCutoff χ r i) x = 0
    rw [extendHalfPlaneTest_apply]
    change massGridBump r i x * χ x = 0
    rw [hχ,mul_zero]
  · exact extendHalfPlaneTest_of_not_mem _ z hH

lemma massGridCutoff_sum_bound (χ : C_c(upperHalfPlane,ℝ))
    (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) {r : ℝ} (hr : 0 < r) (I : Finset (ℤ×ℤ))
    (x y : ℂ) :
    (∑ i ∈ I, ENNReal.ofReal (extendHalfPlaneTest (massGridCutoff χ r i) x) *
      ENNReal.ofReal (extendHalfPlaneTest (massGridCutoff χ r i) y)) ≤
        if dist x y ≤ 6*r then 81 else 0 := by
  refine massGrid_cutoff_product_sum_le hr I
    (fun i z => ENNReal.ofReal (extendHalfPlaneTest (massGridCutoff χ r i) z)) ?_ ?_ x y
  · intro i z
    apply ENNReal.ofReal_le_one.mpr
    by_cases hH : z ∈ upperHalfPlane
    · rw [show z = (⟨z,hH⟩ : upperHalfPlane).val from rfl,extendHalfPlaneTest_apply]
      exact (massGridCutoff_bounds χ hχ r i ⟨z,hH⟩).2
    · rw [extendHalfPlaneTest_of_not_mem _ z hH]
      norm_num
  · intro i z hz
    apply massGridCutoff_support χ hr i z
    intro he
    exact hz (by rw [he,ENNReal.ofReal_zero])

end SLEExactGauge.Multipoint

end

end OAI
