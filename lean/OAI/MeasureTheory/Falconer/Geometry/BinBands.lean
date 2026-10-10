import OAI.MeasureTheory.Falconer.Geometry.BinOffsets

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

noncomputable def bandOffsets (C : ℝ) : Finset ℤ := Finset.Icc (-(⌈C⌉₊ : ℤ)-2) ((⌈C⌉₊ : ℤ)+2)

 theorem realBin_band_offset {w C s₀ x y : ℝ} (hw : 0 < w)
    (hb : |x-y-s₀| ≤ C*w) {i j : ℤ}
    (hi : x ∈ realBin w i) (hj : y ∈ realBin w j) :
    i-j-⌊s₀/w⌋ ∈ bandOffsets C := by
  have hi1 : (i:ℝ) ≤ x/w := (le_div_iff₀ hw).mpr hi.1
  have hi2 : x/w < (i:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hi.2
  have hj1 : (j:ℝ) ≤ y/w := (le_div_iff₀ hw).mpr hj.1
  have hj2 : y/w < (j:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hj.2
  have hm1 := Int.floor_le (s₀/w)
  have hm2 := Int.lt_floor_add_one (s₀/w)
  have hb' : |x/w-y/w-s₀/w| ≤ C := by
    rw [← sub_div,← sub_div,abs_div,abs_of_pos hw]
    exact (div_le_iff₀ hw).mpr hb
  obtain ⟨hl,hu⟩ := abs_le.mp hb'
  have hC := Nat.le_ceil C
  apply Finset.mem_Icc.mpr
  constructor
  · have h : -((⌈C⌉₊:ℕ):ℝ)-2 ≤ (i:ℝ)-(j:ℝ)-(⌊s₀/w⌋:ℝ) := by linarith
    exact_mod_cast h
  · have h : (i:ℝ)-(j:ℝ)-(⌊s₀/w⌋:ℝ) ≤ ((⌈C⌉₊:ℕ):ℝ)+2 := by linarith
    exact_mod_cast h

 theorem real_bin_shifted_band_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {w : ℝ} (hw : 0 < w) (C s₀ : ℝ) :
    (μ.prod ν) {z : ℝ × ℝ | |z.1-z.2-s₀| ≤ C*w} ≤
      ((bandOffsets C).card : ℝ≥0∞) * (binL2Norm μ w * binL2Norm ν w) := by
  let m : ℤ := ⌊s₀/w⌋
  have hs : {z : ℝ × ℝ | |z.1-z.2-s₀| ≤ C*w} ⊆
      ⋃ h ∈ bandOffsets C, ⋃ j : ℤ, realBin w j ×ˢ realBin w (j-(h+m)) := by
    intro z hz
    let i : ℤ := ⌊z.1/w⌋
    let j : ℤ := ⌊z.2/w⌋
    have hi := realBin_cover hw z.1
    have hj := realBin_cover hw z.2
    refine mem_iUnion.mpr ⟨i-j-m,mem_iUnion.mpr ⟨realBin_band_offset hw hz hi hj,?_⟩⟩
    apply mem_iUnion.mpr
    refine ⟨i,hi,?_⟩
    have he : i-(i-j-m+m)=j := by omega
    simpa only [he] using hj
  calc
    _ ≤ (μ.prod ν) (⋃ h ∈ bandOffsets C, ⋃ j : ℤ,
        realBin w j ×ˢ realBin w (j-(h+m))) := measure_mono hs
    _ ≤ ∑ h ∈ bandOffsets C, (μ.prod ν) (⋃ j : ℤ,
        realBin w j ×ˢ realBin w (j-(h+m))) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _h ∈ bandOffsets C, binL2Norm μ w * binL2Norm ν w :=
      Finset.sum_le_sum (fun h _ => offset_rectangles_mass_le μ ν w (h+m))
    _ = _ := by simp

end PlanarFalconer

end OAI
