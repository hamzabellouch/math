import OAI.Analysis.LipschitzHilbert.Trees.SourceWhitneyIntervals
import Mathlib.MeasureTheory.Measure.Real

namespace OAI

/-! Quantitative packing of the actual Whitney intervals used in the
ordinary tree estimate. Bounds are on arbitrary finite subfamilies and
therefore also support subsequent monotone summation. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid

/-- A parent witness locates the entire Whitney cell near the horizontal top. -/
theorem cell_subset_top_enlargement {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L : ℝ}
    (hcenters : ∀ i ∈ tiles, |x i-c| ≤ L/2) {k j : ℤ}
    (h : Whitney tiles x ell k j) :
    cell 0 k j ⊆ Icc (c-(4*scale k+L/2)) (c+(4*scale k+L/2)) := by
  obtain ⟨i,hi,_,hw⟩ := parent_witness tiles x ell h
  intro z hz
  have hbound : |z-c| ≤ 4*scale k+L/2 := by
    have ht := abs_sub_le z (x i) c
    rw [abs_sub_comm z (x i)] at ht
    linarith only [ht,hw z hz,hcenters i hi]
  exact ⟨by linarith [(abs_le.mp hbound).1],by linarith [(abs_le.mp hbound).2]⟩

/-- A finite subfamily with lengths at most `r` has total length at most
`8r+L`, where the tile centers lie in an interval of length `L`. -/
theorem finite_length_budget {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L r : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hcenters : ∀ i ∈ tiles, |x i-c| ≤ L/2)
    (S : Finset (ℤ×ℤ))
    (hW : ∀ p ∈ S, Whitney tiles x ell p.1 p.2)
    (hscale : ∀ p ∈ S, scale p.1 ≤ r) :
    ∑ p ∈ S, scale p.1 ≤ 8*r+L := by
  have hsub (p) (hp : p ∈ S) :
      cell 0 p.1 p.2 ⊆ Icc (c-(4*r+L/2)) (c+(4*r+L/2)) := by
    intro z hz
    have hc := cell_subset_top_enlargement tiles x ell hcenters (hW p hp) hz
    have hs := hscale p hp
    exact ⟨by linarith [hc.1],by linarith [hc.2]⟩
  have hdisj : Set.PairwiseDisjoint (S : Set (ℤ×ℤ)) (fun p => cell 0 p.1 p.2) := by
    intro p hp q hq hpq
    exact whitney_disjoint tiles x ell (hW p hp) (hW q hq) (by simpa using hpq)
  calc
    ∑ p ∈ S, scale p.1 = ∑ p ∈ S, volume.real (cell 0 p.1 p.2) := by
      simp only [cell_length]
    _ = volume.real (⋃ p ∈ S, cell 0 p.1 p.2) :=
      (measureReal_biUnion_finset hdisj (fun p _ => cell_measurable 0 p.1 p.2)
        (fun _ _ => measure_Ico_lt_top.ne)).symm
    _ ≤ volume.real (Icc (c-(4*r+L/2)) (c+(4*r+L/2))) := by
      apply measureReal_mono _ measure_Icc_lt_top.ne
      intro z hz
      obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
      exact hsub p hp hz
    _ = 8*r+L := by
      rw [Real.volume_real_Icc_of_le (by linarith)]
      ring

/-- The small Whitney cells have a summable total length controlled by
the top length. -/
theorem small_length_budget {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L : ℝ} (hL : 0 ≤ L)
    (hcenters : ∀ i ∈ tiles, |x i-c| ≤ L/2)
    (S : Finset (ℤ×ℤ))
    (hW : ∀ p ∈ S, Whitney tiles x ell p.1 p.2)
    (hscale : ∀ p ∈ S, scale p.1 ≤ L) :
    ∑ p ∈ S, scale p.1 ≤ 9*L := by
  have h := finite_length_budget tiles x ell hL hL hcenters S hW hscale
  linarith only [h]

/-- At each length larger than the top there are at most nine Whitney
cells. This is the multiplicity needed for the geometric tail. -/
theorem large_scale_card {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L : ℝ} (hL : 0 ≤ L)
    (hcenters : ∀ i ∈ tiles, |x i-c| ≤ L/2) (k : ℤ) (hk : L ≤ scale k)
    (J : Finset ℤ) (hW : ∀ j ∈ J, Whitney tiles x ell k j) :
    J.card ≤ 9 := by
  classical
  let S := J.image (fun j => (k,j))
  have hScard : S.card = J.card := Finset.card_image_of_injective J (by
    intro i j h
    exact (Prod.mk.inj h).2)
  have hsum : (∑ p ∈ S, scale p.1) = J.card*scale k := by
    rw [Finset.sum_image]
    · simp
    · intro i _ j _ h
      exact (Prod.mk.inj h).2
  have h := finite_length_budget tiles x ell hL (scale_pos k).le hcenters S
    (by intro p hp; obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp; exact hW j hj)
    (by intro p hp; obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp; exact le_rfl)
  rw [hsum] at h
  have hc : (J.card:ℝ) ≤ 9 := (mul_le_mul_iff_left₀ (scale_pos k)).mp (by nlinarith only [h,hk])
  exact_mod_cast hc

end LipschitzHilbert.SourceWhitney

end

end OAI
