import OAI.NumberTheory.TwoPoint.Halasz.HalaszIntegerWindow
import OAI.NumberTheory.TwoPoint.Halasz.HalaszDifferenceCount
import OAI.NumberTheory.TwoPoint.Halasz.HalaszScaledFrequency

namespace OAI

/-! Nearby pairs of moment frequencies are controlled by the zero moment
and a product of one-dimensional near-integer counts. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszIntegerWindow (L : ℕ) (γ δ : ℝ) : Finset ℤ :=
  (Icc (-(L:ℤ)) L).filter (fun d => ‖((γ*(d:ℝ):ℝ):AddCircle (1:ℝ))‖≤δ)

lemma halasz_integer_window_size (L : ℕ) {γ δ : ℝ}
    (hγ : 0<γ) (hδ : 0≤δ) (hδhalf : δ≤1/2) :
    ((halaszIntegerWindow L γ δ).card:ℝ)≤4*(L:ℝ)*δ+2*L*γ+4*δ/γ+2 := by
  apply halasz_integer_window_card _ (Nat.cast_nonneg _) hγ hδ hδhalf
  intro d hd
  obtain ⟨hd,hn⟩ := mem_filter.mp hd
  refine ⟨?_,hn⟩
  obtain ⟨hl,hu⟩ := mem_Icc.mp hd
  exact_mod_cast abs_le.mpr ⟨hl,hu⟩

lemma halasz_integer_window_trivial (L : ℕ) (γ δ : ℝ) :
    ((halaszIntegerWindow L γ δ).card:ℝ)≤2*(L:ℝ)+1 := by
  have h := card_filter_le (Icc (-(L:ℤ)) L)
    (fun d => ‖((γ*(d:ℝ):ℝ):AddCircle (1:ℝ))‖≤δ)
  have he : ((Icc (-(L:ℤ)) (L:ℤ)).card:ℤ)=2*(L:ℤ)+1 := by
    rw [Int.card_Icc_of_le]
    · ring
    · omega
  have heR : ((Icc (-(L:ℤ)) (L:ℤ)).card:ℝ)=2*(L:ℝ)+1 := by exact_mod_cast he
  change ((halaszIntegerWindow L γ δ).card:ℝ)≤_
  rw [← heR]
  exact_mod_cast h

theorem halasz_near_pair_count {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (L : Fin k → ℕ) (γ δ : Fin k → ℝ)
    (hγ : ∀ j,0<γ j) (hδ : ∀ j,0≤δ j) (hδquarter : ∀ j,δ j≤1/4)
    (hdiff : ∀ x y j, |f x j-f y j|≤(L j:ℤ)) :
    ((univ.filter (fun xy : ι×ι => HalaszWindowNear δ
      (halaszScaledFrequency γ (f xy.1)) (halaszScaledFrequency γ (f xy.2)))).card:ℝ)≤
      (halaszRepresentationCount f 0:ℝ)*
        ∏ j,min (2*(L j:ℝ)+1) (8*(L j:ℝ)*δ j+2*L j*γ j+8*δ j/γ j+2) := by
  let W := Fintype.piFinset (fun j => halaszIntegerWindow (L j) (γ j) (2*δ j))
  have hsub : univ.filter (fun xy : ι×ι => HalaszWindowNear δ
      (halaszScaledFrequency γ (f xy.1)) (halaszScaledFrequency γ (f xy.2))) ⊆
      univ.filter (fun xy : ι×ι => f xy.1-f xy.2∈W) := by
    intro xy hxy
    have hn := (mem_filter.mp hxy).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,Fintype.mem_piFinset.mpr ?_⟩
    intro j
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr (abs_le.mp (hdiff xy.1 xy.2 j)),?_⟩
    have hh := hn j
    simpa only [halaszScaledFrequency,Pi.sub_apply,← AddCircle.coe_sub,
      ← mul_sub,← Int.cast_sub] using hh
  have hcount := (card_le_card hsub).trans (halasz_difference_set_count f W)
  have hW : (W.card:ℝ)≤∏ j,min (2*(L j:ℝ)+1) (8*(L j:ℝ)*δ j+2*L j*γ j+8*δ j/γ j+2) := by
    simp only [W,Fintype.card_piFinset,Nat.cast_prod]
    apply prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
    intro j _
    have hh := halasz_integer_window_size (L j) (hγ j)
      (show 0≤2*δ j from mul_nonneg (by norm_num) (hδ j)) (show 2*δ j≤1/2 by linarith [hδquarter j])
    apply le_min (halasz_integer_window_trivial (L j) (γ j) (2*δ j))
    convert hh using 1; ring
  calc
    _ ≤ (W.card:ℝ)*(halaszRepresentationCount f 0:ℝ) := by exact_mod_cast hcount
    _ ≤ (∏ j,min (2*(L j:ℝ)+1) (8*(L j:ℝ)*δ j+2*L j*γ j+8*δ j/γ j+2))*
        (halaszRepresentationCount f 0:ℝ) :=
      mul_le_mul_of_nonneg_right hW (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

/-- The lattice count depends only on the absolute coefficient; alternating
Taylor signs therefore incur no additional factor. -/
theorem halasz_near_pair_count_abs {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (L : Fin k → ℕ) (γ δ : Fin k → ℝ)
    (hγ : ∀ j,γ j≠0) (hδ : ∀ j,0≤δ j) (hδquarter : ∀ j,δ j≤1/4)
    (hdiff : ∀ x y j, |f x j-f y j|≤(L j:ℤ)) :
    ((univ.filter (fun xy : ι×ι => HalaszWindowNear δ
      (halaszScaledFrequency γ (f xy.1)) (halaszScaledFrequency γ (f xy.2)))).card:ℝ)≤
      (halaszRepresentationCount f 0:ℝ)*
        ∏ j,min (2*(L j:ℝ)+1)
          (8*(L j:ℝ)*δ j+2*L j* |γ j| +8*δ j/ |γ j| +2) := by
  have he : (univ.filter (fun xy : ι×ι => HalaszWindowNear δ
      (halaszScaledFrequency γ (f xy.1)) (halaszScaledFrequency γ (f xy.2)))) =
      univ.filter (fun xy : ι×ι => HalaszWindowNear δ
        (halaszScaledFrequency (fun j => |γ j|) (f xy.1))
        (halaszScaledFrequency (fun j => |γ j|) (f xy.2))) := by
    ext xy
    simp only [mem_filter,halasz_scaled_near_abs γ δ]
  rw [he]
  exact halasz_near_pair_count f L (fun j => |γ j|) δ
    (fun j => abs_pos.mpr (hγ j)) hδ hδquarter hdiff

end TwoPointCorrelations

end OAI
