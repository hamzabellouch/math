import OAI.Geometry.CylinderCovering.Nilpotent.GridDefinitions

namespace OAI

noncomputable section
open Set
namespace NilpotentGrid

lemma gridBound_nonneg {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    0 ≤ gridBound δ B := Int.ceil_nonneg (div_nonneg hB hδ.le)

lemma indexRange_card {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ((indexRange δ B).card : ℝ) = 2 * (gridBound δ B : ℝ) + 2 := by
  have hm := gridBound_nonneg hδ hB
  have h := Int.card_Icc_of_le (-gridBound δ B - 1) (gridBound δ B) (show -gridBound δ B - 1 ≤ gridBound δ B + 1 by omega)
  change ((Finset.Icc (-gridBound δ B - 1) (gridBound δ B)).card : ℝ) = _
  have hr := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at hr
  linarith only [hr]

lemma candidates_card {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ((candidates δ B).card : ℝ) = (2 * (gridBound δ B : ℝ) + 2) ^ 2 := by
  unfold candidates
  rw [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul, indexRange_card hδ hB]
  ring

lemma mem_indexRange_of_cell {δ B x : ℝ} {z : ℤ}
    (hδ : 0 < δ) (hx : |x| ≤ B)
    (hl : δ * (z : ℝ) ≤ x) (hu : x ≤ δ * ((z : ℝ) + 1)) :
    z ∈ indexRange δ B := by
  have hceil : B / δ ≤ (gridBound δ B : ℝ) := Int.le_ceil _
  have hceil' : B ≤ δ * (gridBound δ B : ℝ) := by
    have := mul_le_mul_of_nonneg_left hceil hδ.le
    field_simp at this
    nlinarith only [this]
  have hbounds := abs_le.mp hx
  have hlow : (-(gridBound δ B : ℝ) - 1) ≤ (z : ℝ) := by
    nlinarith only [hu, hbounds.1, hceil', hδ]
  have hhigh : (z : ℝ) ≤ (gridBound δ B : ℝ) := by
    nlinarith only [hl, hbounds.2, hceil', hδ]
  simp only [indexRange, Finset.mem_Icc]
  constructor
  · exact_mod_cast hlow
  · exact_mod_cast hhigh

lemma mem_coarseIndices_iff {δ B : ℝ} {D : Set Plane}
    (hδ : 0 < δ) (hD : ∀ x ∈ D, |x 0| ≤ B ∧ |x 1| ≤ B) (z : ℤ × ℤ) :
    z ∈ coarseIndices δ B D ↔ (D ∩ coarseCell δ z).Nonempty := by
  classical
  simp only [coarseIndices, Finset.mem_filter, and_iff_right_iff_imp]
  rintro ⟨x, hxD, hx⟩
  obtain ⟨hx0, hx1⟩ := hD x hxD
  exact Finset.mem_product.mpr
    ⟨mem_indexRange_of_cell hδ hx0 hx.1 hx.2.1,
      mem_indexRange_of_cell hδ hx1 hx.2.2.1 hx.2.2.2⟩

lemma floor_cell {δ x : ℝ} (hδ : 0 < δ) :
    δ * (⌊x / δ⌋ : ℤ) ≤ x ∧ x ≤ δ * ((⌊x / δ⌋ : ℤ) + (1 : ℝ)) := by
  have hlow := Int.floor_le (x / δ)
  have hhigh := (Int.lt_floor_add_one (x / δ)).le
  have h1 := mul_le_mul_of_nonneg_left hlow hδ.le
  have h2 := mul_le_mul_of_nonneg_left hhigh hδ.le
  have hcancel : δ * (x / δ) = x := by field_simp
  rw [hcancel] at h1 h2
  exact ⟨h1, h2⟩

lemma subset_coarseUnion {δ B : ℝ} {D : Set Plane}
    (hδ : 0 < δ) (hD : ∀ x ∈ D, |x 0| ≤ B ∧ |x 1| ≤ B) :
    D ⊆ coarseUnion δ B D := by
  intro x hx
  let z : ℤ × ℤ := (⌊x 0 / δ⌋, ⌊x 1 / δ⌋)
  have h0 := floor_cell (x := x 0) hδ
  have h1 := floor_cell (x := x 1) hδ
  have hcell : x ∈ coarseCell δ z := ⟨h0.1, h0.2, h1.1, h1.2⟩
  have hz : z ∈ coarseIndices δ B D := (mem_coarseIndices_iff hδ hD z).mpr ⟨x, hx, hcell⟩
  exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, hcell⟩⟩

theorem coarse_count_bound {δ B : ℝ} (D : Set Plane)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) :
    ((coarseIndices δ B D).card : ℝ) * δ ^ 2 ≤ (2 * B + 4) ^ 2 := by
  have hcard : (coarseIndices δ B D).card ≤ (candidates δ B).card := by
    classical
    exact Finset.card_filter_le _ _
  have hcardR : ((coarseIndices δ B D).card : ℝ) ≤ ((candidates δ B).card : ℝ) := by
    exact_mod_cast hcard
  rw [candidates_card hδ hB] at hcardR
  have hceil : (gridBound δ B : ℝ) ≤ B / δ + 1 := (Int.ceil_lt_add_one _).le
  have hmul := mul_le_mul_of_nonneg_left hceil hδ.le
  have hcancel : δ * (B / δ) = B := by field_simp
  rw [mul_add, hcancel, mul_one] at hmul
  have hm0 : (0 : ℝ) ≤ gridBound δ B := by exact_mod_cast gridBound_nonneg hδ hB
  have hside : (2 * (gridBound δ B : ℝ) + 2) * δ ≤ 2 * B + 4 := by
    nlinarith only [hmul, hδ1]
  have hside0 : 0 ≤ (2 * (gridBound δ B : ℝ) + 2) * δ := by positivity
  have hsquare := (sq_le_sq₀ hside0 (by positivity : (0 : ℝ) ≤ 2 * B + 4)).mpr hside
  have hc := mul_le_mul_of_nonneg_right hcardR (sq_nonneg δ)
  nlinarith only [hsquare, hc]

lemma same_cell_distance {δ : ℝ} {z : ℤ × ℤ} {x y : Plane}
    (hδ : 0 ≤ δ) (hx : x ∈ coarseCell δ z) (hy : y ∈ coarseCell δ z) :
    ‖x - y‖ ≤ Real.sqrt 2 * δ := by
  have h0 : |x 0 - y 0| ≤ δ := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2.1, hy.1, hy.2.1]
  have h1 : |x 1 - y 1| ≤ δ := by
    rw [abs_le]
    constructor <;> linarith [hx.2.2.1, hx.2.2.2, hy.2.2.1, hy.2.2.2]
  have hs0 : (x 0 - y 0) ^ 2 ≤ δ ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg _) hδ).mpr h0
    simpa only [sq_abs] using this
  have hs1 : (x 1 - y 1) ^ 2 ≤ δ ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg _) hδ).mpr h1
    simpa only [sq_abs] using this
  have hnorm : ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, PiLp.sub_apply]
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htarget : 0 ≤ Real.sqrt 2 * δ := by positivity
  have htargetsq : (Real.sqrt 2 * δ) ^ 2 = 2 * δ ^ 2 := by rw [mul_pow, hsqrt]
  nlinarith only [hs0, hs1, hnorm, htarget, htargetsq, norm_nonneg (x - y)]

theorem coarseUnion_near {δ B : ℝ} {D : Set Plane} {x : Plane}
    (hδ : 0 ≤ δ) (hx : x ∈ coarseUnion δ B D) :
    ∃ y ∈ D, ‖x - y‖ ≤ Real.sqrt 2 * δ := by
  classical
  obtain ⟨z, hz⟩ := mem_iUnion.mp hx
  obtain ⟨hzi, hxcell⟩ := mem_iUnion.mp hz
  have hmeet := (Finset.mem_filter.mp hzi).2
  obtain ⟨y, hyD, hycell⟩ := hmeet
  exact ⟨y, hyD, same_cell_distance hδ hxcell hycell⟩

lemma coarseCell_isCompact (δ : ℝ) (z : ℤ × ℤ) : IsCompact (coarseCell δ z) := by
  let f : ℝ × ℝ → Plane := fun p => RuledApproximation.vec2 p.1 p.2
  have hf : Continuous f := by dsimp [f, RuledApproximation.vec2]; fun_prop
  have heq : coarseCell δ z = f ''
      (Icc (δ * (z.1 : ℝ)) (δ * ((z.1 : ℝ) + 1)) ×ˢ
       Icc (δ * (z.2 : ℝ)) (δ * ((z.2 : ℝ) + 1))) := by
    ext x
    constructor
    · intro hx
      refine ⟨(x 0, x 1), ⟨⟨hx.1, hx.2.1⟩, ⟨hx.2.2.1, hx.2.2.2⟩⟩, ?_⟩
      ext i
      fin_cases i <;> rfl
    · rintro ⟨⟨s,t⟩, ⟨hs, ht⟩, rfl⟩
      exact ⟨hs.1, hs.2, ht.1, ht.2⟩
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).image hf

lemma coarseUnion_isCompact (δ B : ℝ) (D : Set Plane) : IsCompact (coarseUnion δ B D) := by
  exact (coarseIndices δ B D).finite_toSet.isCompact_biUnion
    (fun z _ => coarseCell_isCompact δ z)

end NilpotentGrid

end

end OAI
