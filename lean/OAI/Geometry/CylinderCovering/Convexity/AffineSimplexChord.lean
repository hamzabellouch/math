import OAI.Geometry.CylinderCovering.Simplex.Chord

namespace OAI

open Set
open scoped BigOperators

namespace SimplexChord

variable {ι E : Type*} [AddCommGroup E] [Module ℝ E]

theorem coord_add_smul (p : AffineBasis ι ℝ E) (i : ι) (x u : E) (s : ℝ) :
    p.coord i (x + s • u) = p.coord i x + s * (p.coord i).linear u := by
  simpa only [vadd_eq_add, map_smul, smul_eq_mul, add_comm] using
    (p.coord i).map_vadd x (s • u)

variable [Fintype ι]

theorem sum_coord_linear_eq_zero (p : AffineBasis ι ℝ E) (u : E) :
    (∑ i, (p.coord i).linear u) = 0 := by
  have heq : ∀ i, (p.coord i).linear u = p.coord i u - p.coord i 0 := by
    intro i
    have h := coord_add_smul p i 0 u 1
    simp only [one_smul, zero_add, one_mul] at h
    linarith
  simp_rw [heq]
  rw [Finset.sum_sub_distrib, p.sum_coord_apply_eq_one, p.sum_coord_apply_eq_one]
  ring

theorem coord_linear_ne_zero (p : AffineBasis ι ℝ E) {u : E} (hu : u ≠ 0) :
    (fun i => (p.coord i).linear u) ≠ 0 := by
  intro h
  apply hu
  apply p.ext_elem
  intro i
  have hi := congrFun h i
  have hm := coord_add_smul p i 0 u 1
  simp only [one_smul, zero_add, one_mul] at hm
  simp only [Pi.zero_apply] at hi
  rw [hi, add_zero] at hm
  exact hm

theorem mem_convexHull_iff_coord_mem (p : AffineBasis ι ℝ E) (x : E) :
    x ∈ convexHull ℝ (Set.range p) ↔
      (fun i => p.coord i x) ∈ standardSimplex := by
  rw [p.convexHull_eq_nonneg_coord]
  exact ⟨fun hx => ⟨hx, p.sum_coord_apply_eq_one x⟩, fun hx => hx.1⟩

theorem exists_point_with_coords (p : AffineBasis ι ℝ E) (w : ι → ℝ)
    (hw : ∑ i, w i = 1) : ∃ x : E, ∀ i, p.coord i x = w i := by
  refine ⟨Finset.univ.affineCombination ℝ p w, ?_⟩
  intro i
  exact p.coord_apply_combination_of_mem (Finset.mem_univ i) hw

theorem affine_endpoints_iff (p : AffineBasis ι ℝ E) (x u : E)
    {s : ℝ} (hs : 0 ≤ s) :
    (x ∈ convexHull ℝ (Set.range p) ∧
      x + s • u ∈ convexHull ℝ (Set.range p)) ↔
    ∀ i, s * max 0 (-(p.coord i).linear u) ≤ p.coord i x := by
  rw [mem_convexHull_iff_coord_mem p x,
    mem_convexHull_iff_coord_mem p (x + s • u)]
  simp_rw [coord_add_smul]
  rw [endpoints_iff _ _ (sum_coord_linear_eq_zero p u) hs]
  exact and_iff_left (p.sum_coord_apply_eq_one x)

theorem affine_exists_chord_iff (p : AffineBasis ι ℝ E) {u : E} (hu : u ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) :
    (∃ x : E, x ∈ convexHull ℝ (Set.range p) ∧
      x + s • u ∈ convexHull ℝ (Set.range p)) ↔
    s * (∑ i, max 0 (-(p.coord i).linear u)) ≤ 1 := by
  constructor
  · rintro ⟨x, hx, hy⟩
    apply chord_bound (fun i => (p.coord i).linear u) (fun i => p.coord i x)
      (sum_coord_linear_eq_zero p u) hs
    · exact (mem_convexHull_iff_coord_mem p x).mp hx
    · simpa only [coord_add_smul] using
        (mem_convexHull_iff_coord_mem p (x + s • u)).mp hy
  · intro hsc
    obtain ⟨w, hw, hz⟩ := (exists_chord_iff (fun i => (p.coord i).linear u)
      (sum_coord_linear_eq_zero p u) (coord_linear_ne_zero p hu) hs).mpr hsc
    obtain ⟨x, hx⟩ := exists_point_with_coords p w hw.2
    refine ⟨x, (mem_convexHull_iff_coord_mem p x).mpr ?_,
      (mem_convexHull_iff_coord_mem p (x + s • u)).mpr ?_⟩
    · simpa only [hx] using hw
    · simpa only [coord_add_smul, hx] using hz

theorem affine_maximal_chord (p : AffineBasis ι ℝ E) {u : E} (hu : u ≠ 0) :
    let c := ∑ i, max 0 (-(p.coord i).linear u)
    0 < c ∧
    (∃ x : E, x ∈ convexHull ℝ (Set.range p) ∧
      x + (1 / c) • u ∈ convexHull ℝ (Set.range p)) ∧
    ∀ (x : E) (s : ℝ), 0 ≤ s → x ∈ convexHull ℝ (Set.range p) →
      x + s • u ∈ convexHull ℝ (Set.range p) → s ≤ 1 / c := by
  dsimp only
  have hc := negative_mass_pos (fun i => (p.coord i).linear u)
    (sum_coord_linear_eq_zero p u) (coord_linear_ne_zero p hu)
  refine ⟨hc, ?_, ?_⟩
  · apply (affine_exists_chord_iff p hu (one_div_nonneg.mpr hc.le)).mpr
    rw [one_div_mul_cancel (ne_of_gt hc)]
  · intro x s hs hx hy
    apply (le_div_iff₀ hc).mpr
    exact (affine_exists_chord_iff p hu hs).mp ⟨x, hx, hy⟩

theorem affine_intersection_homothety (p : AffineBasis ι ℝ E) {u : E}
    (hu : u ≠ 0) :
    let c := ∑ i, max 0 (-(p.coord i).linear u)
    ∃ q : E, q ∈ convexHull ℝ (Set.range p) ∧
      (∀ i, p.coord i q = max 0 (-(p.coord i).linear u) / c) ∧
      ∀ s : ℝ, 0 ≤ s → s * c < 1 →
        {x | x ∈ convexHull ℝ (Set.range p) ∧
          x + s • u ∈ convexHull ℝ (Set.range p)} =
        AffineMap.homothety q (1 - s * c) '' convexHull ℝ (Set.range p) := by
  dsimp only
  let b : ι → ℝ := fun i => (p.coord i).linear u
  let c : ℝ := ∑ i, max 0 (-b i)
  have hb := sum_coord_linear_eq_zero p u
  have hc : 0 < c := negative_mass_pos b hb (coord_linear_ne_zero p hu)
  have hsum : (∑ i, max 0 (-b i) / c) = 1 := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hc)
  obtain ⟨q, hq⟩ := exists_point_with_coords p (fun i => max 0 (-b i) / c) hsum
  refine ⟨q, ?_, hq, ?_⟩
  · apply (mem_convexHull_iff_coord_mem p q).mpr
    refine ⟨?_, p.sum_coord_apply_eq_one q⟩
    intro i
    change 0 ≤ p.coord i q
    rw [hq i]
    exact div_nonneg (le_max_left _ _) hc.le
  · intro s hs hsc
    have hcoord : ∀ y i,
        p.coord i (AffineMap.homothety q (1 - s * c) y) =
          s * max 0 (-b i) + (1 - s * c) * p.coord i y := by
      intro y i
      rw [AffineMap.homothety_eq_lineMap, (p.coord i).apply_lineMap,
        AffineMap.lineMap_apply_ring, hq i]
      field_simp
      ring
    ext x
    constructor
    · intro hx
      have hxcoord : (fun i => p.coord i x) ∈
          {w | w ∈ standardSimplex ∧
            (fun i => w i + s * b i) ∈ standardSimplex} := by
        refine ⟨(mem_convexHull_iff_coord_mem p x).mp hx.1, ?_⟩
        simpa only [coord_add_smul] using
          (mem_convexHull_iff_coord_mem p (x + s • u)).mp hx.2
      rw [intersection_homothety b hb hs hsc] at hxcoord
      obtain ⟨w, hw, hwx⟩ := hxcoord
      obtain ⟨y, hy⟩ := exists_point_with_coords p w hw.2
      refine ⟨y, (mem_convexHull_iff_coord_mem p y).mpr ?_, ?_⟩
      · simpa only [hy] using hw
      · apply p.ext_elem
        intro i
        rw [hcoord, hy]
        exact congrFun hwx i
    · rintro ⟨y, hy, rfl⟩
      apply (affine_endpoints_iff p _ u hs).mpr
      intro i
      change s * max 0 (-b i) ≤ _
      rw [hcoord]
      have hypos := ((mem_convexHull_iff_coord_mem p y).mp hy).1 i
      have hn := mul_nonneg (sub_nonneg.mpr hsc.le) hypos
      linarith

theorem linear_image_homothety {F : Type*} [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (q : E) (r : ℝ) (K : Set E) :
    L '' (AffineMap.homothety q r '' K) =
      AffineMap.homothety (L q) r '' (L '' K) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  funext x
  simp only [AffineMap.homothety_apply, vsub_eq_sub,
    vadd_eq_add, map_add, map_smul, map_sub]

end SimplexChord

end OAI
