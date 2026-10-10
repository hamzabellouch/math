import OAI.Analysis.StrictMeans.HorizontalLength

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma scaled_integer_cells_disjoint {h : ℝ} (hh : 0 < h) :
    Pairwise (fun i j : ℤ => Disjoint (Ico ((i : ℝ)*h) (((i : ℝ)+1)*h))
      (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h))) := by
  have hl (i j : ℤ) (hij : i < j) :
      Disjoint (Ico ((i : ℝ)*h) (((i : ℝ)+1)*h))
        (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)) := by
    have he : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hij)
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hle := mul_le_mul_of_nonneg_right he hh.le
    linarith [hx.2, hy.1]
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · exact hl i j hij'
  · exact (hl j i hij').symm

lemma volume_scaled_integer_cell {h : ℝ} (j : ℤ) :
    volume (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)) = ENNReal.ofReal h := by
  rw [Real.volume_Ico]
  congr 1
  ring

lemma cell_disks_measure_bound {h r : ℝ} (hh : 0 < h) (hr : 0 ≤ r)
    (J : Set ℤ) (c : ℤ → ℂ) {C : ℝ≥0∞}
    (hC : volume (⋃ j : J, Ico (((j : ℤ) : ℝ)*h) ((((j : ℤ) : ℝ)+1)*h)) ≤ C) :
    volume (⋃ j : J, closedBall (c j) r) ≤ ENNReal.ofReal (Real.pi*r^2/h) * C := by
  have hd : Pairwise (fun i j : J => Disjoint
      (Ico (((i : ℤ) : ℝ)*h) ((((i : ℤ) : ℝ)+1)*h))
      (Ico (((j : ℤ) : ℝ)*h) ((((j : ℤ) : ℝ)+1)*h))) :=
    fun i j hij => scaled_integer_cells_disjoint hh (Subtype.coe_ne_coe.mpr hij)
  have he : (∑' j : J, ENNReal.ofReal h) ≤ C := by
    simpa only [measure_iUnion hd (fun _ => measurableSet_Ico), volume_scaled_integer_cell] using hC
  calc
    _ ≤ ∑' j : J, volume (closedBall (c j) r) := measure_iUnion_le _
    _ = ∑' j : J, ENNReal.ofReal (Real.pi*r^2/h) * ENNReal.ofReal h := by
      apply tsum_congr
      intro j
      rw [Complex.volume_closedBall]
      rw [← ENNReal.ofReal_coe_nnreal]
      change ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi = _
      rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (sq_nonneg r),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ = ENNReal.ofReal (Real.pi*r^2/h) * ∑' j : J, ENNReal.ofReal h :=
      ENNReal.tsum_mul_left
    _ ≤ _ := by gcongr

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def cellRectangle : Set UpperHalfPlane :=
  {z | |z.re| ≤ 1 ∧ 1/2 ≤ z.im ∧ z.im ≤ 1}

lemma isCompact_cellRectangle : IsCompact cellRectangle := by
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
  have he : ((↑) '' cellRectangle : Set ℂ) =
      {z | |z.re| ≤ 1 ∧ 1/2 ≤ z.im ∧ z.im ≤ 1} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, by linarith [hz.2.1]⟩, hz, rfl⟩
  rw [he]
  apply (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset
    ((isClosed_le Complex.continuous_re.abs continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))
  intro z hz
  change |z.re| ≤ 1 ∧ 1/2 ≤ z.im ∧ z.im ≤ 1 at hz
  simp only [mem_closedBall, dist_zero_right]
  have hn := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg (by linarith [hz.2.1] : 0 ≤ z.im)] at hn
  linarith [hz.1, hz.2.2]

lemma family_rectangle_bound : ∃ M : ℝ, 0 < M ∧
    ∀ (f : DiskFamily) (z : UpperHalfPlane), z ∈ cellRectangle →
      ‖halfPlaneFunction f z‖ ≤ M := by
  have hc := (isCompact_univ (X := DiskFamily)).prod isCompact_cellRectangle
  obtain ⟨M, hMpos, hM⟩ := (hc.image continuous_halfPlaneFunction).isBounded.subset_ball_lt 0 (0 : ℂ)
  refine ⟨M, hMpos, fun f z hz => ?_⟩
  have hh := hM (mem_image_of_mem (fun p : DiskFamily × UpperHalfPlane => halfPlaneFunction p.1 p.2)
    (show (f,z) ∈ (univ : Set DiskFamily) ×ˢ cellRectangle from ⟨mem_univ _, hz⟩))
  exact (by simpa only [mem_ball, dist_zero_right] using hh : ‖halfPlaneFunction f z‖ < M).le

lemma full_ball_halfplane_subset (z : UpperHalfPlane) :
    ball (z : ℂ) z.im ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have he := im_lower_of_mem_ball hw
  change z.im - z.im < w.im at he
  change 0 < w.im
  linarith

lemma omitted_derivative_bound (f : DiskFamily) {ξ : ℂ}
    (hξ : ξ ∉ halfPlaneFunction f '' {z : ℂ | 0 < z.im}) (z : UpperHalfPlane) :
    z.im * ‖deriv (halfPlaneFunction f) z‖ ≤ 4 * ‖halfPlaneFunction f z - ξ‖ := by
  let F := halfPlaneFunction f
  have hd : DifferentiableOn ℂ (fun w => F w - ξ) (ball (z : ℂ) z.im) :=
    ((halfPlaneFunction_differentiableOn f).mono (full_ball_halfplane_subset z)).sub_const ξ
  have hi : InjOn (fun w => F w - ξ) (ball (z : ℂ) z.im) := by
    intro a ha b hb hab
    exact halfPlaneFunction_injOn f (full_ball_halfplane_subset z ha)
      (full_ball_halfplane_subset z hb) (sub_left_injective hab)
  have he : deriv (fun w => F w - ξ) z = deriv F z := deriv_sub_const ξ
  have hn : deriv (fun w => F w - ξ) z ≠ 0 := by
    rw [he]
    exact halfPlaneFunction_deriv_ne_zero f z.im_pos
  have ho : 0 ∉ (fun w => F w - ξ) '' ball (z : ℂ) z.im := by
    rintro ⟨w, hw, hh⟩
    exact hξ ⟨w, full_ball_halfplane_subset z hw, sub_eq_zero.mp hh⟩
  have hh := omitted_local_quarter_bound z.im_pos hd hi hn ho
  rw [he] at hh
  linarith

lemma cell_rebased_mem (z : UpperHalfPlane) {h u : ℝ} (hh : 0 < h)
    (hlo : h ≤ z.im) (hhi : z.im ≤ 2*h) (hu : |u-z.re| ≤ h) :
    ∃ v : UpperHalfPlane, v ∈ cellRectangle ∧ affineAt z v = (u : ℂ) + (h : ℂ)*I := by
  let v : ℂ := ((u-z.re : ℝ) : ℂ) / (z.im : ℂ) + (h/z.im : ℝ)*I
  have hre : v.re = (u-z.re)/z.im := by simp [v]
  have him : v.im = h/z.im := by simp [v]
  have hv : 0 < v.im := by rw [him]; exact div_pos hh z.im_pos
  refine ⟨⟨v,hv⟩, ?_, ?_⟩
  · change |v.re| ≤ 1 ∧ 1/2 ≤ v.im ∧ v.im ≤ 1
    rw [hre, him, abs_div, abs_of_pos z.im_pos]
    refine ⟨(div_le_one z.im_pos).mpr (hu.trans hlo), ?_, (div_le_one z.im_pos).mpr hlo⟩
    rw [le_div_iff₀ z.im_pos]
    linarith
  · apply Complex.ext <;> simp only [affineAt, v, add_re, add_im,
      mul_re, mul_im, div_ofReal_re, div_ofReal_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero]
    · field_simp
      ring
    · field_simp
      ring

lemma omitted_cell_comparison {M : ℝ} (hM : ∀ (f : DiskFamily) (z : UpperHalfPlane),
    z ∈ cellRectangle → ‖halfPlaneFunction f z‖ ≤ M) (hM0 : 0 ≤ M)
    (f : DiskFamily) {ξ : ℂ} (hξ : ξ ∉ halfPlaneFunction f '' {z : ℂ | 0 < z.im})
    (z : UpperHalfPlane) {h u : ℝ} (hh : 0 < h)
    (hlo : h ≤ z.im) (hhi : z.im ≤ 2*h) (hu : |u-z.re| ≤ h) :
    ‖halfPlaneFunction f ((u : ℂ)+(h : ℂ)*I)-ξ‖ ≤
      (4*M+1)*‖halfPlaneFunction f z-ξ‖ := by
  obtain ⟨v, hv, he⟩ := cell_rebased_mem z hh hlo hhi hu
  have hb := hM (rebase f z) v hv
  rw [halfPlaneFunction_rebase f z v.im_pos, he, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos z.im_pos] at hb
  have hd : 0 < ‖deriv (halfPlaneFunction f) z‖ :=
    norm_pos_iff.mpr (halfPlaneFunction_deriv_ne_zero f z.im_pos)
  have hm := (div_le_iff₀ (mul_pos z.im_pos hd)).mp hb
  have hq := mul_le_mul_of_nonneg_left (omitted_derivative_bound f hξ z) hM0
  have ht := norm_add_le (halfPlaneFunction f ((u : ℂ)+(h : ℂ)*I)-halfPlaneFunction f z)
    (halfPlaneFunction f z-ξ)
  rw [sub_add_sub_cancel] at ht
  nlinarith

lemma omitted_cell_power_bound {M k δ : ℝ} (hM : ∀ (f : DiskFamily) (z : UpperHalfPlane),
    z ∈ cellRectangle → ‖halfPlaneFunction f z‖ ≤ M) (hM0 : 0 ≤ M)
    (hk : 0 ≤ k) (hδ : 0 < δ) (f : DiskFamily) {ξ : ℂ}
    (hξ : ξ ∉ halfPlaneFunction f '' {z : ℂ | 0 < z.im})
    (z : UpperHalfPlane) {h u : ℝ} (hh : 0 < h)
    (hlo : h ≤ z.im) (hhi : z.im ≤ 2*h) (hu : |u-z.re| ≤ h)
    (hw : ‖halfPlaneFunction f z-ξ‖ ≤ z.im^k/δ) :
    ‖halfPlaneFunction f ((u : ℂ)+(h : ℂ)*I)-ξ‖ ≤
      ((4*M+1)*2^k/δ)*h^k := by
  calc
    _ ≤ (4*M+1)*‖halfPlaneFunction f z-ξ‖ := omitted_cell_comparison hM hM0 f hξ z hh hlo hhi hu
    _ ≤ (4*M+1)*(z.im^k/δ) := mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ (4*M+1)*((2*h)^k/δ) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (Real.rpow_le_rpow z.im_pos.le hhi hk) hδ.le) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hh.le]; ring

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def boundaryWitness (f : DiskFamily) (k R δ h : ℝ) (ξ : ℂ) (z : UpperHalfPlane) : Prop :=
  ξ ∉ halfPlaneFunction f '' {w : ℂ | 0 < w.im} ∧ ‖ξ‖ ≤ R ∧
  h ≤ z.im ∧ z.im ≤ 2*h ∧ ‖halfPlaneFunction f z-ξ‖ ≤ z.im^k/δ

def boundaryBadScale (f : DiskFamily) (k R δ h : ℝ) : Set ℂ :=
  {ξ | ∃ z, boundaryWitness f k R δ h ξ z}

def boundaryMarkedCells (f : DiskFamily) (k R δ h : ℝ) : Set ℤ :=
  {j | ∃ ξ z, boundaryWitness f k R δ h ξ z ∧ z.re ∈ Ico ((j:ℝ)*h) (((j:ℝ)+1)*h)}

def cellMidpointImage (f : DiskFamily) (h : ℝ) (j : ℤ) : ℂ :=
  halfPlaneFunction f ((((j:ℝ)+1/2)*h : ℝ) + (h:ℂ)*I)

lemma same_cell_difference {j : ℤ} {h u v : ℝ}
    (hu : u ∈ Ico ((j:ℝ)*h) (((j:ℝ)+1)*h))
    (hv : v ∈ Ico ((j:ℝ)*h) (((j:ℝ)+1)*h)) : |u-v| ≤ h := by
  apply abs_le.mpr
  constructor <;> nlinarith [hu.1, hu.2, hv.1, hv.2]

lemma midpoint_mem_cell {h : ℝ} (hh : 0 < h) (j : ℤ) :
    ((j:ℝ)+1/2)*h ∈ Ico ((j:ℝ)*h) (((j:ℝ)+1)*h) := by
  constructor <;> nlinarith

lemma floor_cell_mem {h : ℝ} (hh : 0 < h) (x : ℝ) :
    x ∈ Ico (((⌊x/h⌋ : ℤ):ℝ)*h) ((((⌊x/h⌋ : ℤ):ℝ)+1)*h) := by
  constructor
  · exact (le_div_iff₀ hh).mp (Int.floor_le (x/h))
  · exact (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (x/h))

lemma boundaryBadScale_subset_cover {M k R δ h : ℝ}
    (hM : ∀ (f : DiskFamily) (z : UpperHalfPlane), z ∈ cellRectangle → ‖halfPlaneFunction f z‖ ≤ M)
    (hM0 : 0 ≤ M) (hk : 0 ≤ k) (hδ : 0 < δ) (hh : 0 < h) (f : DiskFamily) :
    boundaryBadScale f k R δ h ⊆ ⋃ j : boundaryMarkedCells f k R δ h,
      closedBall (cellMidpointImage f h j) (((4*M+1)*2^k/δ)*h^k) := by
  rintro ξ ⟨z, hz⟩
  let j : ℤ := ⌊z.re/h⌋
  have hj : j ∈ boundaryMarkedCells f k R δ h := ⟨ξ,z,hz,floor_cell_mem hh z.re⟩
  apply mem_iUnion.mpr
  refine ⟨⟨j,hj⟩, ?_⟩
  rw [mem_closedBall, dist_comm, dist_eq_norm]
  exact omitted_cell_power_bound hM hM0 hk hδ f hz.1 z hh hz.2.2.1 hz.2.2.2.1
    (same_cell_difference (midpoint_mem_cell hh j) (floor_cell_mem hh z.re)) hz.2.2.2.2

lemma marked_segments_image_bounded {M k R δ h : ℝ}
    (hM : ∀ (f : DiskFamily) (z : UpperHalfPlane), z ∈ cellRectangle → ‖halfPlaneFunction f z‖ ≤ M)
    (hM0 : 0 ≤ M) (hk : 0 ≤ k) (hδ : 0 < δ) (hh : 0 < h) (hh1 : h ≤ 1) (f : DiskFamily) :
    (⋃ j : boundaryMarkedCells f k R δ h,
      Ico (((j:ℤ):ℝ)*h) ((((j:ℤ):ℝ)+1)*h)) ⊆
      {u : ℝ | halfPlaneFunction f ((u:ℂ)+(h:ℂ)*I) ∈ closedBall 0 (R+(4*M+1)*2^k/δ)} := by
  rintro u hu
  obtain ⟨j,hj⟩ := mem_iUnion.mp hu
  obtain ⟨ξ,z,hz,hzcell⟩ := j.property
  have hb := omitted_cell_power_bound hM hM0 hk hδ f hz.1 z hh hz.2.2.1 hz.2.2.2.1
    (same_cell_difference hj hzcell) hz.2.2.2.2
  have hp : h^k ≤ 1 := Real.rpow_le_one hh.le hh1 hk
  have hc : 0 ≤ (4*M+1)*2^k/δ := by positivity
  have ht := norm_add_le (halfPlaneFunction f ((u:ℂ)+(h:ℂ)*I)-ξ) ξ
  rw [sub_add_cancel] at ht
  simp only [mem_ofPred_eq, mem_closedBall, dist_zero_right]
  nlinarith [hz.2.1, mul_le_of_le_one_right hc hp]

lemma cell_area_power_identity {h : ℝ} (hh : 0 < h) (A k : ℝ) :
    Real.pi*(A*h^k)^2/h = (Real.pi*A^2)*h^(2*k-1) := by
  rw [Real.rpow_sub_one hh.ne', show 2*k = k*2 by ring,
    Real.rpow_mul hh.le, Real.rpow_two]
  ring

theorem boundaryBadScale_measure_bound (f : DiskFamily) (β k R δ : ℝ)
    (hβ : 0 ≤ β) (hk : 0 ≤ k) (hδ : 0 < δ) (hfin : weightedAreaTail β f < ⊤) :
    ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      volume (boundaryBadScale f k R δ h) ≤ D * ENNReal.ofReal (h^(2*k-1)) := by
  obtain ⟨M,hM0,hM⟩ := family_rectangle_bound
  let A : ℝ := (4*M+1)*2^k/δ
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨C,hC⟩ := horizontal_length_bound f β hβ hfin (isCompact_closedBall (0:ℂ) (R+A))
  refine ⟨ENNReal.ofReal (Real.pi*A^2)*ENNReal.ofReal C, ENNReal.mul_lt_top
    ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top, fun h hh hh1 => ?_⟩
  have hseg : volume (⋃ j : boundaryMarkedCells f k R δ h,
      Ico (((j:ℤ):ℝ)*h) ((((j:ℤ):ℝ)+1)*h)) ≤ ENNReal.ofReal C :=
    (measure_mono (marked_segments_image_bounded hM hM0.le hk hδ hh hh1 f)).trans (hC h hh)
  calc
    _ ≤ volume (⋃ j : boundaryMarkedCells f k R δ h,
        closedBall (cellMidpointImage f h j) (A*h^k)) :=
      measure_mono (boundaryBadScale_subset_cover hM hM0.le hk hδ hh f)
    _ ≤ ENNReal.ofReal (Real.pi*(A*h^k)^2/h)*ENNReal.ofReal C :=
      cell_disks_measure_bound hh (by positivity) _ _ hseg
    _ = _ := by rw [cell_area_power_identity hh, ENNReal.ofReal_mul (by positivity)]; ring

end
end StrictInverseFirstPower

end

end OAI
