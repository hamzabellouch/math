import OAI.Analysis.LipschitzHilbert.Geometry.FarLineLower

namespace OAI

/-! Local strips in the reference coordinates, and the coordinate bounds
needed to compare their overlap with a transverse line through a small
selected rectangle. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

def stripSlab (S : Rectangle) (c l : ℝ) : Set Plane :=
  S.orthogonalCoordinates ⁻¹'
    (Icc (c-l/2) (c+l/2) ×ˢ Icc (-S.short/2) (S.short/2))

theorem mem_stripSlab (S : Rectangle) (c l : ℝ) (x : Plane) :
    x ∈ S.stripSlab c l ↔
      |(S.orthogonalCoordinates x).1-c| ≤ l/2 ∧
      |(S.orthogonalCoordinates x).2| ≤ S.short/2 := by
  simp only [stripSlab,mem_preimage,mem_prod,mem_Icc,abs_le]
  constructor <;> rintro ⟨⟨h1,h2⟩,h3,h4⟩ <;> constructor <;> constructor <;> linarith

theorem isCompact_stripSlab (S : Rectangle) (c l : ℝ) : IsCompact (S.stripSlab c l) := by
  have he : S.stripSlab c l = S.orthogonalCoordinates.symm ''
      (Icc (c-l/2) (c+l/2) ×ˢ Icc (-S.short/2) (S.short/2)) := by
    ext x
    constructor
    · intro hx
      exact ⟨S.orthogonalCoordinates x,hx,S.orthogonalCoordinates.symm_apply_apply x⟩
    · rintro ⟨z,hz,rfl⟩
      simpa only [stripSlab,mem_preimage,S.orthogonalCoordinates.apply_symm_apply] using hz
  rw [he]
  apply (isCompact_Icc.prod isCompact_Icc).image
  change Continuous (fun z : ℝ × ℝ => S.axes.repr.symm (planeCoordinates z)+S.center)
  apply Continuous.add_const
  apply S.axes.repr.symm.continuous.comp
  change Continuous (fun z : ℝ × ℝ => WithLp.toLp 2 ![z.1,z.2])
  fun_prop

theorem volume_stripSlab (S : Rectangle) (c l : ℝ) :
    volume (S.stripSlab c l) = ENNReal.ofReal l*ENNReal.ofReal S.short := by
  rw [stripSlab,S.orthogonalCoordinates_measurePreserving.measure_preimage_equiv,
    Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
  congr 2 <;> ring

theorem transverse_coordinate_change_bound (R S : Rectangle) (z : Plane) :
    |R.axes.repr z 1| ≤ dist (S.axes 0) (R.axes 0)*|S.axes.repr z 0|+|S.axes.repr z 1| := by
  have h0 := R.abs_coordinate_le_norm (S.axes 0-R.axes 0) 1
  have hz : R.axes.repr (R.axes 0) 1 = 0 := by simp
  rw [map_sub,PiLp.sub_apply,hz,sub_zero] at h0
  change |R.axes.repr (S.axes 0) 1| ≤ dist (S.axes 0) (R.axes 0) at h0
  have h1 : |R.axes.repr (S.axes 1) 1| ≤ 1 :=
    (R.abs_coordinate_le_norm (S.axes 1) 1).trans_eq (S.axes.norm_eq_one 1)
  have he := S.axes.sum_repr z
  rw [Fin.sum_univ_two] at he
  nth_rw 1 [←he]
  rw [map_add,PiLp.add_apply,map_smul,map_smul]
  change |S.axes.repr z 0*R.axes.repr (S.axes 0) 1+
    S.axes.repr z 1*R.axes.repr (S.axes 1) 1| ≤ _
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul,abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left h0 (abs_nonneg (S.axes.repr z 0)),
    mul_le_mul_of_nonneg_left h1 (abs_nonneg (S.axes.repr z 1))]

/-- Coordinate bounds at every point of a short rectangle meeting the
fourfold reference interval. The long rectangle meets the original interval. -/
theorem short_to_long_slab_coordinates (S R T : Rectangle) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : 8*l ≤ R.long) (hTlong : T.long ≤ l)
    (hSshort : S.short ≤ θ*l) (hTshort : T.short ≤ θ*l)
    (hRangle : dist (S.axes 0) (R.axes 0) ≤ 2*θ)
    (hTangle : dist (S.axes 0) (T.axes 0) ≤ 2*θ)
    (hR : (R.carrier ∩ S.stripSlab c l).Nonempty)
    (hT : (T.carrier ∩ S.stripSlab c (4*l)).Nonempty)
    {x : Plane} (hx : x ∈ T.carrier) :
    |R.axes.repr (x-R.center) 0| ≤ 32*R.long ∧
      |R.axes.repr (x-R.center) 1| ≤ R.short/2+8*(2*θ*l) := by
  obtain ⟨y,hyR,hy⟩ := hR
  obtain ⟨z,hzT,hz⟩ := hT
  have hy' := (S.mem_stripSlab c l y).mp hy
  have hz' := (S.mem_stripSlab c (4*l) z).mp hz
  have hxz : |(S.orthogonalCoordinates x).1-(S.orthogonalCoordinates z).1| ≤ 2*T.long := by
    change |S.axes.repr (x-S.center) 0-S.axes.repr (z-S.center) 0| ≤ 2*T.long
    rw [coordinate_difference]
    exact (S.abs_coordinate_le_norm (x-z) 0).trans
      (by simpa only [dist_eq_norm] using T.dist_le_two_long hx hzT)
  have hxy0 : |S.axes.repr (x-y) 0| ≤ 9*l/2 := by
    rw [←coordinate_difference]
    change |(S.orthogonalCoordinates x).1-(S.orthogonalCoordinates y).1| ≤ 9*l/2
    have ht1 := abs_sub_le (S.orthogonalCoordinates x).1 (S.orthogonalCoordinates z).1 c
    have ht2 := abs_sub_le (S.orthogonalCoordinates x).1 c (S.orthogonalCoordinates y).1
    rw [abs_sub_comm c] at ht2
    linarith [hy'.1,hz'.1]
  have hxz1 := S.transverse_difference_le T hx hzT
  have hxy1 : |S.axes.repr (x-y) 1| ≤ 4*θ*l := by
    have ht1 := abs_sub_le (S.orthogonalCoordinates x).2 (S.orthogonalCoordinates z).2
      (S.orthogonalCoordinates y).2
    have ht2 := abs_sub (S.orthogonalCoordinates z).2 (S.orthogonalCoordinates y).2
    rw [←coordinate_difference] at hxz1 ⊢
    change |(S.orthogonalCoordinates x).2-(S.orthogonalCoordinates y).2| ≤ _
    change |(S.orthogonalCoordinates x).2-(S.orthogonalCoordinates z).2| ≤ _ at hxz1
    have hp := mul_le_mul_of_nonneg_left hTangle T.long_pos.le
    have hp' := mul_le_mul_of_nonneg_left hTlong hθ.le
    nlinarith [hy'.2,hz'.2]
  have hnorm : ‖x-y‖ ≤ 9*l/2+4*θ*l :=
    (S.norm_le_coordinate_sum (x-y)).trans (add_le_add hxy0 hxy1)
  have hr0 := R.abs_coordinate_le_norm (x-y) 0
  have hr1 := R.transverse_coordinate_change_bound S (x-y)
  have hprod := mul_le_mul hRangle hxy0 (abs_nonneg _) (by positivity : 0 ≤ 2*θ)
  have hxsub : x-R.center = (x-y)+(y-R.center) := by abel
  constructor
  · rw [hxsub,map_add,PiLp.add_apply]
    refine (abs_add_le _ _).trans ?_
    have hp := mul_le_mul_of_nonneg_right hθsmall hl.le
    nlinarith [hyR.1]
  · rw [hxsub,map_add,PiLp.add_apply]
    refine (abs_add_le _ _).trans ?_
    nlinarith [hyR.2]

/-- Comparable lengths permit the same transverse line argument with a
larger line radius. -/
theorem comparable_slab_coordinates (S R T : Rectangle) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : l ≤ R.long) (hTlong : T.long ≤ 16*l)
    (hSshort : S.short ≤ θ*l) (hTshort : T.short ≤ θ*l)
    (hRangle : dist (S.axes 0) (R.axes 0) ≤ 2*θ)
    (hTangle : dist (S.axes 0) (T.axes 0) ≤ 2*θ)
    (hR : (R.carrier ∩ S.stripSlab c l).Nonempty)
    (hT : (T.carrier ∩ S.stripSlab c (4*l)).Nonempty)
    {x : Plane} (hx : x ∈ T.carrier) :
    |R.axes.repr (x-R.center) 0| ≤ 64*R.long ∧
      |R.axes.repr (x-R.center) 1| ≤ R.short/2+8*(16*θ*l) := by
  obtain ⟨y,hyR,hy⟩ := hR
  obtain ⟨z,hzT,hz⟩ := hT
  have hy' := (S.mem_stripSlab c l y).mp hy
  have hz' := (S.mem_stripSlab c (4*l) z).mp hz
  have hxz : |(S.orthogonalCoordinates x).1-(S.orthogonalCoordinates z).1| ≤ 2*T.long := by
    change |S.axes.repr (x-S.center) 0-S.axes.repr (z-S.center) 0| ≤ 2*T.long
    rw [coordinate_difference]
    exact (S.abs_coordinate_le_norm (x-z) 0).trans
      (by simpa only [dist_eq_norm] using T.dist_le_two_long hx hzT)
  have hxy0 : |S.axes.repr (x-y) 0| ≤ 35*l := by
    rw [←coordinate_difference]
    change |(S.orthogonalCoordinates x).1-(S.orthogonalCoordinates y).1| ≤ 35*l
    have ht1 := abs_sub_le (S.orthogonalCoordinates x).1 (S.orthogonalCoordinates z).1 c
    have ht2 := abs_sub_le (S.orthogonalCoordinates x).1 c (S.orthogonalCoordinates y).1
    rw [abs_sub_comm c] at ht2
    linarith [hy'.1,hz'.1]
  have hxz1 := S.transverse_difference_le T hx hzT
  have hxy1 : |S.axes.repr (x-y) 1| ≤ 34*θ*l := by
    have ht1 := abs_sub_le (S.orthogonalCoordinates x).2 (S.orthogonalCoordinates z).2
      (S.orthogonalCoordinates y).2
    have ht2 := abs_sub (S.orthogonalCoordinates z).2 (S.orthogonalCoordinates y).2
    rw [←coordinate_difference] at hxz1 ⊢
    change |(S.orthogonalCoordinates x).2-(S.orthogonalCoordinates y).2| ≤ _
    change |(S.orthogonalCoordinates x).2-(S.orthogonalCoordinates z).2| ≤ _ at hxz1
    have hp := mul_le_mul_of_nonneg_left hTangle T.long_pos.le
    have hp' := mul_le_mul_of_nonneg_left hTlong hθ.le
    nlinarith [hy'.2,hz'.2]
  have hnorm : ‖x-y‖ ≤ 35*l+34*θ*l :=
    (S.norm_le_coordinate_sum (x-y)).trans (add_le_add hxy0 hxy1)
  have hr0 := R.abs_coordinate_le_norm (x-y) 0
  have hr1 := R.transverse_coordinate_change_bound S (x-y)
  have hprod := mul_le_mul hRangle hxy0 (abs_nonneg _) (by positivity : 0 ≤ 2*θ)
  have hxsub : x-R.center = (x-y)+(y-R.center) := by abel
  constructor
  · rw [hxsub,map_add,PiLp.add_apply]
    refine (abs_add_le _ _).trans ?_
    have hp := mul_le_mul_of_nonneg_right hθsmall hl.le
    nlinarith [hyR.1]
  · rw [hxsub,map_add,PiLp.add_apply]
    refine (abs_add_le _ _).trans ?_
    nlinarith [hyR.2]

end LipschitzHilbert.Rectangle

end

end OAI
