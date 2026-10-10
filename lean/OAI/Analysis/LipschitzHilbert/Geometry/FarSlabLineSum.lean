import OAI.Analysis.LipschitzHilbert.Geometry.FarSlabGeometry

namespace OAI

/-! The long-rectangle contribution over a local reference strip is
bounded by the actual line part of the auxiliary maximal operator. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
namespace Rectangle

theorem slab_intersection_transverse (R S : Rectangle) (c l : ℝ)
    (ha : R.axes.repr (S.axes 0) 1 ≠ 0) :
    volume (R.carrier ∩ S.stripSlab c l) ≤
      ENNReal.ofReal (R.short / |R.axes.repr (S.axes 0) 1|)*ENNReal.ofReal S.short := by
  let E := S.orthogonalCoordinates '' (R.carrier ∩ S.stripSlab c l)
  have hE : IsCompact E := (R.isCompact_carrier.inter (S.isCompact_stripSlab c l)).image
    S.continuous_orthogonalCoordinates
  have h := strip_projection_area_swap E hE.measurableSet
    (Icc (-S.short/2) (S.short/2)) measurableSet_Icc
    (R.axes.repr (S.axes 0) 1) (R.axes.repr (S.axes 1) 1)
    (-R.axes.repr (S.center-R.center) 1) (R.short/2) ha (half_pos R.short_pos).le
    (fun z hz => by
      obtain ⟨x,hx,rfl⟩ := hz
      exact (mem_prod.mp hx.2).2)
    (fun z hz => by
      obtain ⟨x,hx,rfl⟩ := hz
      have hh := hx.1.2
      rw [change_transverse_coordinates R S x] at hh
      simpa only [sub_neg_eq_add] using hh)
  have he : (volume.prod volume) E = volume (R.carrier ∩ S.stripSlab c l) := by
    have he := S.orthogonalCoordinates_measurePreserving.measure_preimage_equiv E
    rw [Set.preimage_image_eq _ S.orthogonalCoordinates.injective] at he
    exact he.symm
  rw [he,Real.volume_Icc,show S.short/2- -S.short/2=S.short by ring,
    show 2*(R.short/2)=R.short by ring] at h
  exact h

theorem slab_intersection_min_area (R S : Rectangle) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ)
    (hangle : dist (R.axes 0) (S.axes 0) ≤ 1)
    (hlower : θ/2 ≤ dist (R.axes 0) (S.axes 0)) :
    volume (R.carrier ∩ S.stripSlab c l) ≤
      ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short*ENNReal.ofReal (min R.short (2*θ*l)) := by
  have hc := R.transverse_coordinate_comparable S hangle
  have hb : θ/4 ≤ |R.axes.repr (S.axes 0) 1| := by linarith
  have hbpos : 0 < |R.axes.repr (S.axes 0) 1| := lt_of_lt_of_le (by positivity) hb
  by_cases hw : R.short ≤ 2*θ*l
  · rw [min_eq_left hw]
    have hreal : R.short/|R.axes.repr (S.axes 0) 1| ≤ (4/θ)*R.short := by
      apply (div_le_iff₀ hbpos).mpr
      have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4/θ by positivity)
      have he : (4/θ)*(θ/4)=1 := by field_simp
      rw [he] at hh
      have hh' := mul_le_mul_of_nonneg_left hh R.short_pos.le
      nlinarith
    calc
      _ ≤ ENNReal.ofReal (R.short/|R.axes.repr (S.axes 0) 1|)*ENNReal.ofReal S.short :=
        R.slab_intersection_transverse S c l (abs_pos.mp hbpos)
      _ ≤ ENNReal.ofReal ((4/θ)*R.short)*ENNReal.ofReal S.short :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]; ring
  · rw [min_eq_right (le_of_not_ge hw)]
    calc
      _ ≤ volume (S.stripSlab c l) := measure_mono inter_subset_right
      _ = ENNReal.ofReal l*ENNReal.ofReal S.short := S.volume_stripSlab c l
      _ ≤ ENNReal.ofReal (8*l)*ENNReal.ofReal S.short :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
      _ = _ := by
        have he : (8*l)*S.short=(4/θ)*S.short*(2*θ*l) := by field_simp; ring
        calc
          _ = ENNReal.ofReal ((8*l)*S.short) := (ENNReal.ofReal_mul (by positivity)).symm
          _ = ENNReal.ofReal ((4/θ)*S.short*(2*θ*l)) := congrArg ENNReal.ofReal he
          _ = _ := by
            rw [ENNReal.ofReal_mul (mul_nonneg (div_nonneg (by norm_num) hθ.le) S.short_pos.le),
              ENNReal.ofReal_mul (div_nonneg (by norm_num) hθ.le)]


end Rectangle

variable {ι κ : Type*} [Fintype κ]

theorem far_slab_line_sum (D : κ → Rectangle) (R : ι → Rectangle)
    (s : Finset ι) (S T : Rectangle) (i : κ) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : ∀ j ∈ s, 8*l ≤ (R j).long) (hTlong : T.long ≤ l)
    (hSshort : S.short ≤ θ*l) (hTshort : T.short ≤ θ*l)
    (hRangle : ∀ j ∈ s, dist (S.axes 0) ((R j).axes 0) ≤ 2*θ)
    (hRlower : ∀ j ∈ s, θ/2 ≤ dist (S.axes 0) ((R j).axes 0))
    (hTangle : dist (S.axes 0) (T.axes 0) ≤ 2*θ)
    (hR : ∀ j ∈ s, ((R j).carrier ∩ S.stripSlab c l).Nonempty)
    (hT : (T.carrier ∩ S.stripSlab c (4*l)).Nonempty)
    (htrans : ∀ j ∈ s, 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1|)
    (x : Plane) (hx : x ∈ T.carrier) :
    (∑ j ∈ s, volume ((R j).carrier ∩ S.stripSlab c l)) ≤
      ENNReal.ofReal 6144*volume (S.stripSlab c l)*
        positiveAuxiliary (fun i => (D i).orthogonalCoordinates)
          (rectangleCount (fun j => (R j).dilate 265 (by norm_num)) s) x := by
  let q := 2*θ*l
  have hq : 0 < q := by dsimp [q]; positivity
  let g := rectangleCount (fun j => (R j).dilate 265 (by norm_num)) s
  let e := (D i).orthogonalCoordinates
  let a := (e x).1
  let b := (e x).2
  let I := Icc (a-64*q) (a+64*q)
  let P := fun u : ℝ => e.symm (u,b)
  have hP : Measurable P := e.symm.measurable.comp (measurable_id.prodMk measurable_const)
  have hsum : (∫⁻ u in I, g (P u)) = ∑ j ∈ s,
      ∫⁻ u in I, ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := by
    apply lintegral_finsetSum
    intro j _
    exact (measurable_const.indicator ((R j).dilate 265 (by norm_num)).measurableSet_carrier).comp hP
  have hterm (j : ι) (hj : j ∈ s) :
      volume ((R j).carrier ∩ S.stripSlab c l) ≤
      (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*∫⁻ u in I,
        ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := by
    have hcoord := S.short_to_long_slab_coordinates (R j) T c l θ hl hθ hθsmall
      (hRlong j hj) hTlong hSshort hTshort (hRangle j hj) hTangle (hR j hj) hT hx
    have hqL : q ≤ (R j).long := by
      have hh := mul_le_mul_of_nonneg_right hθsmall hl.le
      dsimp [q]
      linarith [hRlong j hj]
    have hline := (R j).far_line_lower x ((D i).axes 0) q hq hqL
      (by rw [(D i).axes.norm_eq_one]) (htrans j hj)
      (by linarith [hcoord.1,(R j).long_pos]) hcoord.2
    have hchange := Rectangle.line_integral_change_origin (D i)
      (f := ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)))
      (measurable_const.indicator ((R j).dilate 265 (by norm_num)).measurableSet_carrier) x (64*q)
    simp only [neg_mul] at hline
    rw [hchange] at hline
    have hangle : dist ((R j).axes 0) (S.axes 0) ≤ 1 := by
      rw [dist_comm]
      linarith [hRangle j hj]
    have hlower : θ/2 ≤ dist ((R j).axes 0) (S.axes 0) := by simpa only [dist_comm] using hRlower j hj
    exact ((R j).slab_intersection_min_area S c l θ hl hθ hangle hlower).trans
      (mul_le_mul' le_rfl hline)
  have haux := positiveAuxiliary_line_integral (fun j => (D j).orthogonalCoordinates)
    g i a (64*q) (by positivity) x (by constructor <;> dsimp [a] <;> linarith)
  have he : (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*
      (6*ENNReal.ofReal (2*(64*q))) = ENNReal.ofReal 6144*volume (S.stripSlab c l) := by
    rw [S.volume_stripSlab]
    have hreal : (4/θ)*(6*(2*(64*q)))=6144*l := by dsimp [q]; field_simp; ring
    calc
      _ = ENNReal.ofReal ((4/θ)*(6*(2*(64*q))))*ENNReal.ofReal S.short := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4/θ),ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 6)]
        norm_num
        ring
      _ = _ := by rw [hreal,ENNReal.ofReal_mul (by norm_num)]; ring
  calc
    _ ≤ ∑ j ∈ s, (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*∫⁻ u in I,
        ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) :=
      Finset.sum_le_sum hterm
    _ = (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*∫⁻ u in I, g (P u) := by
      rw [hsum,Finset.mul_sum]
    _ ≤ (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*
        (6*ENNReal.ofReal (2*(64*q))*positiveAuxiliary (fun j => (D j).orthogonalCoordinates) g x) :=
      mul_le_mul' le_rfl haux
    _ = _ := by rw [←mul_assoc,he]

/-- The comparable-length version uses the same fixed direction net. -/
theorem comparable_slab_line_sum (D : κ → Rectangle) (R : ι → Rectangle)
    (s : Finset ι) (S T : Rectangle) (i : κ) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : ∀ j ∈ s, l ≤ (R j).long) (hTlong : T.long ≤ 16*l)
    (hSshort : S.short ≤ θ*l) (hTshort : T.short ≤ θ*l)
    (hRangle : ∀ j ∈ s, dist (S.axes 0) ((R j).axes 0) ≤ 2*θ)
    (hRlower : ∀ j ∈ s, θ/2 ≤ dist (S.axes 0) ((R j).axes 0))
    (hTangle : dist (S.axes 0) (T.axes 0) ≤ 2*θ)
    (hR : ∀ j ∈ s, ((R j).carrier ∩ S.stripSlab c l).Nonempty)
    (hT : (T.carrier ∩ S.stripSlab c (4*l)).Nonempty)
    (htrans : ∀ j ∈ s, 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1|)
    (x : Plane) (hx : x ∈ T.carrier) :
    (∑ j ∈ s, volume ((R j).carrier ∩ S.stripSlab c l)) ≤
      ENNReal.ofReal 49152*volume (S.stripSlab c l)*
        positiveAuxiliary (fun i => (D i).orthogonalCoordinates)
          (rectangleCount (fun j => (R j).dilate 265 (by norm_num)) s) x := by
  let q := 16*θ*l
  have hq : 0 < q := by dsimp [q]; positivity
  let g := rectangleCount (fun j => (R j).dilate 265 (by norm_num)) s
  let e := (D i).orthogonalCoordinates
  let a := (e x).1
  let b := (e x).2
  let I := Icc (a-64*q) (a+64*q)
  let P := fun u : ℝ => e.symm (u,b)
  have hP : Measurable P := e.symm.measurable.comp (measurable_id.prodMk measurable_const)
  have hsum : (∫⁻ u in I, g (P u)) = ∑ j ∈ s,
      ∫⁻ u in I, ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := by
    apply lintegral_finsetSum
    intro j _
    exact (measurable_const.indicator ((R j).dilate 265 (by norm_num)).measurableSet_carrier).comp hP
  have hterm (j : ι) (hj : j ∈ s) :
      volume ((R j).carrier ∩ S.stripSlab c l) ≤
      (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*∫⁻ u in I,
        ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := by
    have hcoord := S.comparable_slab_coordinates (R j) T c l θ hl hθ hθsmall
      (hRlong j hj) hTlong hSshort hTshort (hRangle j hj) hTangle (hR j hj) hT hx
    have hqL : q ≤ (R j).long := by
      have hh := mul_le_mul_of_nonneg_right hθsmall hl.le
      dsimp [q]
      linarith [hRlong j hj]
    have hline := (R j).far_line_lower x ((D i).axes 0) q hq hqL
      (by rw [(D i).axes.norm_eq_one]) (htrans j hj)
      hcoord.1 hcoord.2
    have hchange := Rectangle.line_integral_change_origin (D i)
      (f := ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)))
      (measurable_const.indicator ((R j).dilate 265 (by norm_num)).measurableSet_carrier) x (64*q)
    simp only [neg_mul] at hline
    rw [hchange] at hline
    have hangle : dist ((R j).axes 0) (S.axes 0) ≤ 1 := by
      rw [dist_comm]
      linarith [hRangle j hj]
    have hlower : θ/2 ≤ dist ((R j).axes 0) (S.axes 0) := by simpa only [dist_comm] using hRlower j hj
    have hmin : ENNReal.ofReal (min (R j).short (2*θ*l)) ≤
        ENNReal.ofReal (min (R j).short q) := by
      apply ENNReal.ofReal_le_ofReal
      apply min_le_min_left
      dsimp [q]
      nlinarith [mul_pos hθ hl]
    exact ((R j).slab_intersection_min_area S c l θ hl hθ hangle hlower).trans
      (mul_le_mul' le_rfl (hmin.trans hline))
  have haux := positiveAuxiliary_line_integral (fun j => (D j).orthogonalCoordinates)
    g i a (64*q) (by positivity) x (by constructor <;> dsimp [a] <;> linarith)
  have he : (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*
      (6*ENNReal.ofReal (2*(64*q))) = ENNReal.ofReal 49152*volume (S.stripSlab c l) := by
    rw [S.volume_stripSlab]
    have hreal : (4/θ)*(6*(2*(64*q)))=49152*l := by dsimp [q]; field_simp; ring
    calc
      _ = ENNReal.ofReal ((4/θ)*(6*(2*(64*q))))*ENNReal.ofReal S.short := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4/θ),ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 6)]
        norm_num
        ring
      _ = _ := by rw [hreal,ENNReal.ofReal_mul (by norm_num)]; ring
  calc
    _ ≤ ∑ j ∈ s, (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*∫⁻ u in I,
        ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) :=
      Finset.sum_le_sum hterm
    _ = (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*∫⁻ u in I, g (P u) := by
      rw [hsum,Finset.mul_sum]
    _ ≤ (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*
        (6*ENNReal.ofReal (2*(64*q))*positiveAuxiliary (fun j => (D j).orthogonalCoordinates) g x) :=
      mul_le_mul' le_rfl haux
    _ = _ := by rw [←mul_assoc,he]

end LipschitzHilbert

end

end OAI
