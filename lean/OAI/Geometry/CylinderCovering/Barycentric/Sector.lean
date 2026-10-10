import OAI.Geometry.CylinderCovering.Barycentric.SectorDefinitions
import OAI.Geometry.CylinderCovering.Radial.Coordinates
import OAI.Geometry.CylinderCovering.Radial.SectorEuclidean

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace RadialCoordinates.BarycentricSector

theorem ray_sum (t : ℝ) : ray t 0 + ray t 1 = 1 := by
  simp [ray]

theorem mem_positiveSector_iff {l r A : ℝ} (hlr : l ≤ r) {z : Plane} :
    z ∈ positiveSector l r A ↔
      0 ≤ z 0 + z 1 ∧ z 0 + z 1 ≤ A ∧
        l * (z 0 + z 1) ≤ z 0 ∧ z 0 ≤ r * (z 0 + z 1) := by
  constructor
  · rintro ⟨t, ht, ρ, hρ, rfl⟩
    simp only [ray, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have hsum : ρ * t + ρ * (1-t) = ρ := by ring
    rw [hsum]
    exact ⟨hρ.1, hρ.2, by nlinarith [mul_le_mul_of_nonneg_right ht.1 hρ.1],
      by nlinarith [mul_le_mul_of_nonneg_right ht.2 hρ.1]⟩
  · rintro ⟨hs0, hsA, hl, hr⟩
    by_cases hs : z 0 + z 1 = 0
    · have hz0 : z 0 = 0 := by rw [hs] at hl hr; nlinarith
      have hz1 : z 1 = 0 := by linarith
      refine ⟨l, ⟨le_rfl, hlr⟩, 0, ⟨le_rfl, by linarith⟩, ?_⟩
      ext i
      fin_cases i <;> simp [hz0, hz1]
    · have hspos : 0 < z 0 + z 1 := lt_of_le_of_ne hs0 (Ne.symm hs)
      refine ⟨z 0 / (z 0 + z 1),
        ⟨(le_div_iff₀ hspos).2 hl, (div_le_iff₀ hspos).2 hr⟩,
        z 0 + z 1, ⟨hs0, hsA⟩, ?_⟩
      ext i
      fin_cases i <;> simp [ray] <;> field_simp
      ring

theorem positiveSector_convex {l r A : ℝ} (hlr : l ≤ r) :
    Convex ℝ (positiveSector l r A) := by
  intro x hx y hy a b ha hb hab
  rw [mem_positiveSector_iff hlr] at hx hy ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rcases hx with ⟨hx0, hxA, hxl, hxr⟩
  rcases hy with ⟨hy0, hyA, hyl, hyr⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg ha hx0, mul_nonneg hb hy0]
  · nlinarith [mul_le_mul_of_nonneg_left hxA ha, mul_le_mul_of_nonneg_left hyA hb]
  · nlinarith [mul_le_mul_of_nonneg_left hxl ha, mul_le_mul_of_nonneg_left hyl hb]
  · nlinarith [mul_le_mul_of_nonneg_left hxr ha, mul_le_mul_of_nonneg_left hyr hb]

theorem positiveSector_eq_convexHull {l r A : ℝ} (hlr : l ≤ r) (hA : 0 ≤ A) :
    positiveSector l r A = convexHull ℝ (range (vertices l r A)) := by
  apply Subset.antisymm
  · rintro z ⟨t, ht, ρ, hρ, rfl⟩
    have hzero : (0 : Plane) ∈ convexHull ℝ (range (vertices l r A)) :=
      subset_convexHull ℝ _ ⟨0, rfl⟩
    have hleft : A • ray l ∈ convexHull ℝ (range (vertices l r A)) :=
      subset_convexHull ℝ _ ⟨1, rfl⟩
    have hright : A • ray r ∈ convexHull ℝ (range (vertices l r A)) :=
      subset_convexHull ℝ _ ⟨2, rfl⟩
    obtain ⟨a, b, ha, hb, hab, ht'⟩ := (Convex.mem_Icc hlr).mp ht
    have htip : A • ray t ∈ convexHull ℝ (range (vertices l r A)) := by
      have h := (convex_convexHull ℝ _) hleft hright ha hb hab
      convert h using 1
      ext i
      fin_cases i <;> simp [ray] <;> nlinarith [ht']
    obtain ⟨c, d, hc, hd, hcd, hρ'⟩ := (Convex.mem_Icc hA).mp hρ
    have h := (convex_convexHull ℝ _) hzero htip hc hd hcd
    have hρeq : d * A = ρ := by simpa using hρ'
    simpa only [smul_zero, zero_add, smul_smul, hρeq] using h
  · apply convexHull_min _ (positiveSector_convex hlr)
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact ⟨l, ⟨le_rfl, hlr⟩, 0, ⟨le_rfl, hA⟩, by simp [vertices]⟩
    · exact ⟨l, ⟨le_rfl, hlr⟩, A, ⟨hA, le_rfl⟩, rfl⟩
    · exact ⟨r, ⟨hlr, le_rfl⟩, A, ⟨hA, le_rfl⟩, rfl⟩

theorem isCompact_positiveSector {l r A : ℝ} (hlr : l ≤ r) (hA : 0 ≤ A) :
    IsCompact (positiveSector l r A) := by
  rw [positiveSector_eq_convexHull hlr hA]
  exact (finite_range (vertices l r A)).isCompact_convexHull ℝ

theorem signedSector_eq_union {l r a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    signedSector l r a b = positiveSector l r b ∪
      (fun z : Plane => -z) '' positiveSector l r a := by
  ext z
  constructor
  · rintro ⟨t, ht, ρ, hρ, rfl⟩
    by_cases hρ0 : 0 ≤ ρ
    · exact Or.inl ⟨t, ht, ρ, ⟨hρ0, hρ.2⟩, rfl⟩
    · right
      refine ⟨(-ρ) • ray t, ⟨t, ht, -ρ, ⟨by linarith, by linarith [hρ.1]⟩, rfl⟩, ?_⟩
      simp
  · rintro (⟨t, ht, ρ, hρ, rfl⟩ | ⟨z, ⟨t, ht, ρ, hρ, rfl⟩, rfl⟩)
    · exact ⟨t, ht, ρ, ⟨by linarith [hρ.1], hρ.2⟩, rfl⟩
    · exact ⟨t, ht, -ρ, ⟨by linarith [hρ.2], by linarith [hρ.1]⟩, by simp⟩

theorem signedSector_eq_two_triangles {l r a b : ℝ}
    (hlr : l ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    signedSector l r a b = convexHull ℝ (range (vertices l r b)) ∪
      (fun z : Plane => -z) '' convexHull ℝ (range (vertices l r a)) := by
  rw [signedSector_eq_union ha hb, positiveSector_eq_convexHull hlr ha,
    positiveSector_eq_convexHull hlr hb]

theorem isCompact_signedSector {l r a b : ℝ}
    (hlr : l ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsCompact (signedSector l r a b) := by
  rw [signedSector_eq_union ha hb]
  exact (isCompact_positiveSector hlr hb).union
    ((isCompact_positiveSector hlr ha).image continuous_neg)

theorem positive_negative_inter {l r a b : ℝ}
    (hlr : l ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    positiveSector l r b ∩ (fun z : Plane => -z) '' positiveSector l r a = {0} := by
  ext z
  constructor
  · rintro ⟨hp, w, hw, rfl⟩
    obtain ⟨hp0, _, hpl, hpr⟩ := (mem_positiveSector_iff hlr).mp hp
    obtain ⟨hw0, _, _, _⟩ := (mem_positiveSector_iff hlr).mp hw
    simp only [PiLp.neg_apply] at hp0 hpl hpr
    have hs : w 0 + w 1 = 0 := by linarith
    have hwzero : w 0 = 0 := by
      have hneg : -w 0 + -w 1 = 0 := by linarith
      rw [hneg] at hpl hpr
      nlinarith
    have hwone : w 1 = 0 := by linarith
    rw [mem_singleton_iff]
    ext i
    fin_cases i <;> simp [hwzero, hwone]
  · rintro rfl
    have hz (A : ℝ) (hA : 0 ≤ A) : (0 : Plane) ∈ positiveSector l r A :=
      ⟨l, ⟨le_rfl, hlr⟩, 0, ⟨le_rfl, hA⟩, by simp⟩
    exact ⟨hz b hb, 0, hz a ha, by simp⟩

private def coordinateShear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![1, 0; -1, 1]

private theorem coordinateShear_apply (p : ℝ × ℝ) :
    coordinateShear p = (p.1, p.2-p.1) := by
  simp [coordinateShear, Matrix.toLin_finTwoProd_apply]
  ring

private theorem coordinateShear_det : coordinateShear.det = 1 := by
  rw [coordinateShear, LinearMap.det_toLin, Matrix.det_fin_two]
  norm_num

private theorem positiveSector_eq_radial_image (l r A : ℝ) :
    positiveSector l r A = AngularCaps.pairToPlane ''
      (coordinateShear '' AngularCaps.radialSector l r (fun _ => A)) := by
  ext z
  constructor
  · rintro ⟨t, ht, ρ, hρ, rfl⟩
    refine ⟨coordinateShear (t*ρ, ρ),
      ⟨(t*ρ, ρ), ⟨(t,ρ), ⟨ht, hρ⟩, rfl⟩, rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [coordinateShear_apply, AngularCaps.pairToPlane, ray] <;> ring
  · rintro ⟨p, ⟨q, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
    refine ⟨v.1, hv.1, v.2, hv.2, ?_⟩
    ext i
    fin_cases i <;>
      simp [coordinateShear_apply, AngularCaps.radialMap, AngularCaps.pairToPlane, ray] <;> ring

theorem positiveSector_volume {l r A : ℝ} (hlr : l ≤ r) (hA : 0 ≤ A) :
    volume (positiveSector l r A) = ENNReal.ofReal ((r-l)*A^2/2) := by
  rw [positiveSector_eq_radial_image, AngularCaps.pairToPlane_volume,
    Measure.addHaar_image_linearMap, coordinateShear_det]
  simp only [abs_one, ENNReal.ofReal_one, one_mul]
  rw [AngularCaps.radialSector_volume hlr continuousOn_const (fun _ _ => hA)]
  congr 1
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem signedSector_volume {l r a b : ℝ}
    (hlr : l ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    volume (signedSector l r a b) = ENNReal.ofReal ((r-l)*(b^2+a^2)/2) := by
  rw [signedSector_eq_union ha hb]
  have hm := ((isCompact_positiveSector hlr ha).image continuous_neg).measurableSet
  have had : AEDisjoint volume (positiveSector l r b)
      ((fun z : Plane => -z) '' positiveSector l r a) := by
    change volume (_ ∩ _) = 0
    rw [positive_negative_inter hlr ha hb]
    simp
  rw [measure_union₀ hm.nullMeasurableSet had, Set.image_neg_eq_neg,
    Measure.measure_neg, positiveSector_volume hlr hb, positiveSector_volume hlr ha,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem signedSector_area {l r a b : ℝ}
    (hlr : l ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    volume.real (signedSector l r a b) = (r-l)*(b^2+a^2)/2 := by
  rw [measureReal_def, signedSector_volume hlr ha hb, ENNReal.toReal_ofReal]
  positivity

theorem vertices_affineIndependent {l r A : ℝ} (hlr : l < r) (hA : 0 < A) :
    AffineIndependent ℝ (vertices l r A) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  have h0 := congrArg (fun z : Plane => z 0) hv
  have h1 := congrArg (fun z : Plane => z 1) hv
  simp [vertices, ray, Fin.sum_univ_succ] at hw h0 h1
  have hsum : A * (w 1 + w 2) = 0 := by linear_combination h0 + h1
  have hw12 : w 1 + w 2 = 0 := (mul_eq_zero.mp hsum).resolve_left (ne_of_gt hA)
  have hdiff : A * (r-l) * w 2 = 0 := by linear_combination h0 - A*l*hw12
  have hw2 : w 2 = 0 := (mul_eq_zero.mp hdiff).resolve_left
    (mul_ne_zero (ne_of_gt hA) (ne_of_gt (sub_pos.mpr hlr)))
  fin_cases i
  · change w 0 = 0
    linarith
  · change w 1 = 0
    linarith
  · change w 2 = 0
    exact hw2

theorem ray_norm_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖ray t‖ ≤ 1 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [ray, Fin.sum_univ_succ]
  nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]

theorem ray_sub_norm (s t : ℝ) : ‖ray s - ray t‖ = Real.sqrt 2 * |s-t| := by
  have heq : ray s - ray t = (s-t) • (!₂[1,-1] : Plane) := by
    ext i
    fin_cases i <;> simp [ray]
  rw [heq, norm_smul, Real.norm_eq_abs, transverse_unit_norm]
  ring

theorem perimeter_eq {l r A : ℝ} (hlr : l ≤ r) (hA : 0 ≤ A) :
    perimeter l r A = A * (‖ray l‖ + ‖ray r‖ + Real.sqrt 2*(r-l)) := by
  simp only [perimeter, dist_eq_norm, zero_sub, sub_zero, norm_neg,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hA, ray_sub_norm,
    abs_of_nonpos (sub_nonpos.mpr hlr)]
  ring

theorem perimeter_le {l r A : ℝ} (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1)
    (hA : 0 ≤ A) : perimeter l r A ≤ (2 + Real.sqrt 2)*A := by
  rw [perimeter_eq hlr hA]
  have hlN := ray_norm_le_one (show l ∈ Icc (0:ℝ) 1 from ⟨hl, hlr.trans hr⟩)
  have hrN := ray_norm_le_one (show r ∈ Icc (0:ℝ) 1 from ⟨hl.trans hlr, hr⟩)
  have hwidth : r-l ≤ 1 := by linarith
  have hsqrt := mul_le_mul_of_nonneg_left hwidth (Real.sqrt_nonneg 2)
  have hsum : ‖ray l‖ + ‖ray r‖ + Real.sqrt 2*(r-l) ≤ 2 + Real.sqrt 2 := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsum hA]

theorem collar_sector_area {l r k M : ℝ} (hlr : l ≤ r) (hk : 0 ≤ k) (hM : 0 ≤ M) :
    volume.real (signedSector l r (2*k*(r-l)) (M+2*k*(r-l))) =
      (r-l)*M^2/2 + 2*k*M*(r-l)^2 + 4*k^2*(r-l)^3 := by
  rw [signedSector_area hlr (by positivity) (by positivity)]
  ring

theorem collar_sector_area_error {l r k M M₀ : ℝ}
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) (hk : 0 ≤ k)
    (hM : 0 ≤ M) (hMM : M ≤ M₀) :
    0 ≤ volume.real (signedSector l r (2*k*(r-l)) (M+2*k*(r-l))) - (r-l)*M^2/2 ∧
    volume.real (signedSector l r (2*k*(r-l)) (M+2*k*(r-l))) - (r-l)*M^2/2 ≤
      (2*k*M₀+4*k^2)*(r-l)^2 := by
  rw [collar_sector_area hlr hk hM]
  have hd0 : 0 ≤ r-l := sub_nonneg.mpr hlr
  have hd1 : r-l ≤ 1 := by linarith
  have hc : (r-l)^3 ≤ (r-l)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hd1 (sq_nonneg (r-l))]
  constructor
  · have hz : 0 ≤ 2*k*M*(r-l)^2 + 4*k^2*(r-l)^3 := by positivity
    linarith
  · nlinarith [mul_le_mul_of_nonneg_left hMM (by positivity : 0 ≤ 2*k*(r-l)^2),
      mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 4*k^2)]

theorem collar_perimeters_le {l r k M M₀ : ℝ}
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) (hk : 0 ≤ k)
    (hM : 0 ≤ M) (hMM : M ≤ M₀) :
    perimeter l r (2*k*(r-l)) + perimeter l r (M+2*k*(r-l)) ≤
      (2+Real.sqrt 2)*(M₀+4*k) := by
  have hd0 : 0 ≤ r-l := sub_nonneg.mpr hlr
  have hsum := add_le_add
    (perimeter_le hl hlr hr (show 0 ≤ 2*k*(r-l) by positivity))
    (perimeter_le hl hlr hr (show 0 ≤ M+2*k*(r-l) by positivity))
  have hsize : M+4*k*(r-l) ≤ M₀+4*k := by
    nlinarith [mul_le_mul_of_nonneg_left (show r-l ≤ 1 by linarith)
      (show 0 ≤ 4*k by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hsize
    (show 0 ≤ 2+Real.sqrt 2 by positivity)]

theorem frozen_intercept_mem_cthickening {l r c S k p t M : ℝ}
    (hk : 0 ≤ k) (hp : |p| ≤ 1) (hc : c ∈ Icc l r) (ht : t ∈ Icc l r)
    (hS : 0 ≤ S) (hSM : S ≤ M) :
    S • ray t + (k*p) • (velocity t-velocity c) ∈
      Metric.cthickening (Real.sqrt 2*k*(r-l)^2)
        (signedSector l r (2*k*(r-l)) (M+2*k*(r-l))) := by
  have hlr : l ≤ r := hc.1.trans hc.2
  have hdist : |t-c| ≤ r-l := (abs_le).2 ⟨by linarith [ht.1, hc.2],
    by linarith [ht.2, hc.1]⟩
  obtain ⟨ρ, hρ0, hρM, herror⟩ :=
    frozen_intercept_enclosure hk hp (sub_nonneg.mpr hlr) hdist hS hSM
  apply Metric.mem_cthickening_of_dist_le _ (ρ • ray t)
    (Real.sqrt 2*k*(r-l)^2) _
  · exact ⟨t, ht, ρ, ⟨by linarith, hρM⟩, rfl⟩
  · simpa only [dist_eq_norm] using herror

end RadialCoordinates.BarycentricSector

end

end OAI
