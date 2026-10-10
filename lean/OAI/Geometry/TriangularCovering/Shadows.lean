import OAI.Geometry.TriangularCovering.Tetrahedron

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma faceNormal_sum (u : Space) : ∑ i : Fin 4, inner ℝ (faceNormal i) u = 0 := by
  simp only [Fin.sum_univ_succ, inner_coord]
  dsimp [faceNormal]
  ring

lemma positive_face_exists {u : Space} (hu : ‖u‖ = 1) :
    ∃ i : Fin 4, 0 < inner ℝ (faceNormal i) u := by
  by_contra h
  push Not at h
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp only [inner_coord] at h0 h1 h2 h3
  dsimp [faceNormal] at h0 h1 h2 h3
  have hz : u 2 = 0 := by linarith only [h0,h1,h2,h3]
  have hx : u 0 = 0 := by nlinarith only [h0,h1,hz,H_pos]
  have hy : u 1 = 0 := by nlinarith only [h2,h3,hz,H_pos]
  have hun : u = 0 := by ext i; fin_cases i <;> assumption
  simp [hun] at hu

def front (u : Space) : Finset (Fin 4) := Finset.univ.filter (fun i => 0 < inner ℝ (faceNormal i) u)

@[simp] lemma mem_front (u : Space) (i : Fin 4) : i ∈ front u ↔ 0 < inner ℝ (faceNormal i) u := by
  simp [front]

lemma projection_add_axis {u : Space} (hu : ‖u‖ = 1) (z : Space) (r : ℝ) :
    projection u (z+r•u) = projection u z := by
  simp only [projection, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,hu]
  module

lemma forward_face {u : Space} (hu : ‖u‖ = 1) {z : Space} (hz : z ∈ K) :
    ∃ i ∈ front u, ∃ p ∈ face i, projection u p = projection u z := by
  classical
  have hfront : (front u).Nonempty := by
    obtain ⟨i,hi⟩ := positive_face_exists hu
    exact ⟨i,(mem_front u i).mpr hi⟩
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image (front u)
    (fun i => (faceBound i-inner ℝ (faceNormal i) z)/inner ℝ (faceNormal i) u) hfront
  let r := (faceBound i-inner ℝ (faceNormal i) z)/inner ℝ (faceNormal i) u
  have hi0 : 0 < inner ℝ (faceNormal i) u := (mem_front u i).mp hi
  have hzi := K_halfspaces z |>.mp hz
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr (hzi i)) hi0.le
  have hre : r * inner ℝ (faceNormal i) u = faceBound i-inner ℝ (faceNormal i) z := by
    dsimp [r]
    exact div_mul_cancel₀ _ (ne_of_gt hi0)
  refine ⟨i,hi,z+r•u,⟨?_,?_⟩,projection_add_axis hu z r⟩
  · rw [K_halfspaces]
    intro j
    simp only [inner_add_right,inner_smul_right]
    by_cases hj : 0 < inner ℝ (faceNormal j) u
    · have hm := hmin j ((mem_front u j).mpr hj)
      have hm' : r * inner ℝ (faceNormal j) u ≤ faceBound j-inner ℝ (faceNormal j) z :=
        (le_div_iff₀ hj).mp hm
      linarith only [hm']
    · have hn := mul_nonpos_of_nonneg_of_nonpos hr (le_of_not_gt hj)
      linarith only [hn,hzi j]
  · rw [inner_add_right,inner_smul_right,hre]
    ring

lemma shadow_front {u : Space} (hu : ‖u‖ = 1) :
    projection u '' K = ⋃ i ∈ front u, projection u '' face i := by
  ext q
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨i,hi,p,hp,hpq⟩ := forward_face hu hz
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,⟨p,hp,hpq⟩⟩⟩
  · intro h
    obtain ⟨i,hi,p,hp,hpq⟩ := mem_iUnion.mp h |>.imp (fun _ => mem_iUnion.mp)
    exact ⟨p,hp.1,hpq⟩

lemma projected_faces_inter_subset {u : Space} {i j : Fin 4}
    (hi : i ∈ front u) (hj : j ∈ front u) :
    (projection u '' face i) ∩ (projection u '' face j) ⊆ projection u '' (face i ∩ face j) := by
  rintro q ⟨⟨p,hp,hpq⟩,⟨z,hz,hzq⟩⟩
  have hh : projection u p = projection u z := hpq.trans hzq.symm
  let r := inner ℝ u p - inner ℝ u z
  have hpe : p = z+r•u := by
    dsimp [projection] at hh
    dsimp [r]
    calc
      p = (p-inner ℝ u p•u)+inner ℝ u p•u := by abel
      _ = (z-inner ℝ u z•u)+inner ℝ u p•u := by rw [hh]
      _ = z+(inner ℝ u p-inner ℝ u z)•u := by module
  have hzi := (K_halfspaces z).mp hz.1 i
  have hpj := (K_halfspaces p).mp hp.1 j
  have he_i : inner ℝ (faceNormal i) p =
      inner ℝ (faceNormal i) z+r*inner ℝ (faceNormal i) u := by
    rw [hpe,inner_add_right,inner_smul_right]
  have he_j : inner ℝ (faceNormal j) p =
      inner ℝ (faceNormal j) z+r*inner ℝ (faceNormal j) u := by
    rw [hpe,inner_add_right,inner_smul_right]
  have hr0 : 0 ≤ r := by
    have := (mem_front u i).mp hi
    nlinarith only [hzi,hp.2,he_i,this]
  have hr1 : r ≤ 0 := by
    have := (mem_front u j).mp hj
    nlinarith only [hpj,hz.2,he_j,this]
  have hr : r = 0 := le_antisymm hr1 hr0
  have hpz : p = z := by simpa [hr] using hpe
  exact ⟨p,⟨hp,hpz.symm ▸ hz⟩,hpq⟩

end TriangularCovering

namespace TriangularCovering

lemma vertical_edge_mem (a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    point ((1-t)*a) (t*b) t ∈ triangle (point a 0 0) (point 0 b 1) (point 0 b 1) := by
  rw [mem_triangle_iff]
  refine ⟨t,0,ht0,le_rfl,by linarith,?_⟩
  ext i
  fin_cases i <;> dsimp [point] <;> ring

lemma upper_edge_mem (y : ℝ) (hy : |y| ≤ 1) :
    point 0 y 1 ∈ triangle (point 0 (-1) 1) (point 0 1 1) (point 0 1 1) := by
  rw [mem_triangle_iff]
  refine ⟨(y+1)/2,0,by linarith [(abs_le.mp hy).1],le_rfl,
    by linarith [(abs_le.mp hy).2],?_⟩
  ext i
  fin_cases i <;> dsimp [point] <;> ring

lemma lower_edge_mem (x : ℝ) (hx : |x| ≤ 1) :
    point x 0 0 ∈ triangle (point (-1) 0 0) (point 1 0 0) (point 1 0 0) := by
  rw [mem_triangle_iff]
  refine ⟨(x+1)/2,0,by linarith [(abs_le.mp hx).1],le_rfl,
    by linarith [(abs_le.mp hx).2],?_⟩
  ext i
  fin_cases i <;> dsimp [point] <;> ring

lemma face_coord (i : Fin 4) (x y t : ℝ) :
    inner ℝ (faceNormal i) (point x y t) = faceBound i ↔
      (![x+t,-x+t,y-t,-y-t] : Fin 4 → ℝ) i = (![1,1,0,0] : Fin 4 → ℝ) i := by
  fin_cases i <;> simp only [inner_coord] <;> dsimp [faceNormal,faceBound,point]
  all_goals constructor <;> intro h <;> nlinarith only [H_pos,h]

lemma face_pair_edge {i j : Fin 4} (hij : i ≠ j) :
    ∃ a b : Space, face i ∩ face j ⊆ triangle a b b := by
  wlog hlt : i < j generalizing i j
  · obtain ⟨a,b,hab⟩ := this hij.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)
    exact ⟨a,b,by simpa only [inter_comm] using hab⟩
  fin_cases i <;> fin_cases j <;> norm_num at hlt
  · refine ⟨point 0 (-1) 1,point 0 1 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 0 x y t).mp hi
    have hj' := (face_coord 1 x y t).mp hj
    dsimp at hi' hj'
    have ht : t = 1 := by linarith only [hi',hj']
    have hx0 : x = 0 := by linarith only [hi',hj']
    subst t; subst x
    exact upper_edge_mem y hy
  · refine ⟨point 1 0 0,point 0 1 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 0 x y t).mp hi
    have hj' := (face_coord 2 x y t).mp hj
    dsimp at hi' hj'
    convert vertical_edge_mem 1 1 t ht0 ht1 using 1; congr 1 <;> linarith only [hi',hj']
  · refine ⟨point 1 0 0,point 0 (-1) 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 0 x y t).mp hi
    have hj' := (face_coord 3 x y t).mp hj
    dsimp at hi' hj'
    convert vertical_edge_mem 1 (-1) t ht0 ht1 using 1; congr 1 <;> linarith only [hi',hj']
  · refine ⟨point (-1) 0 0,point 0 1 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 1 x y t).mp hi
    have hj' := (face_coord 2 x y t).mp hj
    dsimp at hi' hj'
    convert vertical_edge_mem (-1) 1 t ht0 ht1 using 1; congr 1 <;> linarith only [hi',hj']
  · refine ⟨point (-1) 0 0,point 0 (-1) 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 1 x y t).mp hi
    have hj' := (face_coord 3 x y t).mp hj
    dsimp at hi' hj'
    convert vertical_edge_mem (-1) (-1) t ht0 ht1 using 1; congr 1 <;> linarith only [hi',hj']
  · refine ⟨point (-1) 0 0,point 1 0 0,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 2 x y t).mp hi
    have hj' := (face_coord 3 x y t).mp hj
    dsimp at hi' hj'
    have ht : t = 0 := by linarith only [hi',hj']
    have hy0 : y = 0 := by linarith only [hi',hj']
    subst t; subst y
    exact lower_edge_mem x (by simpa using hx)

lemma cross3_self (a : Space) : cross3 a a = 0 := by
  rw [cross3_coord]
  ext i
  fin_cases i <;> dsimp <;> ring

lemma face_pair_projection_null {u : Space} (hu : ‖u‖ = 1) {i j : Fin 4} (hij : i ≠ j) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' (face i ∩ face j)) = 0 := by
  obtain ⟨a,b,hab⟩ := face_pair_edge hij
  apply measure_mono_null (image_mono hab)
  rw [projection_triangle_measure hu, cross3_self,inner_zero_right,abs_zero,zero_div,ENNReal.ofReal_zero]

lemma front_pairwise_aeDisjoint {u : Space} (hu : ‖u‖ = 1) :
    (↑(front u) : Set (Fin 4)).Pairwise
      (fun i j => AEDisjoint (Measure.euclideanHausdorffMeasure 2)
        (projection u '' face i) (projection u '' face j)) := by
  intro i hi j hj hij
  exact measure_mono_null (projected_faces_inter_subset hi hj) (face_pair_projection_null hu hij)

lemma shadow_measure {u : Space} (hu : ‖u‖ = 1) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' K) =
      ∑ i ∈ front u, ENNReal.ofReal |inner ℝ (faceNormal i) u| := by
  rw [shadow_front hu,measure_biUnion_finset₀ (front_pairwise_aeDisjoint hu)]
  · exact Finset.sum_congr rfl (fun i _ => face_projection_measure hu i)
  · intro i _hi
    rw [face_eq_triangle]
    exact ((triangle_compact _ _ _).image
      (projLinear u).continuous_of_finiteDimensional).measurableSet.nullMeasurableSet

end TriangularCovering

namespace TriangularCovering

lemma max_pos_abs (a : ℝ) : max a 0 = (|a|+a)/2 := by
  by_cases h : 0 ≤ a
  · rw [max_eq_left h,abs_of_nonneg h]; ring
  · rw [max_eq_right (le_of_not_ge h),abs_of_nonpos (le_of_not_ge h)]; ring

lemma shadowArea_positive_sum {u : Space} (hu : ‖u‖ = 1) :
    shadowArea u = ∑ i : Fin 4, max (inner ℝ (faceNormal i) u) 0 := by
  rw [shadowArea,area,shadow_measure hu,ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [front,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 < inner ℝ (faceNormal i) u
  · rw [ite_eq_left h,abs_of_pos h,max_eq_left h.le]
  · rw [ite_eq_right h,max_eq_right (le_of_not_gt h)]

lemma shadowArea_abs_sum {u : Space} (hu : ‖u‖ = 1) :
    shadowArea u = (∑ i : Fin 4, |inner ℝ (faceNormal i) u|)/2 := by
  rw [shadowArea_positive_sum hu]
  simp_rw [max_pos_abs]
  rw [← Finset.sum_div,Finset.sum_add_distrib,faceNormal_sum,add_zero]

lemma abs_pair (a b : ℝ) : |a+b|+|a-b| = 2*max |a| |b| := by
  simp only [abs_eq_max_neg,max_def]
  split_ifs <;> linarith

lemma shadowArea_formula {u : Space} (hu : ‖u‖ = 1) :
    shadowArea u = max (H*|u 0|) |u 2| + max (H*|u 1|) |u 2| := by
  rw [shadowArea_abs_sum hu,Fin.sum_univ_four]
  simp only [inner_coord]
  dsimp [faceNormal]
  have h1 := abs_pair (H*u 0) (u 2)
  have h2 := abs_pair (H*u 1) (u 2)
  rw [abs_mul,abs_of_pos H_pos] at h1 h2
  have he1 : |-H*u 0+0*u 1+1*u 2| = |H*u 0-u 2| := by
    rw [← abs_neg]
    congr 1
    ring
  have he2 : |0*u 0+-H*u 1+-1*u 2| = |H*u 1+u 2| := by
    rw [← abs_neg]
    congr 1
    ring
  rw [he1,he2]
  have he3 : |H*u 0+0*u 1+1*u 2| = |H*u 0+u 2| := by congr 1; ring
  have he4 : |0*u 0+H*u 1+-1*u 2| = |H*u 1-u 2| := by congr 1; ring
  rw [he3,he4]
  linarith only [h1,h2]

lemma shadowArea_ge_H {u : Space} (hu : ‖u‖ = 1) : H ≤ shadowArea u := by
  rw [shadowArea_formula hu]
  let A := max (H*|u 0|) |u 2|
  let B := max (H*|u 1|) |u 2|
  have hA : H*|u 0| ≤ A := le_max_left _ _
  have hB : H*|u 1| ≤ B := le_max_left _ _
  have hAz : |u 2| ≤ A := le_max_right _ _
  have hBz : |u 2| ≤ B := le_max_right _ _
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hAz
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hBz
  have hAs := pow_le_pow_left₀ (mul_nonneg H_pos.le (abs_nonneg (u 0))) hA 2
  have hBs := pow_le_pow_left₀ (mul_nonneg H_pos.le (abs_nonneg (u 1))) hB 2
  rw [mul_pow,H_sq,sq_abs] at hAs hBs
  have hAB := mul_le_mul hAz hBz (abs_nonneg _) hA0
  have hu2 := real_inner_self_eq_norm_sq u
  rw [inner_coord,hu] at hu2
  have hz2 : |u 2| * |u 2| = (u 2)^2 := by nlinarith only [sq_abs (u 2)]
  change H ≤ A+B
  nlinarith only [hu2,hAs,hBs,hAB,hz2,H_sq,H_pos,hA0,hB0]

lemma xAxis_unit : ‖tiltV 0 0 0‖ = 1 := by rw [tiltV_norm]; norm_num

lemma xAxis_shadow : shadowArea (tiltV 0 0 0) = H := by
  rw [shadowArea_formula xAxis_unit]
  dsimp [tiltV]
  simp [H_pos.le]

/-- The minimum Euclidean shadow area equals the height H. -/
theorem projection_minimum : A_min = H := by
  unfold A_min
  apply le_antisymm
  · apply csInf_le
    · exact ⟨H,by rintro a ⟨u,hu,rfl⟩; exact shadowArea_ge_H hu⟩
    · exact ⟨tiltV 0 0 0,xAxis_unit,xAxis_shadow.symm⟩
  · apply le_csInf
    · exact ⟨H,tiltV 0 0 0,xAxis_unit,xAxis_shadow.symm⟩
    · rintro a ⟨u,hu,rfl⟩
      exact shadowArea_ge_H hu

end TriangularCovering

namespace TriangularCovering

/-- The actual two-dimensional linear plane of a unit normal. -/
def normalPlane (u : Space) : Submodule ℝ Space := (ℝ ∙ u)ᗮ

lemma normalPlane_rank {u : Space} (hu : ‖u‖ = 1) :
    Module.finrank ℝ (normalPlane u) = 2 := by
  have hun : u ≠ 0 := by intro h; simp [h] at hu
  have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hun] at h
  have hr : Module.finrank ℝ Space = 3 := by simp
  rw [hr] at h
  change 1 + Module.finrank ℝ (normalPlane u) = 3 at h
  omega

lemma normalPlane_projection {u : Space} (hu : ‖u‖ = 1) (z : Space) :
    (normalPlane u).starProjection z = projection u z := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (projection_perp hu z)
  · intro w hw
    have hw' : inner ℝ u w = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
    simp [projection,inner_smul_left,hw']

lemma twoPlane_normal (P : Submodule ℝ Space) (hp : Module.finrank ℝ P = 2) :
    ∃ u : Space, ‖u‖ = 1 ∧ P = normalPlane u := by
  have ho : Module.finrank ℝ Pᗮ = 1 := by
    have h := P.finrank_add_finrank_orthogonal
    have hr : Module.finrank ℝ Space = 3 := by simp
    rw [hp,hr] at h
    omega
  have : Nontrivial Pᗮ := Module.nontrivial_of_finrank_pos (by rw [ho]; norm_num)
  obtain ⟨v,hv⟩ := exists_ne (0 : Pᗮ)
  have hv' : (v : Space) ≠ 0 := fun h => hv (Subtype.ext h)
  have hu := unit_norm hv'
  have hun : unit (v : Space) ≠ 0 := by intro h; simp [h] at hu
  have hs : (ℝ ∙ unit (v : Space)) = Pᗮ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (singleton_subset_iff.mpr (Pᗮ.smul_mem _ v.property))
    · rw [finrank_span_singleton hun,ho]
  refine ⟨unit (v : Space),hu,?_⟩
  dsimp [normalPlane]
  rw [hs,P.orthogonal_orthogonal]

/-- Planar Lebesgue measure of the orthogonal shadow, intrinsically in the plane. -/
def intrinsicShadow (P : Submodule ℝ Space) : ℝ :=
  (volume (P.orthogonalProjectionOnto '' K)).toReal

lemma intrinsicShadow_eq_area (P : Submodule ℝ Space) (hp : Module.finrank ℝ P = 2) :
    intrinsicShadow P = area (P.starProjection '' K) := by
  have himage : P.starProjection '' K =
      (Subtype.val : P → Space) '' (P.orthogonalProjectionOnto '' K) := by
    rw [image_image]
    rfl
  have hm : (Measure.euclideanHausdorffMeasure 2 : Measure P) = volume := by
    rw [← hp, InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  unfold intrinsicShadow area
  rw [himage,isometry_subtype_coe.euclideanHausdorffMeasure_image,hm]

lemma intrinsicShadow_normal {u : Space} (hu : ‖u‖ = 1) :
    intrinsicShadow (normalPlane u) = shadowArea u := by
  rw [intrinsicShadow_eq_area _ (normalPlane_rank hu)]
  unfold shadowArea
  congr 2
  funext z
  exact normalPlane_projection hu z

lemma shadow_values_eq_planes :
    {a : ℝ | ∃ P : Submodule ℝ Space, Module.finrank ℝ P = 2 ∧ a = intrinsicShadow P} =
      {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = shadowArea u} := by
  ext a
  constructor
  · rintro ⟨P,hp,rfl⟩
    obtain ⟨u,hu,rfl⟩ := twoPlane_normal P hp
    exact ⟨u,hu,intrinsicShadow_normal hu⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨normalPlane u,normalPlane_rank hu,(intrinsicShadow_normal hu).symm⟩

/-- The unit-normal parametrization preserves the minimum-area definition. -/
lemma A_min_eq_plane_inf : A_min = sInf
    {a : ℝ | ∃ P : Submodule ℝ Space, Module.finrank ℝ P = 2 ∧ a = intrinsicShadow P} := by
  rw [shadow_values_eq_planes]
  rfl

/-- The minimum is attained over all two-dimensional subspaces. -/
theorem minimum_over_planes :
    IsLeast {a : ℝ | ∃ P : Submodule ℝ Space,
      Module.finrank ℝ P = 2 ∧ a = intrinsicShadow P} H := by
  rw [shadow_values_eq_planes]
  constructor
  · exact ⟨tiltV 0 0 0,xAxis_unit,xAxis_shadow.symm⟩
  · rintro a ⟨u,hu,rfl⟩
    exact shadowArea_ge_H hu

end TriangularCovering

end

end OAI
