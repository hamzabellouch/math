import OAI.Probability.FirstPassage.SourceTilt

namespace OAI

namespace PlanarFPP
open Set

noncomputable def sourceEndpoint (b : ℝ) (n : ℤ) : Vertex := (n,⌊b*n⌋)

theorem sourceEndpoint_transverse (b : ℝ) (n : ℤ) :
    |transverse b (sourceEndpoint b n)| ≤ 1 := by
  have hl := Int.floor_le (b*n)
  have hu := Int.lt_floor_add_one (b*n)
  simp only [sourceEndpoint,transverse]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem sourceEndpoint_distance (b : ℝ) (n : ℤ) (hb : |b| ≤ 1) (hn : 1 ≤ n) :
    ‖latticeEmbed (sourceEndpoint b n)‖ ≤ 3*(n : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr := sourceEndpoint_transverse b n
  have ht := abs_add_le (transverse b (sourceEndpoint b n)) (b*(n : ℝ))
  have he : transverse b (sourceEndpoint b n)+b*(n : ℝ)=(⌊b*n⌋ : ℝ) := by
    simp [transverse,sourceEndpoint]
  rw [he,abs_mul,abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at ht
  have hm := mul_le_mul_of_nonneg_right hb (by linarith : (0 : ℝ) ≤ n)
  have hh := plane_norm_le_coordinates (latticeEmbed (sourceEndpoint b n))
  change ‖latticeEmbed (sourceEndpoint b n)‖ ≤ |(n : ℝ)|+|(⌊b*n⌋ : ℝ)| at hh
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at hh
  linarith

theorem sourceEndpoint_norm_cost (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (b : ℝ) (n : ℤ) (hn : 0 ≤ n) :
    μ (latticeEmbed (sourceEndpoint b n)) ≤ μ (direction b)*(n : ℝ)+μ transverseUnit := by
  let r := transverse b (sourceEndpoint b n)
  have he : latticeEmbed (sourceEndpoint b n)=(n : ℝ) • direction b+r • transverseUnit := by
    ext i
    fin_cases i <;> simp [r,sourceEndpoint,transverse,latticeEmbed,direction,transverseUnit,
      PiLp.add_apply,PiLp.smul_apply]
    ring
  rw [he]
  have hh := hμ.triangle ((n : ℝ) • direction b) (r • transverseUnit)
  rw [hμ.homogeneous,hμ.homogeneous,abs_of_nonneg (by exact_mod_cast hn : (0 : ℝ) ≤ n)] at hh
  have hr := mul_le_mul_of_nonneg_right (sourceEndpoint_transverse b n) (hμ.nonneg transverseUnit)
  dsimp [r] at hh
  linarith

theorem sourceEndpoint_tube_containment (b C δ s : ℝ) (n : ℤ)
    (hb : |b| ≤ 1) (hs : 1 ≤ s) (hn : 1 ≤ n) (hns : (n : ℝ) ≤ C*s)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/4) (hδC : δ*C ≤ 1/2) :
    SegmentTube 0 (sourceEndpoint b n) (δ*n) ⊆ rareFastRegion b 1 8 s n 0 := by
  rintro z ⟨t,ht0,ht1,hd⟩
  let u := latticeEmbed z-segmentPoint 0 (sourceEndpoint b n) t
  have hnorm : ‖u‖ ≤ δ*n := hd
  have hx : u 0=(z.1 : ℝ)-t*n := by
    simp [u,segmentPoint,sourceEndpoint,latticeEmbed,PiLp.sub_apply,PiLp.smul_apply]
  have hr : rCoord b u=transverse b z-t*transverse b (sourceEndpoint b n) := by
    simp [u,segmentPoint,sourceEndpoint,latticeEmbed,transverse,rCoord_apply,PiLp.sub_apply,PiLp.smul_apply]
    ring
  have hxbound := (plane_coordinate_le_norm u 0).trans hnorm
  rw [hx] at hxbound
  have hx' := abs_le.mp hxbound
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδn : δ*(n : ℝ) ≤ n/4 := by nlinarith
  have htn : t*(n : ℝ) ≤ n := by nlinarith
  have htn0 : 0 ≤ t*(n : ℝ) := by positivity
  have hrbound := transverse_plane_lipschitz b hb u
  rw [hr] at hrbound
  have hseg : |t*transverse b (sourceEndpoint b n)| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg ht0]
    nlinarith [sourceEndpoint_transverse b n]
  have hsum := abs_add_le (transverse b z-t*transverse b (sourceEndpoint b n))
    (t*transverse b (sourceEndpoint b n))
  rw [sub_add_cancel] at hsum
  have hscale := mul_le_mul_of_nonneg_left hns hδ
  have hscale' := mul_le_mul_of_nonneg_right hδC (by linarith : 0 ≤ s)
  refine ⟨?_,?_,?_⟩
  · simp only [sub_zero,neg_one_mul]
    linarith
  · norm_num only [sub_zero,one_add_one_eq_two]
    linarith
  · simp only [sub_zero]
    nlinarith

theorem horizontal_in_crossingRegion (b s : ℝ) (n : ℤ) (hb : |b| ≤ 1)
    (hn : 0 ≤ n) (hns : (n : ℝ) ≤ 8*s) :
    PathIn 0 (horizontal n) (rareFastRegion b 1 8 s n 0) := by
  intro i _
  have he : displacement ((horizontal n).take i)=(((min i n.toNat : ℕ) : ℤ),0) := by
    simp [horizontal,hn,displacement,Step.delta]
  have hm : (min i n.toNat : ℤ) ≤ n := by
    have := min_le_right i n.toNat
    exact_mod_cast (show (min i n.toNat : ℤ) ≤ n by omega)
  have hm0 : (0 : ℤ) ≤ min i n.toNat := by positivity
  have hm' : ((min i n.toNat : ℕ) : ℝ) ≤ n := by exact_mod_cast hm
  have hm0' : (0 : ℝ) ≤ min i n.toNat := by positivity
  rw [he]
  simp only [zero_add,rareFastRegion,mem_ofPred_eq,sub_zero,transverse,Int.cast_natCast,
    Int.cast_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg hm0',neg_one_mul,one_add_one_eq_two]
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hb hm0'
  exact ⟨by linarith,by linarith,by linarith⟩

end PlanarFPP

end OAI
