import OAI.Geometry.CylinderCovering.Footprints.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Footprints.QuadraticPhysicalFootprints
import OAI.Geometry.CylinderCovering.Footprints.Convergence
import OAI.Geometry.CylinderCovering.Footprints.Bridge
import OAI.Geometry.CylinderCovering.Radial.PartitionCover

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace CylinderCovering.CanonicalFootprintFinite
open RuledApproximation RadialRiemann Footprints

private def rotationIsometry : Space ≃ₗᵢ[ℝ] Space where
  toFun := rotation
  invFun z := !₂[-z 1,z 0,-z 2]
  left_inv z := by ext i; fin_cases i <;> simp [rotation]
  right_inv z := by ext i; fin_cases i <;> simp [rotation]
  map_add' z w := by ext i; fin_cases i <;> simp [rotation] <;> ring
  map_smul' c z := by ext i; fin_cases i <;> simp [rotation]
  norm_map' z := by
    change ‖rotation z‖ = ‖z‖
    have hs : ‖rotation z‖^2 = ‖z‖^2 := by
      simp [EuclideanSpace.real_norm_sq_eq, rotation, Fin.sum_univ_succ]
      ring
    nlinarith [norm_nonneg (rotation z), norm_nonneg z]

lemma lowerSweep_eq_rotation (h ε : ℝ) (R : ℝ → ℝ) :
    RadialPairedSweep.lowerSweep h ε R = rotation '' RadialPairedSweep.upperSweep h ε R := by
  ext z
  constructor
  · rintro ⟨q,hq,ρ,hρ,y,hy,rfl⟩
    refine ⟨RadialPairedSweep.point (-y) (ρ*q-ε*(-y)*RadialCaps.G q)
      (h*(1-ρ+ε*(-y)*q)), ⟨q,hq,ρ,hρ,-y,by simpa using hy,rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [rotation, RadialPairedSweep.point]
    ring
  · rintro ⟨z,⟨q,hq,ρ,hρ,x,hx,rfl⟩,rfl⟩
    refine ⟨q,hq,ρ,hρ,-x,by simpa using hx,?_⟩
    ext i
    fin_cases i <;> simp [rotation, RadialPairedSweep.point] <;> ring

lemma midpoint_mem (N : ℕ) (i : Fin N) : midpoint N i ∈ cell (-1) 1 N i := by
  have hd := step_pos (by norm_num : (-1:ℝ)<1) (Nat.zero_lt_of_lt i.isLt)
  have hs := point_succ (-1) 1 N i
  change _ ≤ midpoint N i ∧ midpoint N i ≤ _
  dsimp [midpoint]
  constructor <;> linarith

lemma midpoint_dist {N : ℕ} {i : Fin N} {q : ℝ} (hq : q ∈ cell (-1) 1 N i) :
    |q-midpoint N i| ≤ step (-1) 1 N/2 := by
  have hs := point_succ (-1) 1 N i
  rw [abs_le]
  dsimp [midpoint]
  constructor <;> linarith [hq.1,hq.2]

lemma leftTag_mem (N : ℕ) (i : Fin N) : leftTag N i ∈ cell (-1) 1 N i := by
  have hd := step_pos (by norm_num : (-1:ℝ)<1) (Nat.zero_lt_of_lt i.isLt)
  have hs := point_succ (-1) 1 N i
  exact ⟨le_rfl,by dsimp [leftTag]; linarith⟩

private lemma cylinder_axis (h ε c : ℝ) (F : Set (ℝ × ℝ)) :
    (PhysicalFootprints.footprintCylinder h (quadraticVelocity ε c) F).axis =
      RadialPairedSweep.upperAxis h ε c := by
  have hv : PhysicalFootprints.direction h (quadraticVelocity ε c) =
      RadialPairedSweep.point 1 (-ε*RadialCaps.G c) (h*ε*c) := by
    ext i
    fin_cases i <;> simp [PhysicalFootprints.direction, quadraticVelocity,
      vec2,vec3,RadialPairedSweep.point,RadialCaps.G]
    ring
  change ‖PhysicalFootprints.direction h (quadraticVelocity ε c)‖⁻¹ •
    PhysicalFootprints.direction h (quadraticVelocity ε c) = _
  rw [hv]
  rfl

private lemma physical_weight (h ε t : ℝ) :
    physicalWeight h (quadraticVelocity ε t) =
      1/Real.sqrt (1+ε^2*(RadialCaps.G t^2+h^2*t^2)) := by
  unfold physicalWeight quadraticVelocity RadialCaps.G
  simp only [vec2_apply_zero,vec2_apply_one]
  congr 2
  ring

private theorem assemble {h ε : ℝ} (hh : 0<h) (R : ℝ → ℝ)
    (tag : (N : ℕ) → Fin N → ℝ) (F : (N : ℕ) → Fin N → Set (ℝ × ℝ))
    (hcompact : ∀ N i, IsCompact (F N i))
    (hcontain : ∀ N, 0<N → ∀ q ∈ Icc (-1:ℝ) 1,
      ∀ ρ ∈ Icc (0:ℝ) (R q), ∀ x : ℝ, |x|≤2 →
      ∃ i : Fin N, quadraticIntercept ε x q (tag N i) ρ ∈ F N i)
    (hlimit : Tendsto (fun N => ∑ i : Fin N,
      volume.real (F N i)*physicalWeight h (quadraticVelocity ε (tag N i))) atTop
      (𝓝 (RadialPairedSweep.physicalCost h ε R))) :
    FamilyConclusion h ε R tag F := by
  let U := fun N (i : Fin N) => PhysicalFootprints.footprintCylinder h
    (quadraticVelocity ε (tag N i)) (F N i)
  let L := fun N (i : Fin N) => (U N i).rotate rotationIsometry
  have hUcompact : ∀ N i, IsCompact (U N i).base := fun N i =>
    PhysicalFootprints.footprintCylinder_compact _ _ (hcompact N i)
  have hLcompact : ∀ N i, IsCompact (L N i).base := fun N i =>
    (hUcompact N i).image (rotatedPlane (U N i).axis rotationIsometry).continuous
  have harea : ∀ N i, (U N i).area = localCost h ε (tag N i) (F N i) := by
    intro N i
    exact projected_footprint_area hh _ _ _
  have hLarea : ∀ N i, (L N i).area = (U N i).area := fun N i =>
    Cylinder.rotate_area (U N i) rotationIsometry
  have hUcover : ∀ N, 0<N → RadialPairedSweep.upperSweep h ε R ⊆ familySet (U N) := by
    intro N hN z hz
    rcases hz with ⟨q,hq,ρ,hρ,x,hx,rfl⟩
    obtain ⟨i,hi⟩ := hcontain N hN q hq ρ hρ x hx
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    exact quadraticSweepPoint_mem_projected hi
  refine ⟨U,L,?_,?_⟩
  · intro N hN
    refine ⟨?_, hUcover N hN, ?_⟩
    · intro i
      have hc := hUcompact N i
      have hl := hLcompact N i
      have hconv : Convex ℝ (L N i).base ↔ Convex ℝ (U N i).base := by
        change Convex ℝ ((rotatedPlane (U N i).axis rotationIsometry) '' (U N i).base) ↔ _
        constructor
        · intro hC
          have hhC := hC.affine_preimage (rotatedPlane (U N i).axis rotationIsometry).toAffineMap
          change Convex ℝ ((rotatedPlane (U N i).axis rotationIsometry) ⁻¹'
            ((rotatedPlane (U N i).axis rotationIsometry) '' (U N i).base)) at hhC
          rwa [Set.preimage_image_eq _ (rotatedPlane (U N i).axis rotationIsometry).injective] at hhC
        · intro hC
          exact hC.linear_image (rotatedPlane (U N i).axis rotationIsometry).toLinearMap
      refine ⟨cylinder_axis _ _ _ _, ?_, ?_, ?_,hc,hl,hc.measurableSet,hl.measurableSet,
        hc.measure_lt_top,hl.measure_lt_top,?_,?_,harea N i,(hLarea N i).trans (harea N i)⟩
      · change rotation ((U N i).axis) = _
        rw [show (U N i).axis = _ from cylinder_axis _ _ _ _]
      · exact projected_footprint_ambient_base _ _ _ _
      · change Subtype.val '' ((rotatedPlane (U N i).axis rotationIsometry) '' (U N i).base) = _
        rw [Set.image_image]
        have hb := projected_footprint_ambient_base h ε (tag N i) (F N i)
        change Subtype.val '' (U N i).base = _ at hb
        rw [← hb,Set.image_image]
        rfl
      · exact projected_footprint_convex_iff hh _ _ _
      · exact hconv.trans (projected_footprint_convex_iff hh _ _ _)
    · rw [lowerSweep_eq_rotation]
      rintro z ⟨x,hx,rfl⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hUcover N hN hx)
      apply mem_iUnion.mpr
      refine ⟨i,?_⟩
      change rotation x ∈ ((U N i).rotate rotationIsometry).carrier
      rw [Cylinder.rotate_carrier]
      exact ⟨x,hi,rfl⟩
  · have hu : Tendsto (fun N => familyArea (U N)) atTop
        (𝓝 (h*RadialPairedSweep.physicalCost h ε R)) := by
      convert hlimit.const_mul h using 1
      funext N
      rw [familyArea,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [PhysicalFootprints.footprintCylinder_area hh _ (hcompact N i)]
      ring
    have hl : ∀ N, familyArea (L N) = familyArea (U N) := by
      intro N
      exact Finset.sum_congr rfl (fun i _ => hLarea N i)
    simp_rw [hl]
    convert hu.add hu using 1
    ring_nf

private lemma weight_continuous (h ε : ℝ) :
    Continuous (fun t => physicalWeight h (quadraticVelocity ε t)) := by
  apply (physicalWeight_continuous h).comp
  unfold quadraticVelocity vec2
  fun_prop

private lemma physicalCost_eq (h ε : ℝ) (R : ℝ → ℝ) :
    RadialPairedSweep.physicalCost h ε R =
      (1/2:ℝ)*(∫ t in (-1:ℝ)..1, R t^2*physicalWeight h (quadraticVelocity ε t)) := by
  unfold RadialPairedSweep.physicalCost
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [physical_weight]
  ring

private lemma absolute_limit {h ε A B : ℝ} {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) (hR0 : ∀ q ∈ Icc (-1:ℝ) 1,0≤R q)
    (hA : 0≤A) (hB : 0≤B) (tag : (N : ℕ) → Fin N → ℝ)
    (htag : ∀ N, IsTagged (-1) 1 N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N, volume.real (absoluteFeet R A B N i)*
      physicalWeight h (quadraticVelocity ε (tag N i))) atTop
      (𝓝 (RadialPairedSweep.physicalCost h ε R)) := by
  rw [physicalCost_eq]
  have ht := RadialFootprints.absoluteFootprint_area_sum_tendsto (by norm_num : (-1:ℝ)<1)
    hR (weight_continuous h ε).continuousOn hR0 hA hB tag midpoint htag
  simpa only [absoluteFeet,absoluteFootprint_eq_radial] using ht

private lemma affine_limit {h ε A B : ℝ} {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) (hR0 : ∀ q ∈ Icc (-1:ℝ) 1,0≤R q)
    (hA : 0≤A) (hB : A/2≤B) :
    Tendsto (fun N => ∑ i : Fin N, volume.real (affineFeet R A B N i)*
      physicalWeight h (quadraticVelocity ε (midpoint N i))) atTop
      (𝓝 (RadialPairedSweep.physicalCost h ε R)) := by
  rw [physicalCost_eq]
  have ht := RadialFootprints.affineFootprint_area_sum_tendsto (by norm_num : (-1:ℝ)<1)
    hR (weight_continuous h ε).continuousOn hR0 hA hB midpoint midpoint midpoint_mem
  simpa only [affineFeet,affineFootprint_eq_radial] using ht

theorem absolute_arbitrary {h ε : ℝ} (hh : 0<h) (hε : 0≤ε) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) (hR0 : ∀ q ∈ Icc (-1:ℝ) 1,0≤R q)
    {A B : ℝ} (hA : 2*ε≤A) (hB : ε≤B)
    (tag : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged (-1) 1 N (tag N)) :
    FamilyConclusion h ε R tag (absoluteFeet R A B) := by
  apply assemble hh R tag (absoluteFeet R A B)
  · intro N i
    exact isCompact_absoluteFootprint _ _ _ _ _
  · intro N hN q hq ρ hρ x hx
    obtain ⟨i,hi⟩ := RadialRiemann.exists_cell hN hq
    have hqc : |q-tag N i| ≤ step (-1) 1 N := by
      simpa only [Real.dist_eq] using cell_dist_le hi (htag N i)
    refine ⟨i,?_⟩
    exact quadratic_mem_absolute hε (step_pos (by norm_num) hN).le hx hqc
      (midpoint_dist hi) hρ.1 (hρ.2.trans (le_capMax (by norm_num) hR hi)) hA hB
  · exact absolute_limit hR hR0 (by linarith) (hε.trans hB) tag htag

theorem absolute_midpoint {h ε : ℝ} (hh : 0<h) (hε : 0≤ε) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) (hR0 : ∀ q ∈ Icc (-1:ℝ) 1,0≤R q)
    {A B : ℝ} (hA : ε≤A) (hB : ε/4≤B) :
    FamilyConclusion h ε R midpoint (absoluteFeet R A B) := by
  apply assemble hh R midpoint (absoluteFeet R A B)
  · intro N i
    exact isCompact_absoluteFootprint _ _ _ _ _
  · intro N hN q hq ρ hρ x hx
    obtain ⟨i,hi⟩ := RadialRiemann.exists_cell hN hq
    refine ⟨i,?_⟩
    exact quadratic_mem_absolute_midpoint hε (step_pos (by norm_num) hN).le hx
      (midpoint_dist hi) hρ.1 (hρ.2.trans (le_capMax (by norm_num) hR hi)) hA hB
  · exact absolute_limit hR hR0 (hε.trans hA) (by linarith) midpoint midpoint_mem

theorem affine_midpoint {h ε : ℝ} (hh : 0<h) (hε : 0≤ε) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) (hR0 : ∀ q ∈ Icc (-1:ℝ) 1,0≤R q)
    {A B : ℝ} (hA : ε≤A) (hB : 3*ε/4≤B) (hwidth : A/2≤B) :
    FamilyConclusion h ε R midpoint (affineFeet R A B) := by
  apply assemble hh R midpoint (affineFeet R A B)
  · intro N i
    exact isCompact_affineFootprint _ _ _ _ _
  · intro N hN q hq ρ hρ x hx
    obtain ⟨i,hi⟩ := RadialRiemann.exists_cell hN hq
    refine ⟨i,?_⟩
    exact quadratic_mem_affine_midpoint hε (step_pos (by norm_num) hN).le hx
      (midpoint_dist hi) hρ.1 (hρ.2.trans (le_capMax (by norm_num) hR hi)) hA hB
  · exact affine_limit hR hR0 (hε.trans hA) hwidth

theorem endpoint_affine {h ε : ℝ} (hh : 0<h) (hε : 0≤ε) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) (hR0 : ∀ q ∈ Icc (-1:ℝ) 1,0≤R q) :
    FamilyConclusion h ε R leftTag (endpointFeet R ε) := by
  apply assemble hh R leftTag (endpointFeet R ε)
  · intro N i
    exact isCompact_endpointFootprint _ _ _ _
  · intro N hN q hq ρ hρ x hx
    obtain ⟨i,hi⟩ := RadialRiemann.exists_cell hN hq
    have hs := point_succ (-1) 1 N i
    refine ⟨i,?_⟩
    apply quadratic_mem_endpoint hε (step_pos (by norm_num) hN).le hx
    · change 0≤q-RadialRiemann.point (-1) 1 N i
      linarith [hi.1]
    · change q-RadialRiemann.point (-1) 1 N i ≤ step (-1) 1 N
      linarith [hi.2]
    · exact hρ.1
    · exact hρ.2.trans (le_capMax (by norm_num) hR hi)
  · rw [physicalCost_eq]
    have ht := RadialFootprints.affineFootprint_area_sum_tendsto (by norm_num : (-1:ℝ)<1)
      hR (weight_continuous h ε).continuousOn hR0 (by positivity : 0≤2*ε)
      (by linarith : (2*ε)/2≤3*ε) leftTag
      (fun N i => leftTag N i + step (-1) 1 N/2) leftTag_mem
    simpa only [endpointFeet,endpointFootprint_eq_affine,affineFootprint_eq_radial] using ht

theorem canonical_footprint_finite : Statement := by
  intro h ε hh hε R hR hR0
  exact ⟨fun _ _ hA hB tag htag => absolute_arbitrary hh hε hR hR0 hA hB tag htag,
    fun _ _ hA hB => absolute_midpoint hh hε hR hR0 hA hB,
    fun _ _ hA hB hw => affine_midpoint hh hε hR hR0 hA hB hw,
    endpoint_affine hh hε hR hR0⟩

end CylinderCovering.CanonicalFootprintFinite

end

end OAI
