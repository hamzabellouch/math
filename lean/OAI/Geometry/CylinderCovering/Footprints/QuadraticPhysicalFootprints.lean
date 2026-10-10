import OAI.Geometry.CylinderCovering.Footprints.QuadraticPhysicalFootprintsDefinitions
import OAI.Geometry.CylinderCovering.Footprints.Footprints
import OAI.Geometry.CylinderCovering.Footprints.Certificates
import OAI.Geometry.CylinderCovering.Physical.PhysicalFootprints
import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set

namespace CylinderCovering.Footprints

def physicalPairEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  ((MeasurableEquiv.subLeft (1:ℝ)).prodCongr (MeasurableEquiv.refl ℝ)).trans
    MeasurableEquiv.prodComm

@[simp] theorem physicalPairEquiv_apply (p : ℝ × ℝ) :
    physicalPairEquiv p = (p.2,1-p.1) := rfl

theorem physicalPair_measurePreserving : MeasurePreserving physicalPairEquiv volume volume := by
  have hp : MeasurePreserving (Prod.map (fun u : ℝ => 1-u) (id : ℝ → ℝ))
      (volume.prod volume) (volume.prod volume) :=
    (volume.measurePreserving_sub_left (1:ℝ)).prod (MeasurePreserving.id volume)
  exact Measure.measurePreserving_swap.comp hp

def physicalChartEquiv : (ℝ × ℝ) ≃ᵐ RuledApproximation.Plane :=
  physicalPairEquiv.trans RuledApproximation.pairPlaneEquiv

@[simp] theorem physicalChartEquiv_apply (p : ℝ × ℝ) :
    physicalChartEquiv p = physicalChart p := rfl

theorem physicalChart_measurePreserving : MeasurePreserving physicalChartEquiv volume volume :=
  RuledApproximation.pairPlane_measurePreserving.comp physicalPair_measurePreserving

theorem physicalLabelSet_volume (F : Set (ℝ × ℝ)) :
    volume (physicalLabelSet F) = volume F := by
  have hp := physicalChart_measurePreserving.measure_preimage_equiv (physicalLabelSet F)
  have he : physicalChartEquiv ⁻¹' physicalLabelSet F = F := by
    change physicalChartEquiv ⁻¹' (physicalChartEquiv '' F) = F
    exact Set.preimage_image_eq F physicalChartEquiv.injective
  rw [he] at hp
  exact hp.symm

theorem physicalLabelSet_realVolume (F : Set (ℝ × ℝ)) :
    volume.real (physicalLabelSet F) = volume.real F := by
  simp only [measureReal_def, physicalLabelSet_volume]

theorem physicalChart_continuous : Continuous physicalChart := by
  unfold physicalChart RuledApproximation.vec2
  fun_prop

theorem physicalLabelSet_compact {F : Set (ℝ × ℝ)} (hF : IsCompact F) :
    IsCompact (physicalLabelSet F) := hF.image physicalChart_continuous

theorem projected_footprint_area {h : ℝ} (hh : 0 < h) (ε c : ℝ) (F : Set (ℝ × ℝ)) :
    (RuledApproximation.projectedCylinder h (quadraticVelocity ε c) (physicalLabelSet F)).area =
      h * volume.real F /
        Real.sqrt (1+ε^2*(((1+c^2)/2)^2+h^2*c^2)) := by
  rw [RuledApproximation.projectedCylinder_area hh, physicalLabelSet_realVolume]
  unfold RuledApproximation.physicalWeight quadraticVelocity
  simp only [RuledApproximation.vec2_apply_zero, RuledApproximation.vec2_apply_one]
  have he : 1 + (-ε * ((1 + c^2) / 2))^2 + h^2 * (ε*c)^2 =
      1 + ε^2 * (((1+c^2)/2)^2+h^2*c^2) := by ring
  rw [he]
  ring

theorem quadraticSweepPoint_mem_projected {h ε x q c ρ : ℝ} {F : Set (ℝ × ℝ)}
    (hF : quadraticIntercept ε x q c ρ ∈ F) :
    quadraticSweepPoint h ε x q ρ ∈
      (RuledApproximation.projectedCylinder h (quadraticVelocity ε c) (physicalLabelSet F)).carrier := by
  rw [RuledApproximation.projectedCylinder_mem_iff]
  refine ⟨physicalChart (quadraticIntercept ε x q c ρ), ⟨_, hF, rfl⟩, x, ?_⟩
  ext i
  fin_cases i <;>
    simp [quadraticSweepPoint, physicalChart, quadraticIntercept, quadraticVelocity,
      RuledApproximation.planeEmbedding, RuledApproximation.physicalDirection,
      RuledApproximation.vec2, RuledApproximation.vec3] <;> ring

def physicalChartAffine : (ℝ × ℝ) →ᵃ[ℝ] RuledApproximation.Plane where
  toFun := physicalChart
  linear :=
    { toFun := fun p => RuledApproximation.vec2 p.2 (-p.1)
      map_add' := by intro p q; ext i; fin_cases i <;> simp [RuledApproximation.vec2]; ring
      map_smul' := by intro t p; ext i; fin_cases i <;> simp [RuledApproximation.vec2] }
  map_vadd' := by
    intro p v
    ext i
    fin_cases i <;> simp [physicalChart, RuledApproximation.vec2]
    ring

def projectedFootprintChart (h ε c : ℝ) : (ℝ × ℝ) →ᵃ[ℝ]
    ((Submodule.span ℝ ({RuledApproximation.physicalUnit h (quadraticVelocity ε c)} :
      Set RuledApproximation.Space))ᗮ) :=
  (RuledApproximation.perpendicularProjection h (quadraticVelocity ε c)).toAffineMap.comp
    physicalChartAffine

theorem projectedFootprintChart_injective {h : ℝ} (hh : 0 < h) (ε c : ℝ) :
    Function.Injective (projectedFootprintChart h ε c) :=
  (RuledApproximation.perpendicularProjection_injective hh _).comp physicalChartEquiv.injective

theorem projected_footprint_base (h ε c : ℝ) (F : Set (ℝ × ℝ)) :
    (RuledApproximation.projectedCylinder h (quadraticVelocity ε c) (physicalLabelSet F)).base =
      projectedFootprintChart h ε c '' F := by
  change RuledApproximation.perpendicularProjection h (quadraticVelocity ε c) ''
    (physicalChart '' F) = _
  rw [Set.image_image]
  rfl

theorem projected_footprint_compact (h ε c : ℝ) {F : Set (ℝ × ℝ)} (hF : IsCompact F) :
    IsCompact (RuledApproximation.projectedCylinder h (quadraticVelocity ε c)
      (physicalLabelSet F)).base := by
  change IsCompact (RuledApproximation.perpendicularProjection h (quadraticVelocity ε c) ''
    physicalLabelSet F)
  exact (physicalLabelSet_compact hF).image
    (RuledApproximation.perpendicularProjection h (quadraticVelocity ε c)).continuous_of_finiteDimensional

theorem projected_footprint_convex (h ε c : ℝ) {F : Set (ℝ × ℝ)} (hF : Convex ℝ F) :
    Convex ℝ (RuledApproximation.projectedCylinder h (quadraticVelocity ε c)
      (physicalLabelSet F)).base := by
  rw [projected_footprint_base]
  exact hF.affine_image (projectedFootprintChart h ε c)

theorem projected_affine_triangle {h m M d A ε c : ℝ}
    (hh : 0 < h) (hd : 0 < d) (hlength : 0 < M+2*A*d) :
    let C := RuledApproximation.projectedCylinder h (quadraticVelocity ε c)
      (physicalLabelSet (affineFootprint m M d A (A/2)))
    ∃ v : Fin 3 → ((Submodule.span ℝ ({C.axis} : Set RuledApproximation.Space))ᗮ),
      AffineIndependent ℝ v ∧ C.base = convexHull ℝ (range v) := by
  let f := projectedFootprintChart h ε c
  refine ⟨f ∘ RadialTriangle.vertices (-A*d) (M+A*d) m d, ?_, ?_⟩
  · exact (affineFootprint_half_vertices_independent hd hlength).map' f
      (projectedFootprintChart_injective hh ε c)
  · rw [projected_footprint_base, affineFootprint_half_eq_convexHull hd hlength,
      (projectedFootprintChart h ε c).image_convexHull, ← Set.range_comp]
    rfl

theorem projected_footprint_area_sqrtTwo (ε c : ℝ) (F : Set (ℝ × ℝ)) :
    (RuledApproximation.projectedCylinder (Real.sqrt 2) (quadraticVelocity ε c)
      (physicalLabelSet F)).area =
      Real.sqrt 2 * volume.real F /
        Real.sqrt (1+ε^2*(((1+c^2)/2)^2+2*c^2)) := by
  rw [projected_footprint_area (Real.sqrt_pos.2 (by norm_num))]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem projected_footprint_convex_iff {h : ℝ} (hh : 0 < h) (ε c : ℝ)
    (F : Set (ℝ × ℝ)) :
    Convex ℝ (RuledApproximation.projectedCylinder h (quadraticVelocity ε c)
      (physicalLabelSet F)).base ↔ Convex ℝ F := by
  rw [projected_footprint_base]
  constructor
  · intro hF
    have hp := hF.affine_preimage (projectedFootprintChart h ε c)
    rwa [Set.preimage_image_eq F (projectedFootprintChart_injective hh ε c)] at hp
  · exact fun hF => hF.affine_image (projectedFootprintChart h ε c)

theorem projected_footprint_ambient_base (h ε c : ℝ) (F : Set (ℝ × ℝ)) :
    Subtype.val '' (RuledApproximation.projectedCylinder h (quadraticVelocity ε c)
      (physicalLabelSet F)).base = physicalFootprintProjection h ε c '' F := by
  change Subtype.val '' (RuledApproximation.perpendicularProjection h (quadraticVelocity ε c) ''
    (physicalChart '' F)) = _
  rw [Set.image_image, Set.image_image]
  rfl

theorem physicalFootprintRealization : PhysicalFootprintRealization := by
  intro h ε c F hh
  refine ⟨RuledApproximation.projectedCylinder h (quadraticVelocity ε c)
    (physicalLabelSet F), rfl, projected_footprint_ambient_base h ε c F,
    projected_footprint_area hh ε c F, ?_, projected_footprint_convex_iff hh ε c F, ?_, ?_⟩
  · exact projected_footprint_compact h ε c
  · intro x q ρ hF
    exact quadraticSweepPoint_mem_projected hF
  · exact ⟨projectedFootprintChart h ε c, projectedFootprintChart_injective hh ε c,
      projected_footprint_base h ε c F, fun _ => rfl⟩

theorem physicalFootprintCertificates : PhysicalFootprintCertificates :=
  ⟨localFootprintCertificates, physicalFootprintRealization⟩

theorem quadratic_footprintCylinder_eq (h ε c : ℝ) (F : Set (ℝ × ℝ)) :
    RuledApproximation.projectedCylinder h (quadraticVelocity ε c) (physicalLabelSet F) =
      PhysicalFootprints.footprintCylinder h (quadraticVelocity ε c) F := rfl

theorem physical_absolute_contains {h ε x q c ρ m M d A B : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q-c| ≤ d) (hqm : |q-m| ≤ d/2) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hA : 2*ε ≤ A) (hB : ε ≤ B) :
    quadraticSweepPoint h ε x q ρ ∈
      (PhysicalFootprints.footprintCylinder h (quadraticVelocity ε c)
        (absoluteFootprint m M d A B)).carrier :=
  quadraticSweepPoint_mem_projected
    (quadratic_mem_absolute hε hd hx hqc hqm hρ hρM hA hB)

theorem physical_midpoint_absolute_contains {h ε x q c ρ M d A B : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q-c| ≤ d/2) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hA : ε ≤ A) (hB : ε/4 ≤ B) :
    quadraticSweepPoint h ε x q ρ ∈
      (PhysicalFootprints.footprintCylinder h (quadraticVelocity ε c)
        (absoluteFootprint c M d A B)).carrier :=
  quadraticSweepPoint_mem_projected
    (quadratic_mem_absolute_midpoint hε hd hx hqc hρ hρM hA hB)

theorem physical_midpoint_affine_contains {h ε x q c ρ M d A B : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc : |q-c| ≤ d/2) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hA : ε ≤ A) (hB : 3*ε/4 ≤ B) :
    quadraticSweepPoint h ε x q ρ ∈
      (PhysicalFootprints.footprintCylinder h (quadraticVelocity ε c)
        (affineFootprint c M d A B)).carrier :=
  quadraticSweepPoint_mem_projected
    (quadratic_mem_affine_midpoint hε hd hx hqc hρ hρM hA hB)

theorem physical_endpoint_contains {h ε x q c ρ M d : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hx : |x| ≤ 2)
    (hqc0 : 0 ≤ q-c) (hqc : q-c ≤ d) (hρ : 0 ≤ ρ) (hρM : ρ ≤ M) :
    quadraticSweepPoint h ε x q ρ ∈
      (PhysicalFootprints.footprintCylinder h (quadraticVelocity ε c)
        (endpointFootprint c M d ε)).carrier :=
  quadraticSweepPoint_mem_projected (quadratic_mem_endpoint hε hd hx hqc0 hqc hρ hρM)

end CylinderCovering.Footprints

end

end OAI
