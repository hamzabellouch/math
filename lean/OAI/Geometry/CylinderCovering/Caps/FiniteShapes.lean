import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Caps.TrapezoidShapes
import OAI.Geometry.CylinderCovering.Radial.Riemann

namespace OAI

noncomputable section
open Set
open scoped InnerProductSpace

namespace CylinderCovering.HalfheightFinite
open TriangularCovering

private theorem shape_height_pos : 0 < height := by unfold height; positivity

private theorem shape_ex_norm : ‖(!₂[1,0,0] : Space)‖ = 1 := by
  norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_succ]

private theorem shape_ey_norm : ‖(!₂[0,1,0] : Space)‖ = 1 := by
  norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_succ]

private theorem shape_first_independent :
    LinearIndependent ℝ (![(!₂[0,0,height] : Space), !₂[0,1/2,0]] : Fin 2 → Space) := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have := congrArg (fun z : Space => z 1) h
    norm_num at this
  · intro c h
    have hh := congrArg (fun z : Space => z 2) h
    simp at hh
    exact shape_height_pos.ne' hh.symm

private theorem shape_second_independent :
    LinearIndependent ℝ (![(!₂[0,0,-height] : Space), !₂[1/2,0,0]] : Fin 2 → Space) := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have := congrArg (fun z : Space => z 0) h
    norm_num at this
  · intro c h
    have hh := congrArg (fun z : Space => z 2) h
    simp at hh
    linarith [shape_height_pos]

def firstShapeChart (δ r : ℝ) : (ℝ × ℝ) →ᵃ[ℝ] Space :=
  RadialProjection.projectedCoordinateAffine (firstAxis δ r) 0
    !₂[0,0,height] !₂[0,1/2,0]

def secondShapeChart (δ r : ℝ) : (ℝ × ℝ) →ᵃ[ℝ] Space :=
  RadialProjection.projectedCoordinateAffine (secondAxis δ r) !₂[0,0,height]
    !₂[0,0,-height] !₂[1/2,0,0]

@[simp] theorem firstShapeChart_apply (δ r : ℝ) (p : ℝ × ℝ) :
    firstShapeChart δ r p = projection (firstAxis δ r) (firstFoot p) := by
  unfold firstShapeChart
  rw [RadialProjection.projectedCoordinateAffine_apply]
  congr 1
  ext i
  fin_cases i <;> simp [firstFoot] <;> ring

@[simp] theorem secondShapeChart_apply (δ r : ℝ) (p : ℝ × ℝ) :
    secondShapeChart δ r p = projection (secondAxis δ r) (secondFoot p) := by
  unfold secondShapeChart
  rw [RadialProjection.projectedCoordinateAffine_apply]
  congr 1
  ext i
  fin_cases i <;> simp [secondFoot] <;> ring

theorem firstShapeChart_injective (δ r : ℝ) : Function.Injective (firstShapeChart δ r) := by
  have haxis : firstAxis δ r = unit
      ((!₂[1,0,0] : Space) + !₂[0,δ*alpha r,2*height*δ*beta r]) := by
    have hraw : firstRaw δ r =
        (!₂[1,0,0] : Space) + !₂[0,δ*alpha r,2*height*δ*beta r] := by
      ext i
      fin_cases i <;> simp [firstRaw]
    simp only [firstAxis, TriangularCovering.unit, hraw]
  unfold firstShapeChart
  rw [haxis]
  exact RadialProjection.projectedCoordinateAffine_injective 0 shape_ex_norm
    (by simp [inner_coord]) (by simp [inner_coord]) (by simp [inner_coord])
    shape_first_independent

theorem secondShapeChart_injective (δ r : ℝ) : Function.Injective (secondShapeChart δ r) := by
  have haxis : secondAxis δ r = unit
      ((!₂[0,1,0] : Space) + !₂[-δ*alpha r,0,2*height*δ*beta r]) := by
    have hraw : secondRaw δ r =
        (!₂[0,1,0] : Space) + !₂[-δ*alpha r,0,2*height*δ*beta r] := by
      ext i
      fin_cases i <;> simp [secondRaw]
    simp only [secondAxis, TriangularCovering.unit, hraw]
  unfold secondShapeChart
  rw [haxis]
  exact RadialProjection.projectedCoordinateAffine_injective !₂[0,0,height] shape_ey_norm
    (by simp [inner_coord]) (by simp [inner_coord]) (by simp [inner_coord])
    shape_second_independent

theorem firstBase_eq_shapeChart (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) :
    firstBase δ R N i = firstShapeChart δ (midpoint N i) '' foot δ R N i := by
  simp only [firstBase, image_image, ← firstShapeChart_apply]

theorem secondBase_eq_shapeChart (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) :
    secondBase δ R N i = secondShapeChart δ (midpoint N i) '' foot δ R N i := by
  simp only [secondBase, image_image, ← secondShapeChart_apply]

theorem finite_base_trapezoids {δ : ℝ} (hδ : 0 < δ) (R : ℝ → ℝ)
    {N : ℕ} (hN : 0 < N) (i : Fin N) (hM : 0 ≤ maxCap R N i) :
    let v := RadialFootprints.halfheightVertices
      (halfwidth N) (collar δ N) (maxCap R N i) (midpoint N i)
    (firstBase δ R N i = convexHull ℝ (range (firstShapeChart δ (midpoint N i) ∘ v)) ∧
      Function.Injective (firstShapeChart δ (midpoint N i) ∘ v)) ∧
    (secondBase δ R N i = convexHull ℝ (range (secondShapeChart δ (midpoint N i) ∘ v)) ∧
      Function.Injective (secondShapeChart δ (midpoint N i) ∘ v)) := by
  have hρ : 0 < halfwidth N := by unfold halfwidth; positivity
  have he : 0 < collar δ N := by unfold collar; positivity
  have hshape := RadialFootprints.halfheightFootprint_eq_convexHull (midpoint N i) hρ he hM
  have hinj := RadialFootprints.halfheightVertices_injective (midpoint N i) hρ he hM
  dsimp only
  constructor
  · constructor
    · rw [firstBase_eq_shapeChart, foot, hshape,
        (firstShapeChart δ (midpoint N i)).image_convexHull, ← range_comp]
    · exact (firstShapeChart_injective δ (midpoint N i)).comp hinj
  · constructor
    · rw [secondBase_eq_shapeChart, foot, hshape,
        (secondShapeChart δ (midpoint N i)).image_convexHull, ← range_comp]
    · exact (secondShapeChart_injective δ (midpoint N i)).comp hinj

theorem cubic_maxCap_nonneg {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (i : Fin N) :
    0 ≤ maxCap (cubicCap δ) N i := by
  apply RadialRiemann.capMax_nonneg (by norm_num : (-1 : ℝ) < 1)
  · apply Continuous.continuousOn
    unfold cubicCap profile
    fun_prop
  · intro r hr
    dsimp [cubicCap, profile]
    positivity

theorem fractional_maxCap_nonneg {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (i : Fin N) :
    0 ≤ maxCap (fractionalCap δ) N i := by
  apply RadialRiemann.capMax_nonneg (by norm_num : (-1 : ℝ) < 1)
  · apply Continuous.continuousOn
    unfold fractionalCap profile
    fun_prop
  · intro r hr
    dsimp [fractionalCap, profile]
    positivity

theorem source_base_trapezoids {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 0 < N)
    (i : Fin N) :
    ∀ R ∈ ({cubicCap δ, fractionalCap δ} : Set (ℝ → ℝ)),
      ∃ v₁ v₂ : Fin 4 → Space,
        firstBase δ R N i = convexHull ℝ (range v₁) ∧
        secondBase δ R N i = convexHull ℝ (range v₂) ∧
        Function.Injective v₁ ∧ Function.Injective v₂ := by
  intro R hR
  have hM : 0 ≤ maxCap R N i := by
    simp only [mem_insert_iff, mem_singleton_iff] at hR
    rcases hR with rfl | rfl
    · exact cubic_maxCap_nonneg hδ i
    · exact fractional_maxCap_nonneg hδ i
  obtain ⟨⟨hfirst,hfirstinj⟩,⟨hsecond,hsecondinj⟩⟩ := finite_base_trapezoids hδ R hN i hM
  exact ⟨_,_,hfirst,hsecond,hfirstinj,hsecondinj⟩

end CylinderCovering.HalfheightFinite

end

end OAI
