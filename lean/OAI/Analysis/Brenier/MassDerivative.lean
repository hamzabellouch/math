import OAI.Analysis.Brenier.CanonicalLaplacian
import OAI.Analysis.Brenier.LineDerivative

namespace OAI

/-! The actual normalized cell-mass line derivative with canonical coefficients. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Compact convex positive-cell geometry alone gives the normalized mass
derivative. The auxiliary interior tie points are chosen internally. -/
theorem hasDerivAt_uniformMass_line
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y v : ι → E d) (c r : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0) (i : ι) :
    HasDerivAt (fun t : ℝ => (uniformMeasure K).real
      (closedCell K (fun j => y j + t • v j) (fun j => c j + t * r j) i))
      (∑ j, (
        (IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)
          (closedCell K y c i ∩ closedCell K y c j)).toReal /
            ((volume K).toReal * ‖y i - y j‖) * (r i - r j) +
          ⟪faceMoment K y c i j, v i - v j⟫)) 0 := by
  classical
  have hex : ∀ j, ∃ z : E d, j ≠ i →
      z ∈ interior K ∧ ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j := by
    intro j
    by_cases hji : j = i
    · exact ⟨0, fun h => (h hji).elim⟩
    · obtain ⟨z, hz, hzt⟩ := exists_equality_interior_of_positive_cells
        hρ hconv y c hy (Ne.symm hji) (hpos i) (hpos j)
      exact ⟨z, fun _ => ⟨hz, hzt⟩⟩
  choose z hz using hex
  have hd := PositiveCellFullDerivative.hasDerivAt_closedCell_integral
    hρ hK hconv y v c r hy hpos (fun _ => (1 : ℝ)) continuous_const i z
    (fun j hji => (hz j hji).1) (fun j hji => (hz j hji).2)
  have hd' := hasDerivAt_uniformMass_of_integral_one hK.isClosed
    (fun t j => y j + t • v j) (fun t j => c j + t * r j) i hd
  let D : ι → ℝ := fun j =>
    (IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)
      (closedCell K y c i ∩ closedCell K y c j)).toReal /
        ((volume K).toReal * ‖y i - y j‖) * (r i - r j) +
      ⟪faceMoment K y c i j, v i - v j⟫
  have hD : D i = 0 := by simp [D]
  have heq : (volume K).toReal⁻¹ *
      (∑ j ∈ Finset.univ.erase i,
        PositiveCellFullDerivative.faceVariation K y v c r (fun _ => 1) i j (z j)) =
        ∑ j, D j := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ j ∈ Finset.univ.erase i, D j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        exact PositiveCellFullDerivative.normalized_faceVariation_one hK y v c r
          (hy.ne hji.symm) (hz j hji).2
      _ = ∑ j, D j := by
        simpa only [hD, add_zero] using
          (Finset.sum_erase_add Finset.univ D (Finset.mem_univ i))
  rw [heq] at hd'
  simpa only [D] using hd'

end Problem358.CellGeometry

end

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace BigOperators
namespace Problem358.PositiveCellFullDerivative

open CellGeometry

/-- The stationary coordinate face derivative has exactly the canonical vector
coefficient and source-volume normalization. -/
theorem normalized_faceVariation_coordinate_stationary
    {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Set (E d)} (hK : IsCompact K) (y : ι → E d) (c q : ι → ℝ)
    {i j : ι} (hy : y i ≠ y j) {z : E d}
    (htie : ⟪z, y i⟫_ℝ + c i = ⟪z, y j⟫_ℝ + c j) (k : Fin d) :
    (volume K).toReal⁻¹ * faceVariation K y (fun _ => 0) c q (fun x => x k) i j z =
      (q i - q j) * faceMoment K y c i j k := by
  have hid : IntegrableOn (fun x : E d => x)
      (closedCell K y c i ∩ closedCell K y c j)
      (IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)) :=
    IntrinsicSurface.integrableOn_interfaceMeasure _ _ _ _
      ((isCompact_closedCell hK y c i).inter (isCompact_closedCell hK y c j))
      continuous_id.continuousOn
  rw [faceVariation_eq_intrinsic hK.isClosed y (fun _ => 0) c q (fun x => x k) hy htie]
  simp only [sub_self, inner_zero_left, add_zero]
  rw [integral_const_mul]
  unfold faceMoment
  rw [PiLp.smul_apply, CellVectorDerivative.integral_coordinate hid k]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Actual stationary-site moment differential with the canonical intrinsic
face moments. No directional derivative or face regularity premise remains. -/
theorem hasDerivAt_uniform_closedCell_moment_stationary
    {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c q : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0) (i : ι) :
    HasDerivAt (fun t : ℝ => ∫ x in
      closedCell K y (fun j => c j + t * q j) i, x ∂uniformMeasure K)
      (∑ j, (q i - q j) • faceMoment K y c i j) 0 := by
  classical
  have hex : ∀ j, ∃ z : E d, j ≠ i → z ∈ interior K ∧
      ⟪z, y i⟫_ℝ + c i = ⟪z, y j⟫_ℝ + c j := by
    intro j
    by_cases hji : j = i
    · exact ⟨0, fun h => (h hji).elim⟩
    · obtain ⟨z, hz, he⟩ := exists_equality_interior_of_positive_cells hρ hconv y c hy
        (Ne.symm hji) (hpos i) (hpos j)
      exact ⟨z, fun _ => ⟨hz, he⟩⟩
  choose z hz using hex
  have hd := hasDerivAt_uniform_closedCell_moment hρ hK hconv y (fun _ => 0) c q hy hpos
    i z (fun j hj => (hz j hj).1) (fun j hj => (hz j hj).2)
  have heq : (volume K).toReal⁻¹ • (WithLp.toLp 2 fun k : Fin d =>
      ∑ j ∈ Finset.univ.erase i, faceVariation K y (fun _ => 0) c q (fun x => x k) i j (z j)) =
      ∑ j, (q i - q j) • faceMoment K y c i j := by
    have hsum : (∑ j ∈ Finset.univ.erase i, (q i - q j) • faceMoment K y c i j) =
        ∑ j, (q i - q j) • faceMoment K y c i j := by
      simp
    rw [← hsum]
    apply PiLp.ext
    intro k
    change (volume K).toReal⁻¹ * (∑ j ∈ Finset.univ.erase i,
      faceVariation K y (fun _ => 0) c q (fun x => x k) i j (z j)) =
      (EuclideanSpace.proj k) (∑ j ∈ Finset.univ.erase i,
        (q i - q j) • faceMoment K y c i j)
    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact normalized_faceVariation_coordinate_stationary hK y c q
      (hy.ne (Finset.ne_of_mem_erase hj).symm) ((hz j (Finset.ne_of_mem_erase hj)).2) k
  rw [heq] at hd
  simpa only [smul_zero, add_zero] using hd

end Problem358.PositiveCellFullDerivative

end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual mass derivative as a bounded linear map in sites and intercepts. -/
def massLinearMap (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i : ι) :
    ((ι → E d) × (ι → ℝ)) →L[ℝ] ℝ :=
  FaceDerivative.cellLinearMap Finset.univ i (fun _ => 1)
    (PositiveFacet.canonicalFaceWeight K y c i) (faceMoment K y c i)

omit [DecidableEq ι] in
@[simp] theorem massLinearMap_apply (K : Set (E d))
    (y v : ι → E d) (c r : ι → ℝ) (i : ι) :
    massLinearMap K y c i (v, r) =
      ∑ j, (PositiveFacet.canonicalFaceWeight K y c i j * (r i - r j) +
        ⟪faceMoment K y c i j, v i - v j⟫) := by
  simp only [massLinearMap, FaceDerivative.cellLinearMap_apply, div_one, one_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm, real_inner_comm]

/-- Geometry supplies all directional derivatives of the true uniform masses. -/
theorem hasLineDerivAt_uniformMass
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0) (i : ι)
    (w : (ι → E d) × (ι → ℝ)) :
    HasLineDerivAt ℝ (fun p : (ι → E d) × (ι → ℝ) =>
      (uniformMeasure K).real (closedCell K p.1 p.2 i))
      (massLinearMap K y c i w) (y, c) w := by
  rcases w with ⟨v, r⟩
  rw [massLinearMap_apply]
  change HasDerivAt (fun t : ℝ => (uniformMeasure K).real
    (closedCell K (fun j => y j + t • v j) (fun j => c j + t * r j) i)) _ 0
  exact hasDerivAt_uniformMass_line hρ hK hconv y v c r hy hpos i

/-- Continuity of the true mass derivative in operator norm. -/
theorem continuousAt_massLinearMap
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0) (i : ι) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      massLinearMap K p.1 p.2 i) (y, c) := by
  unfold massLinearMap FaceDerivative.cellLinearMap
  apply tendsto_finsetSum Finset.univ
  intro j _
  exact (FaceDerivative.continuousAt_linearMap continuousAt_const
    (continuousAt_canonicalFaceWeight hρ hK hconv y c hy hpos i j)
    (continuousAt_faceMoment hρ hK hconv y c hy hpos i j)
    (by norm_num)).clm_comp continuousAt_const

/-- Distinct configurations with strictly positive actual cell masses. -/
def positiveMassConfigurations (K : Set (E d)) : Set ((ι → E d) × (ι → ℝ)) :=
  {p | Function.Injective p.1 ∧ ∀ i, 0 < (uniformMeasure K).real (closedCell K p.1 p.2 i)}

omit [Fintype ι] [DecidableEq ι] in
theorem nonzero_cellMass_of_positive {K : Set (E d)}
    {p : (ι → E d) × (ι → ℝ)} (hp : p ∈ positiveMassConfigurations K) (i : ι) :
    uniformMeasure K (closedCell K p.1 p.2 i) ≠ 0 := by
  intro h
  have hh := hp.2 i
  simp only [Measure.real, h, ENNReal.toReal_zero, lt_self_iff_false] at hh

/-- Joint C¹ regularity of the entire genuine normalized mass map, on its open
positive-cell locus. All face calculus hypotheses have been discharged. -/
theorem contDiffOn_uniformMassMap
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K) :
    ContDiffOn ℝ 1 (fun p : (ι → E d) × (ι → ℝ) =>
      fun i => (uniformMeasure K).real (closedCell K p.1 p.2 i))
      (positiveMassConfigurations K) := by
  apply contDiffOn_pi.mpr
  intro i
  apply Problem358.contDiffOn_one_of_continuousOn_lineDeriv
    (isOpen_distinct_positive_real_closedCell hK.measurableSet)
    (D := fun p => massLinearMap K p.1 p.2 i)
  · intro p hp
    exact hasLineDerivAt_uniformMass (uniformMeasure_absolutelyContinuous K)
      hK hconv p.1 p.2 hp.1 (nonzero_cellMass_of_positive hp) i
  · intro p hp
    exact (continuousAt_massLinearMap (uniformMeasure_absolutelyContinuous K)
      hK hconv p.1 p.2 hp.1 (nonzero_cellMass_of_positive hp) i).continuousWithinAt

/-- The pointwise C¹ form consumed by normalized implicit-function arguments. -/
theorem contDiffAt_uniformMassMap
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < (uniformMeasure K).real (closedCell K y c i)) :
    ContDiffAt ℝ 1 (fun p : (ι → E d) × (ι → ℝ) =>
      fun i => (uniformMeasure K).real (closedCell K p.1 p.2 i)) (y, c) :=
  (contDiffOn_uniformMassMap hK hconv (y, c) ⟨hy, hpos⟩).contDiffAt
    ((isOpen_distinct_positive_real_closedCell hK.measurableSet).mem_nhds ⟨hy, hpos⟩)

end Problem358.CellGeometry

end

end OAI
