import OAI.Geometry.CylinderCovering.Physical.TrianglesDefinitions
import OAI.Geometry.CylinderCovering.Physical.Finite

namespace OAI

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
noncomputable section
namespace RadialPhysical.ExplicitTriangles
open CylinderCovering PhysicalFiniteProof

variable (centered : Bool) (b eta : ℝ) (hb : 0 < b) (T : ℝ → ℝ)
  (hT : ContinuousOn T (Icc (-b) b))
  (hT0 : ∀ s ∈ Icc (-b) b, 0 ≤ T s)

lemma upper_scalarBound :
    RadialSweep.scalarBound (upperData centered b eta hb T hT hT0) = |eta| := by
  unfold RadialSweep.scalarBound
  change sSup ((fun _ : ℝ => |-eta|) '' Icc (-b) b) = |eta|
  have him : ((fun _ : ℝ => |-eta|) '' Icc (-b) b) = {|eta|} := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      simp
    · rintro rfl
      exact ⟨0, ⟨by linarith, by linarith⟩, abs_neg eta⟩
  rw [him, csSup_singleton]

lemma lower_scalarBound :
    RadialSweep.scalarBound (lowerData centered b eta hb T hT hT0) = |eta| := by
  unfold RadialSweep.scalarBound
  change sSup ((fun _ : ℝ => |eta|) '' Icc (-b) b) = |eta|
  have him : ((fun _ : ℝ => |eta|) '' Icc (-b) b) = {|eta|} := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      rfl
    · rintro rfl
      exact ⟨0, ⟨by linarith, by linarith⟩, rfl⟩
  rw [him, csSup_singleton]

lemma upper_error :
    RadialSweep.radialError (upperData centered b eta hb T hT hT0) =
      error centered b eta := by
  unfold RadialSweep.radialError
  rw [upper_scalarBound]
  rfl

lemma lower_error :
    RadialSweep.radialError (lowerData centered b eta hb T hT hT0) =
      error centered b eta := by
  unfold RadialSweep.radialError
  rw [lower_scalarBound]
  rfl

lemma upper_coordinateMap (p : ℝ × ℝ) :
    RadialSweep.coordinateMap (upperData centered b eta hb T hT hT0) p =
      upperIntercept b p := by
  ext i
  fin_cases i <;> simp [RadialSweep.coordinateMap, upperData, upperIntercept,
    point, RadialPairedSweep.point]
  ring

lemma lower_coordinateMap (p : ℝ × ℝ) :
    RadialSweep.coordinateMap (lowerData centered b eta hb T hT hT0) p =
      lowerIntercept centered b p := by
  cases centered <;> ext i <;>
    fin_cases i <;> simp [RadialSweep.coordinateMap, lowerData, lowerIntercept,
    point, RadialPairedSweep.point] <;> ring

lemma upper_vertices (N : ℕ) (i : Fin N) :
    RadialSweep.frozenVertices (upperData centered b eta hb T hT hT0) N i =
      upperVertices centered b eta T N i := by
  unfold RadialSweep.frozenVertices
  simp only [RadialSweep.leftTip, RadialSweep.rightEdge, RadialSweep.collar,
    upper_error, RadialSweep.midpoint]
  change ![_, _, _] = _
  funext j
  fin_cases j <;>
    change RadialSweep.coordinateMap (upperData centered b eta hb T hT hT0) _ =
      upperIntercept b _
  all_goals
    rw [upper_coordinateMap]
    rfl

lemma lower_vertices (N : ℕ) (i : Fin N) :
    RadialSweep.frozenVertices (lowerData centered b eta hb T hT hT0) N i =
      lowerVertices centered b eta T N i := by
  unfold RadialSweep.frozenVertices
  simp only [RadialSweep.leftTip, RadialSweep.rightEdge, RadialSweep.collar,
    lower_error, RadialSweep.midpoint]
  change ![_, _, _] = _
  funext j
  fin_cases j <;>
    change RadialSweep.coordinateMap (lowerData centered b eta hb T hT hT0) _ =
      lowerIntercept centered b _
  all_goals
    rw [lower_coordinateMap]
    rfl

lemma upper_base (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    RadialSweep.frozenBase (upperData centered b eta hb T hT hT0) N tag i =
      upperBase centered b eta T N tag i := by
  unfold RadialSweep.frozenBase RadialSweep.frozenTriangle upperBase
  rw [upperData_direction, upper_vertices]

lemma lower_base (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    RadialSweep.frozenBase (lowerData centered b eta hb T hT hT0) N tag i =
      lowerBase centered b eta T N tag i := by
  unfold RadialSweep.frozenBase RadialSweep.frozenTriangle lowerBase
  rw [lowerData_direction, lower_vertices]

lemma upper_speed (s : ℝ) :
    ‖(upperData centered b eta hb T hT hT0).w s‖^2 =
      eta^2 * ((s^2+b^2)^2/4 + height b^2*s^2) := by
  have hv : (upperData centered b eta hb T hT hT0).w s =
      RadialPairedSweep.point 0 (-eta/2*(s^2+b^2)) (height b*eta*s) := by
    change (-eta/2*(s^2+b^2)) • RadialPairedSweep.point 0 1 0 +
      (height b*eta*s) • RadialPairedSweep.point 0 0 1 = _
    ext i
    fin_cases i <;> simp [RadialPairedSweep.point]
  rw [hv, RadialPairedSweep.point_norm_sq]
  ring

lemma lower_speed (s : ℝ) :
    ‖(lowerData centered b eta hb T hT hT0).w s‖^2 =
      eta^2 * ((s^2+b^2)^2/4 + height b^2*s^2) := by
  have hv : (lowerData centered b eta hb T hT hT0).w s =
      RadialPairedSweep.point (eta/2*(s^2+b^2)) 0 (height b*eta*s) := by
    change (eta/2*(s^2+b^2)) • RadialPairedSweep.point 1 0 0 +
      (height b*eta*s) • RadialPairedSweep.point 0 0 1 = _
    ext i
    fin_cases i <;> simp [RadialPairedSweep.point]
  rw [hv, RadialPairedSweep.point_norm_sq]
  ring

lemma upper_area (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    RadialSweep.frozenArea (upperData centered b eta hb T hT hT0) N tag i =
      localArea centered b eta T N tag i := by
  unfold RadialSweep.frozenArea RadialSweep.collar
  rw [upperData_kappa, upper_error, upper_speed]
  change height b * RadialRiemann.step (-b) b N *
    (RadialRiemann.capMax T (-b) b N i +
      (error centered b eta + (3*error centered b eta+1))*RadialRiemann.step (-b) b N)^2 /
      (2*Real.sqrt (1+eta^2*((tag i^2+b^2)^2/4+height b^2*tag i^2))) = _
  unfold localArea
  ring

lemma lower_area (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    RadialSweep.frozenArea (lowerData centered b eta hb T hT hT0) N tag i =
      localArea centered b eta T N tag i := by
  unfold RadialSweep.frozenArea RadialSweep.collar
  rw [lowerData_kappa, lower_error, lower_speed]
  change height b * RadialRiemann.step (-b) b N *
    (RadialRiemann.capMax T (-b) b N i +
      (error centered b eta + (3*error centered b eta+1))*RadialRiemann.step (-b) b N)^2 /
      (2*Real.sqrt (1+eta^2*((tag i^2+b^2)^2/4+height b^2*tag i^2))) = _
  unfold localArea
  ring

def upperCylinder (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) (i : Fin N) :
    TriangularCovering.TriCylinder :=
  RadialSweep.frozenCylinder (upperData centered b eta hb T hT hT0) N tag htag i

def lowerCylinder (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) (i : Fin N) :
    TriangularCovering.TriCylinder :=
  RadialSweep.frozenCylinder (lowerData centered b eta hb T hT hT0) N tag htag i

theorem upperCylinder_axis (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) (i : Fin N) :
    (upperCylinder centered b eta hb T hT hT0 N tag htag i).axis =
      upperPhysicalAxis b eta (tag i) :=
  upperData_direction centered b eta hb T hT hT0 (tag i)

theorem lowerCylinder_axis (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) (i : Fin N) :
    (lowerCylinder centered b eta hb T hT hT0 N tag htag i).axis =
      lowerPhysicalAxis b eta (tag i) :=
  lowerData_direction centered b eta hb T hT hT0 (tag i)

theorem upperCylinder_base (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) (i : Fin N) :
    (upperCylinder centered b eta hb T hT hT0 N tag htag i).base =
      upperBase centered b eta T N tag i :=
  upper_base centered b eta hb T hT hT0 N tag i

theorem lowerCylinder_base (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) (i : Fin N) :
    (lowerCylinder centered b eta hb T hT hT0 N tag htag i).base =
      lowerBase centered b eta T N tag i :=
  lower_base centered b eta hb T hT hT0 N tag i

theorem upperCylinder_area (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) (i : Fin N) :
    TriangularCovering.area
      (upperCylinder centered b eta hb T hT hT0 N tag htag i).base =
      localArea centered b eta T N tag i := by
  exact (RadialSweep.frozenCylinder_area
    (upperData centered b eta hb T hT hT0) N tag htag i).trans
    (upper_area centered b eta hb T hT hT0 N tag i)

theorem lowerCylinder_area (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) (i : Fin N) :
    TriangularCovering.area
      (lowerCylinder centered b eta hb T hT hT0 N tag htag i).base =
      localArea centered b eta T N tag i := by
  exact (RadialSweep.frozenCylinder_area
    (lowerData centered b eta hb T hT hT0) N tag htag i).trans
    (lower_area centered b eta hb T hT hT0 N tag i)

theorem upper_actual_enclosure (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) (i : Fin N) :
    upperPhysicalBase centered b eta T N tag i ⊆
      (upperCylinder centered b eta hb T hT hT0 N tag htag i).base := by
  rw [upperCylinder_base, ← upper_base centered b eta hb T hT hT0,
    ← upperData_actualBase centered b eta hb T hT hT0]
  exact RadialSweep.actualBase_subset_frozenBase _ tag htag i

theorem lower_actual_enclosure (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) (i : Fin N) :
    lowerPhysicalBase centered b eta T N tag i ⊆
      (lowerCylinder centered b eta hb T hT hT0 N tag htag i).base := by
  rw [lowerCylinder_base, ← lower_base centered b eta hb T hT hT0,
    ← lowerData_actualBase centered b eta hb T hT hT0]
  exact RadialSweep.actualBase_subset_frozenBase _ tag htag i

theorem upper_cover {N : ℕ} (hN : 0 < N) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) :
    ∀ z ∈ upperSweepOn centered b eta T (Icc (-b) b),
      ∃ i : Fin N, z ∈ (upperCylinder centered b eta hb T hT hT0 N tag htag i).carrier := by
  intro z hz
  rw [← upperData_sweep centered b eta hb T hT hT0,
    RadialSweep.sweep_eq_iUnion_localSweep _ hN] at hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  exact ⟨i, RadialSweep.localSweep_mem_frozenCylinder _ tag htag i hi⟩

theorem lower_cover {N : ℕ} (hN : 0 < N) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) :
    ∀ z ∈ lowerSweepOn centered b eta T (Icc (-b) b),
      ∃ i : Fin N, z ∈ (lowerCylinder centered b eta hb T hT hT0 N tag htag i).carrier := by
  intro z hz
  rw [← lowerData_sweep centered b eta hb T hT hT0,
    RadialSweep.sweep_eq_iUnion_localSweep _ hN] at hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  exact ⟨i, RadialSweep.localSweep_mem_frozenCylinder _ tag htag i hi⟩

theorem upper_total_tendsto (tag : (N : ℕ) → Fin N → ℝ)
    (htag : ∀ N, RadialRiemann.IsTagged (-b) b N (tag N)) :
    Tendsto (fun N => TriangularCovering.totalArea
      (upperCylinder centered b eta hb T hT hT0 N (tag N) (htag N)))
      atTop (𝓝 (scaledCost b eta T / 2)) := by
  have h := RadialSweep.frozenArea_tendsto
    (upperData centered b eta hb T hT hT0) tag htag
  rw [upperData_weightedArea] at h
  convert h using 1
  funext N
  apply Finset.sum_congr rfl
  intro i _
  exact RadialSweep.frozenCylinder_area _ N (tag N) (htag N) i

theorem lower_total_tendsto (tag : (N : ℕ) → Fin N → ℝ)
    (htag : ∀ N, RadialRiemann.IsTagged (-b) b N (tag N)) :
    Tendsto (fun N => TriangularCovering.totalArea
      (lowerCylinder centered b eta hb T hT hT0 N (tag N) (htag N)))
      atTop (𝓝 (scaledCost b eta T / 2)) := by
  have h := RadialSweep.frozenArea_tendsto
    (lowerData centered b eta hb T hT hT0) tag htag
  rw [lowerData_weightedArea] at h
  convert h using 1
  funext N
  apply Finset.sum_congr rfl
  intro i _
  exact RadialSweep.frozenCylinder_area _ N (tag N) (htag N) i

theorem total_tendsto (tagU tagL : (N : ℕ) → Fin N → ℝ)
    (htagU : ∀ N, RadialRiemann.IsTagged (-b) b N (tagU N))
    (htagL : ∀ N, RadialRiemann.IsTagged (-b) b N (tagL N)) :
    Tendsto (fun N => TriangularCovering.totalArea
      (upperCylinder centered b eta hb T hT hT0 N (tagU N) (htagU N)) +
      TriangularCovering.totalArea
      (lowerCylinder centered b eta hb T hT hT0 N (tagL N) (htagL N)))
      atTop (𝓝 (scaledCost b eta T)) := by
  simpa only [add_halves] using
    (upper_total_tendsto centered b eta hb T hT hT0 tagU htagU).add
      (lower_total_tendsto centered b eta hb T hT hT0 tagL htagL)

include hb hT hT0 in

theorem localArea_pos (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    0 < localArea centered b eta T N tag i := by
  have hinterval : -b < b := by linarith
  have hd := RadialRiemann.step_pos hinterval (Nat.zero_lt_of_lt i.isLt)
  have hcap := RadialRiemann.capMax_nonneg hinterval hT hT0 i
  have hh : 0 < height b := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hb
  have hA : 0 ≤ error centered b eta := by
    unfold error axialBound
    cases centered <;> simp <;> positivity
  have hwidth : 0 < RadialRiemann.capMax T (-b) b N i +
      (4 * error centered b eta + 1) * RadialRiemann.step (-b) b N := by positivity
  unfold localArea
  exact div_pos (mul_pos (mul_pos hh hd) (sq_pos_of_pos hwidth))
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by positivity)))

theorem physical_triangle_construction : ConstructionStatement := by
  intro centered b eta hb T hT hT0 tagU tagL htagU htagL
  refine ⟨(fun N => upperCylinder centered b eta hb T hT hT0 N (tagU N) (htagU N)),
    (fun N => lowerCylinder centered b eta hb T hT hT0 N (tagL N) (htagL N)), ?_, ?_, ?_⟩
  · intro N i
    exact ⟨upperCylinder_axis centered b eta hb T hT hT0 N (tagU N) (htagU N) i,
      lowerCylinder_axis centered b eta hb T hT hT0 N (tagL N) (htagL N) i,
      upperCylinder_base centered b eta hb T hT hT0 N (tagU N) (htagU N) i,
      lowerCylinder_base centered b eta hb T hT hT0 N (tagL N) (htagL N) i,
      upperCylinder_area centered b eta hb T hT hT0 N (tagU N) (htagU N) i,
      lowerCylinder_area centered b eta hb T hT hT0 N (tagL N) (htagL N) i,
      upper_actual_enclosure centered b eta hb T hT hT0 N (tagU N) (htagU N) i,
      lower_actual_enclosure centered b eta hb T hT hT0 N (tagL N) (htagL N) i⟩
  · intro N hN
    exact ⟨upper_cover centered b eta hb T hT hT0 hN (tagU N) (htagU N),
      lower_cover centered b eta hb T hT hT0 hN (tagL N) (htagL N)⟩
  · exact total_tendsto centered b eta hb T hT hT0 tagU tagL htagU htagL

include hb hT hT0 in

theorem upperActual_area_le (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) (i : Fin N) :
    TriangularCovering.area (upperPhysicalBase centered b eta T N tag i) ≤
      localArea centered b eta T N tag i := by
  have h := measureReal_mono
    (upper_actual_enclosure centered b eta hb T hT hT0 N tag htag i)
    (upperCylinder centered b eta hb T hT hT0 N tag htag i).finite_area
  change TriangularCovering.area _ ≤ TriangularCovering.area _ at h
  rwa [upperCylinder_area] at h

include hb hT hT0 in

theorem lowerActual_area_le (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-b) b N tag) (i : Fin N) :
    TriangularCovering.area (lowerPhysicalBase centered b eta T N tag i) ≤
      localArea centered b eta T N tag i := by
  have h := measureReal_mono
    (lower_actual_enclosure centered b eta hb T hT hT0 N tag htag i)
    (lowerCylinder centered b eta hb T hT hT0 N tag htag i).finite_area
  change TriangularCovering.area _ ≤ TriangularCovering.area _ at h
  rwa [lowerCylinder_area] at h

include hb hT hT0 in

theorem actualCost_le_formula (N : ℕ) (tagU tagL : Fin N → ℝ)
    (htagU : RadialRiemann.IsTagged (-b) b N tagU)
    (htagL : RadialRiemann.IsTagged (-b) b N tagL) :
    physicalActualCost centered b eta T N tagU tagL ≤
      (∑ i : Fin N, localArea centered b eta T N tagU i) +
      (∑ i : Fin N, localArea centered b eta T N tagL i) := by
  apply add_le_add
  · exact Finset.sum_le_sum fun i _ =>
      upperActual_area_le centered b eta hb T hT hT0 N tagU htagU i
  · exact Finset.sum_le_sum fun i _ =>
      lowerActual_area_le centered b eta hb T hT hT0 N tagL htagL i

end RadialPhysical.ExplicitTriangles

end

end OAI
