import OAI.Geometry.HeilbronnTriangle.IntegerMatrixFibers
import OAI.Geometry.HeilbronnTriangle.IntegerPointLawTriples
import OAI.Geometry.HeilbronnTriangle.UniformFixedFiberCount

namespace OAI


noncomputable section
namespace Problem355.TypedFixedFiberCount

open Matrix IntegerSampling OrbitSampling IntegerMatrixEvents
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def orbitEvent (N h : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) : Finset IntMatrix :=
  (matrices N (samplingShift N)).filter (fun A =>
    Homogeneous.projectedDistinct (Homogeneous.integerColumn A 0)
      (Homogeneous.integerColumn A 1) (Homogeneous.integerColumn A 2) ∧
    (fun j i => (A i j : ZMod h)) ∈ orbitFinset (MainGroup h) C)

theorem orbitEvent_filter_det (N h : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ) :
    (orbitEvent N h C).filter (fun A => A.det = t) = fixedDetEvent N h C t := by
  ext A
  simp only [orbitEvent, fixedDetEvent, fixedDetProperty, Finset.mem_filter]
  tauto

theorem orbitEvent_reduction {N h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {A : IntMatrix}
    (hA : A ∈ orbitEvent N h C) :
    A.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit (transpose C) := by
  exact fixedDetProperty_reduction
    (show fixedDetProperty h C A.det A from ⟨(Finset.mem_filter.mp hA).2.1,
      (Finset.mem_filter.mp hA).2.2, rfl⟩)

theorem orbitEvent_box {N h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {A : IntMatrix}
    (hA : A ∈ orbitEvent N h C) (j : Fin 3) :
    Homogeneous.InBox (N : ℝ) (fun i => (A i j : ℝ)) := by
  have hAm := (Finset.mem_filter.mp hA).1
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hAm
  exact IntegerPointLaw.column_inBox (x j)

theorem orbitEvent_projections {N h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {A : IntMatrix}
    (hA : A ∈ orbitEvent N h C) (i j : Fin 3) (hij : i ≠ j) :
    Homogeneous.project (Homogeneous.integerColumn A i) ≠
      Homogeneous.project (Homogeneous.integerColumn A j) := by
  apply fixedDetEvent_projections (t := A.det) (h := h) (C := C) (N := N) _ i j hij
  rw [← orbitEvent_filter_det]
  exact Finset.mem_filter.mpr ⟨hA, rfl⟩

theorem raw_fiber_le_of_zero_count
    {B k q H N : ℕ} (hB : 0 < B) [NeZero B] [Fact q.Prime]
    (C : Fin 3 → Fin 3 → ZMod (B ^ k))
    (d : PrimePowerData B k (transpose C)) (aux : AuxiliarySampling.Law q H)
    (hN : 0 < N) (Czero : ℝ) (hCzero : 0 ≤ Czero)
    (hzero : (∑ A ∈ fixedDetEvent N (B ^ k) C 0,
      matrixWeight q aux.size aux.weight aux.sets A) ≤
        Czero * (Real.log (4 * (N : ℝ)) / Real.log 2) * (N : ℝ) ^ 6 /
          ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2)
    (t : ℤ) (htq : |t| < (q : ℤ)) :
    (∑ A ∈ fixedDetEvent N (B ^ k) C t,
      matrixWeight q aux.size aux.weight aux.sets A) ≤
        UniformFixedFiberCount.commonConstant Czero NonzeroAuxiliaryCount.countConstant *
          Real.log (2 * (N : ℝ)) ^ 2 * (N : ℝ) ^ 6 /
            ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
  have hz : (∑ A ∈ (orbitEvent N (B ^ k) C).filter (fun A => A.det = 0),
      matrixWeight q aux.size aux.weight aux.sets A) ≤
        Czero * (Real.log (4 * (N : ℝ)) / Real.log 2) * (N : ℝ) ^ 6 /
          ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
    simpa only [orbitEvent_filter_det] using hzero
  have hb := UniformFixedFiberCount.matrix_fiber_le_of_zero_count hB
    (transpose C) d (N : ℝ) (by exact_mod_cast hN) (orbitEvent N (B ^ k) C)
    (fun A hA => orbitEvent_reduction hA) (fun A hA j => orbitEvent_box hA j)
    (matrixWeight q aux.size aux.weight aux.sets) 8 Czero (by norm_num) hCzero
    (fun A _ hAI => aux.weight_le_eight _ hAI) hz t htq
  simpa only [orbitEvent_filter_det, NonzeroAuxiliaryCount.countConstant] using hb

theorem typed_fiber_le_of_zero_count
    {B k q H N : ℕ} (hB : 0 < B) [NeZero B] [Fact q.Prime]
    (C : Fin 3 → Fin 3 → ZMod (B ^ k))
    (d : PrimePowerData B k (transpose C)) (aux : AuxiliarySampling.Law q H)
    (hN : 0 < N) (Czero : ℝ) (hCzero : 0 ≤ Czero)
    (hzero : (∑ A ∈ fixedDetEvent N (B ^ k) C 0,
      matrixWeight q aux.size aux.weight aux.sets A) ≤
        Czero * (Real.log (4 * (N : ℝ)) / Real.log 2) * (N : ℝ) ^ 6 /
          ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2)
    (t : ℤ) (htq : |t| < (q : ℤ)) :
    (∑ x ∈ (((Finset.univ : Finset (Fin 3 → Box N 3 (samplingShift N))).filter
      (fun x => project (x 0) ≠ project (x 1) ∧ project (x 0) ≠ project (x 2) ∧
        project (x 1) ≠ project (x 2))).filter
      (fun x => (fun j => residue (B ^ k) (x j)) ∈ orbitFinset (MainGroup (B ^ k)) C)).filter
      (fun x => (integralMatrix x).det = t),
      LiftingProbability.auxiliaryWeight q aux.size aux.weight aux.sets
        (fun j => residue q (x j))) ≤
      UniformFixedFiberCount.commonConstant Czero NonzeroAuxiliaryCount.countConstant *
        Real.log (2 * (N : ℝ)) ^ 2 * (N : ℝ) ^ 6 /
          (((B : ℝ) ^ d.b) ^ 2 * ((B : ℝ) ^ d.e) ^ 2) := by
  rw [sum_fixedDet_nested_event]
  simpa only [mul_pow] using raw_fiber_le_of_zero_count hB C d aux hN Czero hCzero
    hzero t htq

end Problem355.TypedFixedFiberCount

end

end OAI
