import OAI.Geometry.HeilbronnTriangle.IntegerMatrixEvents
import OAI.Geometry.HeilbronnTriangle.OrbitRowLattice

namespace OAI


noncomputable section
namespace Problem355.IntegerMatrixEvents
open Finset Matrix IntegerSampling OrbitSampling
attribute [local instance] Classical.propDecidable

def fixedDetProperty (h : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ) (A : IntMatrix) : Prop :=
  Homogeneous.projectedDistinct (Homogeneous.integerColumn A 0)
      (Homogeneous.integerColumn A 1) (Homogeneous.integerColumn A 2) ∧
    (fun j i => (A i j : ZMod h)) ∈ orbitFinset (MainGroup h) C ∧ A.det = t

def fixedDetEvent (N h : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ) : Finset IntMatrix :=
  (matrices N (samplingShift N)).filter (fixedDetProperty h C t)

theorem sum_fixedDet_event {Ω : Type*} [Fintype Ω]
    (N h q s : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q)) :
    (∑ x ∈ (Finset.univ : Finset (Fin 3 → Box N 3 (samplingShift N))).filter
      (fun x => fixedDetProperty h C t (integralMatrix x)),
      LiftingProbability.auxiliaryWeight q s w V (fun j => residue q (x j))) =
      ∑ A ∈ fixedDetEvent N h C t, matrixWeight q s w V A := by
  exact sum_auxiliaryWeight_event q s w V (fixedDetProperty h C t)
theorem fixedDetProperty_integralMatrix {N h : ℕ} [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ)
    (x : Fin 3 → Box N 3 (samplingShift N)) :
    fixedDetProperty h C t (integralMatrix x) ↔
      Homogeneous.projectedDistinct (Homogeneous.integerColumn (integralMatrix x) 0)
        (Homogeneous.integerColumn (integralMatrix x) 1)
        (Homogeneous.integerColumn (integralMatrix x) 2) ∧
      (fun j => residue h (x j)) ∈ orbitFinset (MainGroup h) C ∧
      (integralMatrix x).det = t := by
  rfl

theorem fixedDetProperty_reduction {h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {t : ℤ} {A : IntMatrix}
    (hA : fixedDetProperty h C t A) :
    A.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit (Matrix.transpose C) := by
  obtain ⟨G, hG⟩ := (mem_orbitFinset C _).mp hA.2.1
  refine ⟨G, ?_⟩
  change G.val * Matrix.transpose C = A.map (Int.castRingHom (ZMod h))
  rw [← sl_action_transpose]
  exact congrArg Matrix.transpose hG

theorem fixedDetEvent_rows {N h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {t : ℤ} {A : IntMatrix}
    (hA : A ∈ fixedDetEvent N h C t) (i : Fin 3) :
    A i ∈ RowLattice.integerRowLattice h (Matrix.transpose C) := by
  exact OrbitRowLattice.row_mem_integerRowLattice_of_reduction_mem_slOrbit
    h (Matrix.transpose C) A (fixedDetProperty_reduction (Finset.mem_filter.mp hA).2) i

theorem fixedDetEvent_det {N h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {t : ℤ} {A : IntMatrix}
    (hA : A ∈ fixedDetEvent N h C t) : A.det = t :=
  (Finset.mem_filter.mp hA).2.2.2

theorem fixedDetEvent_coord {N h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {t : ℤ} {A : IntMatrix}
    (hA : A ∈ fixedDetEvent N h C t) (i j : Fin 3) :
    |(A i j : ℝ)| ≤ 2 * (N : ℝ) :=
  sampling_coord_abs_le (Finset.mem_filter.mp hA).1 i j

theorem fixedDetEvent_height {N h : ℕ} [NeZero h] (hN : 0 < N)
    {C : Fin 3 → Fin 3 → ZMod h} {t : ℤ} {A : IntMatrix}
    (hA : A ∈ fixedDetEvent N h C t) (j : Fin 3) : A 2 j ≠ 0 :=
  (sampling_height_pos hN (Finset.mem_filter.mp hA).1 j).ne'

theorem fixedDetEvent_projections {N h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {t : ℤ} {A : IntMatrix}
    (hA : A ∈ fixedDetEvent N h C t) (i j : Fin 3) (hij : i ≠ j) :
    Homogeneous.project (Homogeneous.integerColumn A i) ≠
      Homogeneous.project (Homogeneous.integerColumn A j) := by
  obtain ⟨h01, h02, h12⟩ := (Finset.mem_filter.mp hA).2.1
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact h01
  · exact h02
  · exact h01.symm
  · exact False.elim (hij rfl)
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact False.elim (hij rfl)

theorem sum_fixedDet_nested_event {Ω : Type*} [Fintype Ω]
    (N h q s : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q)) :
    (∑ x ∈ (((Finset.univ : Finset (Fin 3 → Box N 3 (samplingShift N))).filter
      (fun x => project (x 0) ≠ project (x 1) ∧
        project (x 0) ≠ project (x 2) ∧ project (x 1) ≠ project (x 2))).filter
      (fun x => (fun j => residue h (x j)) ∈ orbitFinset (MainGroup h) C)).filter
      (fun x => (integralMatrix x).det = t),
      LiftingProbability.auxiliaryWeight q s w V (fun j => residue q (x j))) =
      ∑ A ∈ fixedDetEvent N h C t, matrixWeight q s w V A := by
  rw [← sum_fixedDet_event N h q s C t w V]
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      fixedDetProperty_integralMatrix, Homogeneous.projectedDistinct,
      integralMatrix_project]
    tauto
  · intro x hx
    rfl

end Problem355.IntegerMatrixEvents

end

end OAI
