import OAI.Geometry.HeilbronnTriangle.OrbitSampling
import OAI.Geometry.HeilbronnTriangle.ProjectiveBadEvent

namespace OAI


noncomputable section

namespace Problem355.IntegerMatrixEvents
attribute [local instance] Classical.propDecidable

open Finset Matrix
open IntegerSampling OrbitSampling

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ

theorem integralMatrix_injective {N : ℕ} {shift : Fin 3 → ℤ} :
    Function.Injective (@integralMatrix N shift) := by
  intro x y h
  funext j i
  apply Subtype.ext
  exact congrFun (congrFun h i) j

def InBox (N : ℕ) (shift : Fin 3 → ℤ) (A : IntMatrix) : Prop :=
  ∀ i j, shift i ≤ A i j ∧ A i j < shift i + N

def integralMatrixEquiv (N : ℕ) (shift : Fin 3 → ℤ) :
    (Fin 3 → Box N 3 shift) ≃ {A : IntMatrix // InBox N shift A} where
  toFun x := ⟨integralMatrix x, fun i j => (x j i).property⟩
  invFun A := fun j i => ⟨A.val i j, A.property i j⟩
  left_inv _ := rfl
  right_inv _ := rfl

def matrices (N : ℕ) (shift : Fin 3 → ℤ) : Finset IntMatrix := by
  classical
  exact Finset.univ.image (@integralMatrix N shift)

@[simp] theorem mem_matrices {N : ℕ} {shift : Fin 3 → ℤ} {A : IntMatrix} :
    A ∈ matrices N shift ↔ InBox N shift A := by
  classical
  constructor
  · intro h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    exact fun i j => (x j i).property
  · intro h
    exact Finset.mem_image.mpr
      ⟨(integralMatrixEquiv N shift).symm ⟨A, h⟩, Finset.mem_univ _, rfl⟩

@[simp] theorem integralMatrix_residue {N : ℕ} {shift : Fin 3 → ℤ}
    (m : ℕ) (x : Fin 3 → Box N 3 shift) :
    (integralMatrix x).map (Int.cast : ℤ → ZMod m) =
      Matrix.transpose (fun j => residue m (x j)) := rfl

@[simp] theorem integralMatrix_project {N : ℕ}
    (x : Fin 3 → Box N 3 (samplingShift N)) (j : Fin 3) :
    Homogeneous.project (Homogeneous.integerColumn (integralMatrix x) j) =
      IntegerSampling.project (x j) := rfl

theorem sum_image_integralMatrix {N : ℕ} {shift : Fin 3 → ℤ}
    (S : Finset (Fin 3 → Box N 3 shift)) (W : IntMatrix → ℝ) :
    (∑ x ∈ S, W (integralMatrix x)) =
      ∑ A ∈ S.image integralMatrix, W A := by
  classical
  rw [Finset.sum_image]
  exact fun x _ y _ h => integralMatrix_injective h

theorem image_matrix_event {N : ℕ} {shift : Fin 3 → ℤ}
    (P : IntMatrix → Prop) :
    ((Finset.univ : Finset (Fin 3 → Box N 3 shift)).filter
      (fun x => P (integralMatrix x))).image integralMatrix =
      (matrices N shift).filter P := by
  classical
  ext A
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    matrices]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hx⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩

theorem sum_matrix_event {N : ℕ} {shift : Fin 3 → ℤ}
    (P : IntMatrix → Prop) (W : IntMatrix → ℝ) :
    (∑ x ∈ (Finset.univ : Finset (Fin 3 → Box N 3 shift)).filter
      (fun x => P (integralMatrix x)), W (integralMatrix x)) =
      ∑ A ∈ (matrices N shift).filter P, W A := by
  classical
  rw [sum_image_integralMatrix, image_matrix_event]

def matrixWeight {Ω : Type*} [Fintype Ω] (q s : ℕ)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q)) (A : IntMatrix) : ℝ :=
  LiftingProbability.auxiliaryWeight q s w V
    (fun j i => (A i j : ZMod q))

@[simp] theorem matrixWeight_integralMatrix {Ω : Type*} [Fintype Ω]
    {N : ℕ} {shift : Fin 3 → ℤ} (q s : ℕ)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
    (x : Fin 3 → Box N 3 shift) :
    matrixWeight q s w V (integralMatrix x) =
      LiftingProbability.auxiliaryWeight q s w V
        (fun j => residue q (x j)) := rfl

theorem sum_auxiliaryWeight_event {Ω : Type*} [Fintype Ω]
    {N : ℕ} {shift : Fin 3 → ℤ} (q s : ℕ)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
    (P : IntMatrix → Prop) :
    (∑ x ∈ (Finset.univ : Finset (Fin 3 → Box N 3 shift)).filter
      (fun x => P (integralMatrix x)),
      LiftingProbability.auxiliaryWeight q s w V (fun j => residue q (x j))) =
      ∑ A ∈ (matrices N shift).filter P, matrixWeight q s w V A := by
  exact sum_matrix_event P (matrixWeight q s w V)

theorem sampling_coord_bounds {N : ℕ} {A : IntMatrix}
    (hA : A ∈ matrices N (samplingShift N)) (i j : Fin 3) :
    0 ≤ A i j ∧ A i j < 2 * (N : ℤ) := by
  have h := (mem_matrices.mp hA) i j
  have hN : (0 : ℤ) ≤ N := Nat.cast_nonneg N
  fin_cases i <;> norm_num [samplingShift] at h ⊢ <;> omega

theorem sampling_coord_abs_le {N : ℕ} {A : IntMatrix}
    (hA : A ∈ matrices N (samplingShift N)) (i j : Fin 3) :
    |(A i j : ℝ)| ≤ 2 * (N : ℝ) := by
  obtain ⟨hzero, hupper⟩ := sampling_coord_bounds hA i j
  have h : |A i j| ≤ 2 * (N : ℤ) := by
    rw [abs_of_nonneg hzero]
    exact hupper.le
  exact_mod_cast h

theorem sampling_height_pos {N : ℕ} (hN : 0 < N) {A : IntMatrix}
    (hA : A ∈ matrices N (samplingShift N)) (j : Fin 3) : 0 < A 2 j := by
  have h := (mem_matrices.mp hA) 2 j
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  exact hNz.trans_le h.1

end Problem355.IntegerMatrixEvents

end

end OAI
