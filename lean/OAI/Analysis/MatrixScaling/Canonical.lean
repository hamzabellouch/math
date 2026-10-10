import OAI.Analysis.MatrixScaling.Continuous
import Mathlib.Topology.Compactness.LocallyCompact

namespace OAI

/-! Unitary naturality and canonical local matrix scaling. -/

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

def frameTuple (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ) :=
  fun i => V * T i * Uᴴ

theorem scalingMap_frame (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ)
    (hU : Uᴴ * U = 1) (P : Matrix (Fin d) (Fin d) ℂ) :
    scalingMap (frameTuple T U V) (U * P * Uᴴ) = V * scalingMap T P * Vᴴ := by
  simp only [scalingMap, frameTuple, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]

theorem det_unitary_conjugate (U P : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) : (U * P * Uᴴ).det = P.det := by
  have hdet := congrArg Matrix.det hU
  simp only [Matrix.det_mul, Matrix.det_one] at hdet
  simp only [Matrix.det_mul]
  calc
    U.det * P.det * Uᴴ.det = P.det * (Uᴴ.det * U.det) := by ring
    _ = P.det := by rw [hdet, mul_one]

theorem scalingPotential_frame (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    (P : Matrix (Fin d) (Fin d) ℂ) :
    scalingPotential (frameTuple T U V) (U * P * Uᴴ) = scalingPotential T P := by
  have hQ : 1 + V * scalingMap T P * Vᴴ = V * (1 + scalingMap T P) * Vᴴ := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hV']
  simp only [scalingPotential, scalingMap_frame T U V hU, hQ,
    det_unitary_conjugate U P hU, det_unitary_conjugate V _ hV]

theorem posDef_unitary_conjugate (U P : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (hP : P.PosDef) : (U * P * Uᴴ).PosDef := by
  have hu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr (by
    have hd := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact isUnit_iff_ne_zero.mpr (by intro hz; simp [hz] at hd))
  exact hu.posDef_star_right_conjugate_iff.mpr hP

/-- A minimizer transports to any other unitary frame. -/
theorem scaling_minimizer_frame (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosDef)
    (hmin : ∀ R, R.PosDef → scalingPotential T P ≤ scalingPotential T R) :
    (U * P * Uᴴ).PosDef ∧ ∀ R, R.PosDef →
      scalingPotential (frameTuple T U V) (U * P * Uᴴ) ≤
        scalingPotential (frameTuple T U V) R := by
  refine ⟨posDef_unitary_conjugate U P hU hP, ?_⟩
  intro R hR
  have hR' := posDef_unitary_conjugate Uᴴ R (by simpa using hU') hR
  have he : U * (Uᴴ * R * U) * Uᴴ = R := by
    simp only [← Matrix.mul_assoc, hU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hU', Matrix.mul_one]
  have hi := scalingPotential_frame T U V hU hV hV' (Uᴴ * R * U)
  rw [he] at hi
  rw [scalingPotential_frame T U V hU hV hV' P, hi]
  exact hmin _ (by simpa using hR')

/-- The positive square root, not an arbitrary Gram factor, is equivariant. -/
theorem sqrt_unitary_conjugate (U P : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (hP : P.PosSemidef) :
    CFC.sqrt (U * P * Uᴴ) = U * CFC.sqrt P * Uᴴ := by
  apply CFC.sqrt_unique
  · calc
      (U * CFC.sqrt P * Uᴴ) * (U * CFC.sqrt P * Uᴴ) =
          U * (CFC.sqrt P * CFC.sqrt P) * Uᴴ := by
            simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
      _ = U * P * Uᴴ := by rw [CFC.sqrt_mul_sqrt_self P hP.nonneg]
  · exact ((CFC.sqrt_nonneg P).posSemidef.mul_mul_conjTranspose_same U).nonneg

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

def Expanding (T : Fin n → Matrix (Fin r) (Fin d) ℂ) : Prop :=
  ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
    Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ))

def canonicalMinimizer (T : Fin n → Matrix (Fin r) (Fin d) ℂ) (h : Expanding T) :
    Matrix (Fin d) (Fin d) ℂ := (existsUnique_scaling_minimizer T h).choose

theorem canonicalMinimizer_spec (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (h : Expanding T) : (canonicalMinimizer T h).PosDef ∧ ∀ R, R.PosDef →
      scalingPotential T (canonicalMinimizer T h) ≤ scalingPotential T R :=
  (existsUnique_scaling_minimizer T h).choose_spec.1

theorem canonicalMinimizer_frame (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    (h : Expanding T) (h' : Expanding (frameTuple T U V)) :
    canonicalMinimizer (frameTuple T U V) h' = U * canonicalMinimizer T h * Uᴴ := by
  have hp := canonicalMinimizer_spec T h
  have ht := scaling_minimizer_frame T U V hU hU' hV hV' _ hp.1 hp.2
  have hq := canonicalMinimizer_spec (frameTuple T U V) h'
  exact scaling_minimizer_unique _ h' hq.1 ht.1 hq.2 ht.2

def canonicalScaling (T : Fin n → Matrix (Fin r) (Fin d) ℂ) (h : Expanding T) :=
  normalizedTuple T (CFC.sqrt (canonicalMinimizer T h))
    (CFC.sqrt (1 + scalingMap T (canonicalMinimizer T h)))⁻¹

theorem canonicalScaling_relations (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (h : Expanding T) :
    (∑ i, (canonicalScaling T h i)ᴴ * canonicalScaling T h i) = 1 ∧
    ((2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
      ∑ i, canonicalScaling T h i * (canonicalScaling T h i)ᴴ).PosSemidef := by
  have hp := canonicalMinimizer_spec T h
  have hq := Matrix.PosDef.one.add_posSemidef (scalingMap_positive T hp.1.posSemidef)
  exact normalizedTuple_of_minimizer T hp.1 hp.2 _ (matrix_sqrt_factor hp.1).1
    (matrix_sqrt_factor hp.1).2 _ (matrix_sqrt_factor hq).1 (matrix_sqrt_factor hq).2

theorem inverse_unitary_conjugate (U P : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) :
    (U * P * Uᴴ)⁻¹ = U * P⁻¹ * Uᴴ := by
  have hi : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hU
  have hi' : (Uᴴ)⁻¹ = U := Matrix.inv_eq_left_inv hU'
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hi, hi']
  simp only [Matrix.mul_assoc]

/-- The normalized maps obey precisely the bundle transition law. -/
theorem canonicalScaling_frame (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin r) (Fin r) ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    (h : Expanding T) (h' : Expanding (frameTuple T U V)) :
    canonicalScaling (frameTuple T U V) h' = frameTuple (canonicalScaling T h) U V := by
  have hp := (canonicalMinimizer_spec T h).1
  have hq := Matrix.PosDef.one.add_posSemidef (scalingMap_positive T hp.posSemidef)
  have he : 1 + V * scalingMap T (canonicalMinimizer T h) * Vᴴ =
      V * (1 + scalingMap T (canonicalMinimizer T h)) * Vᴴ := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hV']
  simp only [canonicalScaling, canonicalMinimizer_frame T U V hU hU' hV hV' h h',
    scalingMap_frame T U V hU, he, sqrt_unitary_conjugate U _ hU hp.posSemidef,
    sqrt_unitary_conjugate V _ hV hq.posSemidef, inverse_unitary_conjugate V _ hV hV']
  funext i
  simp only [normalizedTuple, frameTuple, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul,
    ← Matrix.mul_assoc Uᴴ U, hU]

/-- Continuity of the canonical, hence frame-compatible, choice. -/
theorem continuous_canonicalMinimizer {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (h : ∀ y, Expanding (T y)) : Continuous (fun y => canonicalMinimizer (T y) (h y)) := by
  obtain ⟨P,hP,hmin⟩ := exists_continuous_scaling_minimizer T hT h
  have he (y : Y) : canonicalMinimizer (T y) (h y) = P y := by
    have hp := canonicalMinimizer_spec (T y) (h y)
    exact scaling_minimizer_unique _ (h y) hp.1 (hmin y).1 hp.2 (hmin y).2
  simpa only [he] using hP

theorem continuous_canonicalScaling {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (h : ∀ y, Expanding (T y)) : Continuous (fun y => canonicalScaling (T y) (h y)) := by
  let P := fun y => canonicalMinimizer (T y) (h y)
  have hp := continuous_canonicalMinimizer T hT h
  have hp' := fun y => (canonicalMinimizer_spec (T y) (h y)).1
  let Q := fun y => 1 + scalingMap (T y) (P y)
  have hq : Continuous Q := continuous_const.add (continuous_scalingMap T hT P hp)
  have hq' : ∀ y, (Q y).PosDef := fun y =>
    Matrix.PosDef.one.add_posSemidef (scalingMap_positive (T y) (hp' y).posSemidef)
  have ha := continuous_matrix_sqrt P hp hp'
  have hb := continuous_matrix_sqrt Q hq hq'
  have hi := continuous_matrix_inverse _ hb (fun y => (matrix_sqrt_factor (hq' y)).1)
  apply continuous_pi
  intro i
  exact (continuous_const : Continuous (fun _ : Y => (Real.sqrt (2/3 : ℝ) : ℂ))).smul ((hi.matrix_mul ((continuous_apply i).comp hT)).matrix_mul ha)

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

theorem continuous_canonicalScaling_local {Y : Type*} [TopologicalSpace Y]
    [WeaklyLocallyCompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (h : ∀ y, Expanding (T y)) : Continuous (fun y => canonicalScaling (T y) (h y)) := by
  rw [continuous_iff_continuousAt]
  intro y
  obtain ⟨K,hK,hy⟩ := exists_compact_mem_nhds y
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc := continuous_canonicalScaling (fun z : K => T z.val)
    (hT.comp continuous_subtype_val) (fun z => h z.val)
  have hon : ContinuousOn (fun y => canonicalScaling (T y) (h y)) K :=
    continuousOn_iff_continuous_domRestrict.mpr hc
  exact (hon y (mem_of_mem_nhds hy)).continuousAt hy

/-- The same localization for the positive endomorphism before normalization. -/
theorem continuous_canonicalMinimizer_local {Y : Type*} [TopologicalSpace Y]
    [WeaklyLocallyCompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (h : ∀ y, Expanding (T y)) : Continuous (fun y => canonicalMinimizer (T y) (h y)) := by
  rw [continuous_iff_continuousAt]
  intro y
  obtain ⟨K,hK,hy⟩ := exists_compact_mem_nhds y
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc := continuous_canonicalMinimizer (fun z : K => T z.val)
    (hT.comp continuous_subtype_val) (fun z => h z.val)
  have hon : ContinuousOn (fun y => canonicalMinimizer (T y) (h y)) K :=
    continuousOn_iff_continuous_domRestrict.mpr hc
  exact (hon y (mem_of_mem_nhds hy)).continuousAt hy

end Kaplansky

end

end OAI
