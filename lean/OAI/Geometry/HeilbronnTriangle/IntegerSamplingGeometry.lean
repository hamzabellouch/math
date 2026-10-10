import OAI.Geometry.HeilbronnTriangle.IntegerSampling
import OAI.Geometry.HeilbronnTriangle.HomogeneousGeometry
import OAI.Geometry.HeilbronnTriangle.SharedGeometricAlteration

namespace OAI


noncomputable section

namespace Problem355.IntegerSamplingGeometry

abbrev Column (N : ℕ) := IntegerSampling.Box N 3 (IntegerSampling.samplingShift N)

def realColumn {N : ℕ} (x : Column N) : Homogeneous.Column :=
  fun i => ((x i).val : ℝ)

def matrix {N : ℕ} (x : Fin 3 → Column N) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => (x j i).val

lemma realColumn_inBox {N : ℕ} (x : Column N) :
    Homogeneous.InBox (N : ℝ) (realColumn x) := by
  have h0 : 0 ≤ (x 0).val ∧ (x 0).val < (N : ℤ) := by
    simpa [IntegerSampling.samplingShift] using (x 0).property
  have h1 : 0 ≤ (x 1).val ∧ (x 1).val < (N : ℤ) := by
    simpa [IntegerSampling.samplingShift] using (x 1).property
  have h2 : (N : ℤ) ≤ (x 2).val ∧ (x 2).val < (N : ℤ) + N := (x 2).property
  change 0 ≤ ((x 0).val : ℝ) ∧ ((x 0).val : ℝ) < N ∧
    0 ≤ ((x 1).val : ℝ) ∧ ((x 1).val : ℝ) < N ∧
    (N : ℝ) ≤ ((x 2).val : ℝ) ∧ ((x 2).val : ℝ) < 2 * N
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast h0.1
  · exact_mod_cast h0.2
  · exact_mod_cast h1.1
  · exact_mod_cast h1.2
  · exact_mod_cast h2.1
  · have h : (x 2).val < 2 * (N : ℤ) := by omega
    exact_mod_cast h

lemma project_realColumn {N : ℕ} (x : Column N) :
    Homogeneous.project (realColumn x) = IntegerSampling.project x := rfl

lemma det_realColumn {N : ℕ} (x : Fin 3 → Column N) :
    (Homogeneous.columns (realColumn (x 0)) (realColumn (x 1))
      (realColumn (x 2))).det = ((matrix x).det : ℝ) := by
  simp [Homogeneous.columns, realColumn, matrix, Matrix.det_fin_three]

theorem project_area_lower_bound {N : ℕ} (hN : 0 < N) {τ : ℝ} (hτ : 0 ≤ τ)
    (x : Fin 3 → Column N) (hd : τ ≤ |((matrix x).det : ℝ)|) :
    τ / (16 * (N : ℝ) ^ 3) ≤
      triangleArea (IntegerSampling.project (x 0)) (IntegerSampling.project (x 1))
        (IntegerSampling.project (x 2)) := by
  have h := Homogeneous.project_area_lower_bound_of_box
    (show (0 : ℝ) < N by exact_mod_cast hN) hτ
    (realColumn_inBox (x 0)) (realColumn_inBox (x 1)) (realColumn_inBox (x 2))
  rw [det_realColumn] at h
  exact h hd

theorem smallTriangle_implies_small_det {N : ℕ} (hN : 0 < N) {τ : ℝ} (hτ : 0 ≤ τ)
    (x : Fin 3 → Column N)
    (hx : Alteration.smallTriangle (τ / (16 * (N : ℝ) ^ 3))
      (IntegerSampling.project (x 0)) (IntegerSampling.project (x 1))
      (IntegerSampling.project (x 2))) :
    IntegerSampling.project (x 0) ≠ IntegerSampling.project (x 1) ∧
    IntegerSampling.project (x 0) ≠ IntegerSampling.project (x 2) ∧
    IntegerSampling.project (x 1) ≠ IntegerSampling.project (x 2) ∧
    |((matrix x).det : ℝ)| ≤ τ := by
  refine ⟨hx.1, hx.2.1, hx.2.2.1, le_of_lt ?_⟩
  by_contra hn
  exact (not_lt_of_ge (project_area_lower_bound hN hτ x (le_of_not_gt hn))) hx.2.2.2

def BadDet {N : ℕ} (τ : ℤ) (x : Fin 3 → Column N) : Prop :=
  IntegerSampling.project (x 0) ≠ IntegerSampling.project (x 1) ∧
  IntegerSampling.project (x 0) ≠ IntegerSampling.project (x 2) ∧
  IntegerSampling.project (x 1) ≠ IntegerSampling.project (x 2) ∧
  |(matrix x).det| ≤ τ

lemma smallTriangle_implies_badDet {N : ℕ} (hN : 0 < N) {τ : ℤ} (hτ : 0 ≤ τ)
    (x : Fin 3 → Column N)
    (hx : Alteration.smallTriangle ((τ : ℝ) / (16 * (N : ℝ) ^ 3))
      (IntegerSampling.project (x 0)) (IntegerSampling.project (x 1))
      (IntegerSampling.project (x 2))) : BadDet τ x := by
  have h := smallTriangle_implies_small_det hN (by exact_mod_cast hτ) x hx
  exact ⟨h.1, h.2.1, h.2.2.1, by exact_mod_cast h.2.2.2⟩

def determinantMass {Θ : Type*} [Fintype Θ] {N : ℕ}
    (ρ : Θ → ℝ) (μ : Θ → Column N → ℝ) (τ : ℤ) : ℝ := by
  classical
  exact ∑ z : Θ × (Fin 3 → Column N),
    if BadDet τ z.2 then ConditionalSamples.sharedWeight ρ μ z else 0

theorem tripleMass_le_determinantMass {Θ : Type*} [Fintype Θ] {N : ℕ}
    (hN : 0 < N) {τ : ℤ} (hτ : 0 ≤ τ)
    (ρ : Θ → ℝ) (μ : Θ → Column N → ℝ)
    (hρ : ∀ θ, 0 ≤ ρ θ) (hμ : ∀ θ x, 0 ≤ μ θ x) :
    SharedGeometricAlteration.tripleMass ρ μ (fun _ => IntegerSampling.project)
      ((τ : ℝ) / (16 * (N : ℝ) ^ 3)) ≤ determinantMass ρ μ τ := by
  classical
  unfold SharedGeometricAlteration.tripleMass determinantMass
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : Alteration.smallTriangle ((τ : ℝ) / (16 * (N : ℝ) ^ 3))
      (IntegerSampling.project (z.2 0)) (IntegerSampling.project (z.2 1))
      (IntegerSampling.project (z.2 2))
  · rw [ite_eq_left hz, ite_eq_left (smallTriangle_implies_badDet hN hτ z.2 hz)]
  · rw [ite_eq_right hz]
    split_ifs
    · exact ConditionalSamples.sharedWeight_nonneg ρ μ hρ hμ z
    · exact le_rfl

end Problem355.IntegerSamplingGeometry

end

end OAI
