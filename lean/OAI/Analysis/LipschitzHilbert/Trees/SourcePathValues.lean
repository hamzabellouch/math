import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionValues

namespace OAI

/-! Exact source values in dominant-path coordinates, before estimates. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem diagonalModulation_real_smul (f : κ → ℝ) (a : ℝ)
    (A : EuclideanSpace ℂ κ) (b : ℝ) :
    diagonalModulation f (a • A) b = a • diagonalModulation f A b :=
  (diagonalModulationRealIsometry f b).map_smul _ _

theorem source_snapshot_value_as_prediction (p μ n : ℝ) (c : ι → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) (frequency : ι → κ → ℝ) (b : ℝ) :
    sourceSnapshotPrediction p μ n c A lam frequency b =
      sourcePredictionValue p μ n c (fun i => diagonalModulation (frequency i) (A i) b) lam := by
  unfold sourceSnapshotPrediction sourcePredictionValue
  simp only [← diagonalModulation_real_smul,norm_diagonalModulation]

/-- The source actual ratio in any common unitary path frame. -/
theorem source_prediction_path_value {n p μ : ℝ} (hn : 0 < n) (hp : 0 < p)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (i₀ : ι) (hlam : lam i₀ ≠ 0) (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ) :
    sourcePredictionValue p μ n c A lam =
      energyRatio p
        (1+‖(c i₀/n)^(1/p) • U ((c i₀)^(μ-1) • A i₀)‖^p+
          ∑ i : RemainderIndex i₀, (c i/n)*‖(c i)^(μ-1) • A i‖^p)
        (((c i₀/n)^(1-μ-1/p)*‖lam i₀‖) •
          ((c i₀/n)^(1/p) • U ((c i₀)^(μ-1) • A i₀))+
          (scalarPhase (lam i₀))⁻¹ • U
            (∑ i : RemainderIndex i₀, ((n^(μ-1):ℝ):ℂ) • (lam i • A i))) := by
  have h := source_path_prediction_identity (μ := μ) (fun i => c i/n)
    (fun i => (c i)^(μ-1) • A i) lam i₀ U hp (div_pos (hc i₀) hn) hlam
  dsimp only at h
  have heq (i : ι) := source_normalized_numerator_eq hn (hc i) μ (lam i) (A i)
  unfold sourcePredictionValue
  simp_rw [heq] at h ⊢
  exact h

/-- The model leaves precisely the distinguished path unshrunk. -/
theorem source_snapshot_path_value {n p μ ε : ℝ} (hn : 0 < n) (hp : 0 < p)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (i₀ : ι) (hlam : lam i₀ ≠ 0) (f : ι → κ → ℝ) (b : ℝ) :
    let shrink := fun i => if i = i₀ then A i else radialShrink (2*ε*c i) (A i)
    let U := diagonalModulationIsometry (fun k => -f i₀ k) b
    sourceSnapshotPrediction p μ n c shrink lam f b =
      energyRatio p
        (1+‖(c i₀/n)^(1/p) • ((c i₀)^(μ-1) • A i₀)‖^p+
          ∑ i : RemainderIndex i₀, (c i/n)*‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p)
        (((c i₀/n)^(1-μ-1/p)*‖lam i₀‖) •
          ((c i₀/n)^(1/p) • ((c i₀)^(μ-1) • A i₀))+
          (scalarPhase (lam i₀))⁻¹ • U
            (∑ i : RemainderIndex i₀, ((n^(μ-1):ℝ):ℂ) •
              (lam i • diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b))) := by
  dsimp only
  rw [source_snapshot_value_as_prediction]
  have h := source_prediction_path_value (μ := μ) hn hp c hc
    (fun i => diagonalModulation (f i)
      (if i = i₀ then A i else radialShrink (2*ε*c i) (A i)) b)
    lam i₀ hlam (diagonalModulationIsometry (fun k => -f i₀ k) b)
  have hoff (i : RemainderIndex i₀) :
      (if (i:ι) = i₀ then A i else radialShrink (2*ε*c i) (A i)) =
        radialShrink (2*ε*c i) (A i) := ite_eq_right i.property
  simpa only [ite_eq_left rfl,ite_true,hoff,← diagonalModulation_real_smul,norm_diagonalModulation,
    diagonalModulationIsometry_apply,diagonalModulation_inverse] using h

end LipschitzHilbert

end

end OAI
