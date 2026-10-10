import Mathlib
import OAI.Probability.LogConcave.Model

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory
open WithLp

namespace LogConcaveSampling
lemma pi_append_law {E : Type*} [MeasurableSpace E] (γ : Measure E) [SigmaFinite γ]
    (m n : ℕ) :
    ((Measure.pi (fun _ : Fin m => γ)).prod (Measure.pi (fun _ : Fin n => γ))).map
      (fun p => Fin.append p.1 p.2) = Measure.pi (fun _ : Fin (m+n) => γ) := by
  have hsum := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin n => γ)
  have he := measurePreserving_piCongrLeft (fun _ : Fin (m+n) => γ) finSumFinEquiv
  have h := (he.comp hsum).map_eq
  convert h using 1
  congr 1
  funext p i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      MeasurableEquiv.sumPiEquivProdPi]

lemma pi_transpose_law {ι κ E : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace E]
    (γ : Measure E) [IsProbabilityMeasure γ] :
    (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => γ))).map
      (fun x j i => x i j) = Measure.pi (fun _ : κ => Measure.pi (fun _ : ι => γ)) := by
  have h₁ := Measure.infinitePi_map_curry_symm (fun (_ : ι) (_ : κ) => γ)
  have h₃ := Measure.infinitePi_map_curry (fun (_ : κ) (_ : ι) => γ)
  have h₂ := (measurePreserving_piCongrLeft (fun _ : κ × ι => γ) (Equiv.prodComm ι κ)).map_eq
  simp only [Measure.infinitePi_eq_pi] at h₁ h₃
  rw [← h₂,← h₁,Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h₃
  convert h₃ using 1
  rfl

lemma stdGaussian_ofLp (d : ℕ) :
    (stdGaussian (Point d)).map ofLp = Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
  rw [← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id

lemma gaussianColumns_rows_law (d b : ℕ) :
    (Measure.pi (fun _ : Fin b => stdGaussian (Point d))).map
      (fun a k i => a i k) =
      Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin b => gaussianReal 0 1)) := by
  have h := (measurePreserving_pi
    (fun _ : Fin b => stdGaussian (Point d))
    (fun _ : Fin b => Measure.pi (fun _ : Fin d => gaussianReal 0 1))
    (fun _ => ⟨by fun_prop, stdGaussian_ofLp d⟩ : ∀ _ : Fin b,
      MeasurePreserving (ofLp : Point d → Fin d → ℝ) _ _)).map_eq
  have ht := pi_transpose_law (ι := Fin b) (κ := Fin d) (gaussianReal 0 1)
  rw [← h,Measure.map_map (by fun_prop) (by fun_prop)] at ht
  exact ht

end LogConcaveSampling

end LowerProof
end
end
end

end OAI
