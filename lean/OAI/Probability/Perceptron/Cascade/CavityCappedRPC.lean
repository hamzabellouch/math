import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityDiagonalKernel
import OAI.Probability.Perceptron.Cavity.CavityIndexedLog

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavityDiagonalAverage_bounds {I : Type} [Fintype I] [DecidableEq I]
    (σ : I→ℝ) (Ψ : EuclideanSpace ℝ I→ᵇℝ) {a b : ℝ}
    (ha : ∀ z,a≤Ψ z) (hb : ∀ z,Ψ z≤b) (x : EuclideanSpace ℝ I) :
    a≤cavityDiagonalAverage σ Ψ x ∧ cavityDiagonalAverage σ Ψ x≤b := by
  have hm : Measurable (fun z : EuclideanSpace ℝ I=>Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i))) := by fun_prop
  have hi : Integrable (fun z : EuclideanSpace ℝ I=>Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i)))
      (stdGaussian (EuclideanSpace ℝ I)) :=
    Integrable.of_bound hm.aestronglyMeasurable ‖Ψ‖ (ae_of_all _ fun z=>Ψ.norm_coe_le_norm _)
  change a≤∫ z,Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i)) ∂stdGaussian (EuclideanSpace ℝ I) ∧
    (∫ z,Ψ (WithLp.toLp 2 (fun i=>x i+σ i*z i)) ∂stdGaussian (EuclideanSpace ℝ I))≤b
  constructor
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (integrable_const a) hi (fun z=>ha _)
  · simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono hi (integrable_const b) (fun z=>hb _)

lemma cavityResidualCapped_bounds (n d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (x : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    Real.exp (-(d:ℝ)*‖f‖)≤cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) x ∧
      cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) x≤Λ*Real.exp ((d:ℝ)*‖f‖) :=
  cavityDiagonalAverage_bounds σ _ (fun z=>(cavitySingleTest_bounds n d f Λ hΛ z).1)
    (fun z=>(cavitySingleTest_bounds n d f Λ hΛ z).2) x

lemma cavityResidualCapped_pos (n d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (x : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    0<cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) x :=
  (Real.exp_pos _).trans_le (cavityResidualCapped_bounds n d f Λ hΛ σ x).1

lemma cavityResidualCapped_log_bound (n d : ℕ) (f : ℝ→ᵇℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (σ : Fin (n+1)⊕Fin d→ℝ) (x : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    |Real.log (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) x)|≤Real.log Λ+d*‖f‖ := by
  have hb:=cavityResidualCapped_bounds n d f Λ hΛ σ x
  have hp:=cavityResidualCapped_pos n d f Λ hΛ σ x
  have hl:=Real.log_le_log (Real.exp_pos _) hb.1
  have hu:=Real.log_le_log hp hb.2
  rw [Real.log_exp] at hl
  rw [Real.log_mul (by linarith : Λ≠0) (Real.exp_pos _).ne',Real.log_exp] at hu
  exact abs_le.mpr ⟨by linarith [Real.log_nonneg hΛ],hu⟩

theorem cavity_capped_indexed_log_recursion (n d k : ℕ) (f : ℝ→ᵇℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (σ : Fin (n+1)⊕Fin d→ℝ)
    (A : ℕ→EuclideanSpace ℝ (Fin (n+1)⊕Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)⊕Fin d))
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (x : ℕ→EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    (∫ p : IndexedCascadeBase k×IndexedCascadeMarks (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) k,
      Real.log (∫ l,cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)
        (indexedLeafState (gaussianLinearMarkStep A) k (x,p.2) l 0)
        ∂indexedLeafProbability k p.1)
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) k))=
      finiteCascadeLogRecursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
        (gaussianLinearMarkStep A) k z
        (fun s=>Real.log (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) (s 0))) x := by
  have hm : Measurable (fun s : ℕ→EuclideanSpace ℝ (Fin (n+1)⊕Fin d)=>
      Real.log (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) (s 0))) :=
    ((cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ)).measurable.comp (measurable_pi_apply 0)).log
  have hh:=cavity_indexed_log_recursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
    (gaussianLinearMarkStep A) (gaussianLinearMarkStep_measurable A)
    (fun s=>Real.log (cavityDiagonalAverage σ (cavitySingleTest n d f Λ hΛ) (s 0))) hm
    (fun s=>cavityResidualCapped_log_bound n d f Λ hΛ σ (s 0)) k z hz hz0 hz1 x
  simpa only [Real.exp_log (cavityResidualCapped_pos n d f Λ hΛ σ _)] using hh

end SphericalPerceptronFreeEnergy
end

end OAI
