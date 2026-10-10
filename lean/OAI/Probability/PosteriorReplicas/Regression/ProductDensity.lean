import OAI.Probability.PosteriorReplicas.Regression.ReplicaKernel

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section ProductDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

lemma measure_pi_withDensity (n : ℕ) (f : Fin n → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite (μ.withDensity (f i))] :
    Measure.pi (fun i => μ.withDensity (f i)) =
      (Measure.pi (fun _ : Fin n => μ)).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have he (x : Fin n → X) :
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x =
        ∏ i, (s i).indicator (f i) (x i) := by
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      have : ∃ i, x i ∉ s i := by simpa only [Set.mem_univ_pi, not_forall] using hx
      obtain ⟨i, hi⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  simp_rw [he]
  rw [lintegral_fin_prod μ n _ (fun i => (hf i).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]
end ProductDensity

end PosteriorRegression
end

end OAI
