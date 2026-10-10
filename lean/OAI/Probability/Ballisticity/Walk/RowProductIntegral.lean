import Mathlib
import OAI.Probability.Ballisticity.Estimates.IndependentRandomTestBound

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma lintegral_prod_disjoint_rows {d : ℕ} {ι : Type*}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (S : ι → Set (Lattice d)) (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (F : ι → Environment d → ℝ≥0∞)
    (hF : ∀ i, @Measurable _ _ (rowSigma (S i)) _ (F i)) (I : Finset ι) :
    (∫⁻ ω, ∏ i ∈ I, F i ω ∂environmentLaw ν) =
      ∏ i ∈ I, ∫⁻ ω, F i ω ∂environmentLaw ν := by
  induction I using Finset.cons_induction with
  | empty => simp
  | cons a I ha ih =>
    simp only [Finset.prod_cons]
    let T := ⋃ i ∈ (I : Set ι), S i
    have hST : Disjoint (S a) T := by
      simp only [T,Set.disjoint_iUnion_right]
      intro i hi
      exact hS (by intro he; subst i; exact ha hi)
    have hp : @Measurable _ _ (rowSigma T) _ (fun ω => ∏ i ∈ I, F i ω) := by
      apply Finset.measurable_prod
      intro i hi
      exact (hF i).mono (rowSigma_mono (by
        intro x hx; exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,hx⟩⟩)) le_rfl
    have hind := indepFun_of_disjoint_rows ν hST (F a) _ (hF a) hp
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      ((hF a).mono (rowSigma_le _) le_rfl).aemeasurable
      (hp.mono (rowSigma_le _) le_rfl).aemeasurable hind,ih]

end DirectionalTransience

end

end

end OAI
