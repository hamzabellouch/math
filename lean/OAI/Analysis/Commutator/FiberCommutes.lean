import Mathlib
import OAI.Analysis.Commutator.DenseCommutes
import OAI.Analysis.Commutator.FiberCommutator

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

lemma commute_ae_of_commuting_fields (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb0 : 0≤b) (hc0 : 0≤c)
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖≤c)
    (hcomm : Commute (operator μ T hT hb) (operator μ S hS hc)) :
    ∀ᵐ a ∂μ,Commute (T a) (S a) := by
  have hnorm := commutator_ae_bound μ T S hT hS hb0 hc0 (by norm_num : (0:ℝ)≤0) hb hc
    (by rw [hcomm.eq,sub_self,norm_zero])
  filter_upwards [hnorm] with a ha
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ha (norm_nonneg _)))

theorem commutant_ae_of_dense_commuting_fields
    (Q R : Ω → VonNeumannAlgebra H)
    (T S : ℕ → Ω → H →L[ℂ] H)
    (hT : ∀ n ξ,AEStronglyMeasurable (fun a => T n a ξ) μ)
    (hS : ∀ n ξ,AEStronglyMeasurable (fun a => S n a ξ) μ)
    (hTb : ∀ n,∀ᵐ a ∂μ,‖T n a‖≤1) (hSb : ∀ n,∀ᵐ a ∂μ,‖S n a‖≤1)
    (hcomm : ∀ i j,Commute (operator μ (T i) (hT i) (hTb i))
      (operator μ (S j) (hS j) (hSb j)))
    (hTd : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => T (k n) a ξ) atTop (𝓝 (A ξ)))
    (hSd : ∀ᵐ a ∂μ,∀ B : H →L[ℂ] H,B∈R a → ‖B‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => S (k n) a ξ) atTop (𝓝 (B ξ))) :
    ∀ᵐ a ∂μ,R a≤(Q a).commutant := by
  have ht (i j : ℕ) := commute_ae_of_commuting_fields μ (T i) (S j) (hT i) (hS j)
    (by norm_num) (by norm_num) (hTb i) (hSb j) (hcomm i j)
  filter_upwards [hTd,hSd,ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ht i j))]
    with a hTd hSd hc
  intro B hB
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro A hA
  have hcQ (j : ℕ) : Commute A (S j a) := commutes_of_dense_contraction_tests (Q a)
    (fun i => T i a) hTd (S j a) (fun i => hc i j) A hA
  exact (commutes_of_dense_contraction_tests (R a) (fun j => S j a) hSd A
    (fun j => (hcQ j).symm) B hB).eq.symm

end Kadison.Decomposable

end

end
end

end OAI
