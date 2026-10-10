import OAI.NumberTheory.DukePrimeDegree.Geometry.TransverseRootFibers
import OAI.NumberTheory.DukePrimeDegree.Entropy.FineReturnObservation

namespace OAI

/-! # Return observations in actual upper-root quotient coordinates -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

namespace UpperRootBox
variable {n : ℕ} {g : G n}

theorem exists_measurable_logDiagonal (B : UpperRootBox n g) :
    ∃ f : X n → Fin n → ℝ, Measurable f ∧
      ∀ z : B.domain, f (B.param z)=transverseLogDiagonal z.val.1 := by
  obtain ⟨f,hf,he⟩ := B.embedding.measurableEmbedding.exists_measurable_extend
    ((continuous_transverseLogDiagonal n).measurable.comp
      (measurable_fst.comp measurable_subtype_coe)) (fun _ => inferInstance)
  exact ⟨f,hf,fun z => congrFun he z⟩

theorem exists_fine_logDiagonal_return_observation (B : UpperRootBox n g)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    {T : X n → X n} (hT : Ergodic T μ) (hE : MeasurableEmbedding T)
    {S : Set (X n)} (hS : MeasurableSet S) (hSB : S ⊆ B.range)
    (htail : ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ μ (firstReturnLevel T S m) ≠ 0)
    {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ z : B.domain, B.param z ∈ S →
      ∀ i, |transverseLogDiagonal z.val.1 i| ≤ R) :
    ∃ (K : ℕ → ℕ) (C : ∀ m, X n → Fin (K m)),
      (∀ m, Measurable (C m)) ∧
      Summable (fun z : Option (Σ m : ℕ, Fin (K m)) =>
        Real.negMulLog (μ.real {x | returnRefinement T S C x=z})) ∧
      ∀ᵐ x ∂μ, ∀ y, (∀ k : ℕ,
        returnRefinement T S C (T^[k] y)=returnRefinement T S C (T^[k] x)) →
        ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, T^[k] x ∈ S ∧ T^[k] y ∈ S ∧
          ∀ z w : B.domain, B.param z=T^[k] x → B.param w=T^[k] y →
            ∀ i, |transverseLogDiagonal w.val.1 i-transverseLogDiagonal z.val.1 i| < ε := by
  obtain ⟨f,hf,hval⟩ := B.exists_measurable_logDiagonal
  have hfb : ∀ x ∈ S, ∀ i, |f x i| ≤ R := by
    intro x hx
    obtain ⟨z,rfl⟩ := hSB hx
    rw [hval z]
    exact hbound z hx
  obtain ⟨K,C,hC,hent,hfine⟩ := exists_fine_return_observation
    μ hT hE hS htail f hf hR hfb
  refine ⟨K,C,hC,hent,?_⟩
  filter_upwards [hfine] with x hx
  intro y hy ε hε
  obtain ⟨k,hkx,hky,hk⟩ := hx y hy ε hε
  refine ⟨k,hkx,hky,?_⟩
  intro z w hz hw i
  have h := hk i
  rw [←hz,←hw,hval z,hval w] at h
  exact h

end UpperRootBox
end DukePrimeDegree

end

end OAI
