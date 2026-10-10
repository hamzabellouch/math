import Mathlib
import OAI.Analysis.Commutator.CountableStarHomTests
import OAI.Analysis.Commutator.DecomposableOperator
import OAI.Analysis.Commutator.MatrixTowerGNS

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace Kadison.Decomposable

variable {Ω H A : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp H 2 μ)]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A]

omit [IsFiniteMeasure μ] in
theorem exists_common_tests
    (ρ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (σ : Ω → A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hm : ∀ a ξ,AEStronglyMeasurable (fun x => σ x a ξ) μ)
    (hact : ∀ a (f : Lp H 2 μ),ρ a f =ᵐ[μ] fun x => σ x a (f x)) :
    ∃ (test : ℕ → Ω → H →L[ℂ] H)
      (ht : ∀ n ξ,AEStronglyMeasurable (fun x => test n x ξ) μ)
      (hb : ∀ n,∀ᵐ x ∂μ,‖test n x‖≤1),
      (∀ n,operator μ (test n) (ht n) (hb n)∈NormalGNS.bicommutant ρ.range) ∧
      (∀ n,∀ᵐ x ∂μ,test n x∈NormalGNS.bicommutant (σ x).range) ∧
      (∀ᵐ x ∂μ,∀ T : H →L[ℂ] H,T∈NormalGNS.bicommutant (σ x).range → ‖T‖≤1 →
        ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) x ξ) atTop (𝓝 (T ξ))) ∧
      (∀ T : Lp H 2 μ →L[ℂ] Lp H 2 μ,T∈NormalGNS.bicommutant ρ.range → ‖T‖≤1 →
        ∃ k : ℕ → ℕ,∀ f,Tendsto
          (fun n => operator μ (test (k n)) (ht (k n)) (hb (k n)) f) atTop (𝓝 (T f))) := by
  let test : ℕ → Ω → H →L[ℂ] H := fun n x => σ x (countableContractions (A:=A) n)
  have ht : ∀ n ξ,AEStronglyMeasurable (fun x => test n x ξ) μ :=
    fun n ξ => hm _ ξ
  have hb : ∀ n,∀ᵐ x ∂μ,‖test n x‖≤1 := fun n => Eventually.of_forall (fun x =>
    (NonUnitalStarAlgHom.norm_apply_le (σ x) _).trans (countableContractions_norm n))
  have he (n : ℕ) : operator μ (test n) (ht n) (hb n)=ρ (countableContractions (A:=A) n) := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (operator_ae μ (test n) (ht n) (hb n) f).trans (hact _ f).symm
  refine ⟨test,ht,hb,?_,?_,?_,?_⟩
  · intro n
    rw [he]
    exact NormalGNS.subset_bicommutant ρ.range ⟨_,rfl⟩
  · intro n
    exact Eventually.of_forall (fun x => NormalGNS.subset_bicommutant (σ x).range ⟨_,rfl⟩)
  · apply Eventually.of_forall
    intro x T hT hn
    exact countableContractions_strong_dense (σ x) T
      ((NormalGNS.mem_bicommutant _ _).mp hT) hn
  · intro T hT hn
    obtain ⟨k,hk⟩ := countableContractions_strong_dense ρ T
      ((NormalGNS.mem_bicommutant _ _).mp hT) hn
    refine ⟨k,?_⟩
    intro f
    simpa only [he] using hk f

end Kadison.Decomposable

end

end
end

end OAI
