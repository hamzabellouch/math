import OAI.Analysis.BoundedHochschild.FiniteCoefficientExtension
import OAI.Analysis.BoundedHochschild.CompletelyPositiveLimits

namespace OAI

/-! Unital completely positive extension, without a separability hypothesis.
Finite coefficient extensions are joined by a weak-operator ultralimit. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

theorem exists_unital_completelyPositive_extension
    (S : Submodule ℂ A) (h1 : (1 : A) ∈ S) (hstar : ∀ a ∈ S, star a ∈ S)
    (φ : S →ₗ[ℂ] (H →L[ℂ] H)) (hφ1 : φ ⟨1, h1⟩ = 1)
    (hφ : ∀ n (X : operatorSystemMatrices S n),
      0 ≤ (X : CStarMatrix (Fin n) (Fin n) A) →
        0 ≤ operatorSystemAmplification S φ n X) :
    ∃ Φ : CompletelyPositiveMap A (H →L[ℂ] H),
      Φ 1 = 1 ∧ (∀ a, ‖Φ a‖ ≤ ‖a‖) ∧ ∀ a : S, Φ (a : A) = φ a := by
  classical
  have hex := exists_finite_coefficient_extension S h1 hstar φ hφ1 hφ
  choose Ψ hΨ hcoeff using hex
  let ω : Ultrafilter (Finset H) := Ultrafilter.of atTop
  have hω : (ω : Filter (Finset H)) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨Φ, hΦ, ht⟩ := exists_completelyPositive_ultralimit ω Ψ zero_le_one
    (fun s a => by simpa only [one_mul] using hΨ s a)
  have hext (a : S) : Φ (a : A) = φ a := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply ext_inner_left ℂ
    intro η
    have he : (fun s => inner ℂ η (Ψ s (a : A) ξ)) =ᶠ[ω]
        (fun _ => inner ℂ η (φ a ξ)) := by
      filter_upwards [(eventually_finset_mem_atTop ξ).filter_mono hω,
        (eventually_finset_mem_atTop η).filter_mono hω] with s hξ hη
      exact hcoeff s a ξ hξ η hη
    exact tendsto_nhds_unique (ht (a : A) ξ η) (tendsto_const_nhds.congr' he.symm)
  exact ⟨Φ, (hext ⟨1, h1⟩).trans hφ1,
    fun a => by simpa only [one_mul] using hΦ a, hext⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
