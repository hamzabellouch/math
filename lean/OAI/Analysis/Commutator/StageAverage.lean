import Mathlib
import OAI.Analysis.Commutator.Average
import OAI.Analysis.Commutator.CompactAverage
import OAI.Analysis.Commutator.WeakConvergence

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory MeasureTheory.Measure Filter

namespace Kadison.CompactAverage

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (G : ℕ → Type*) [∀ n, Group (G n)] [∀ n, TopologicalSpace (G n)]
  [∀ n, IsTopologicalGroup (G n)] [∀ n, CompactSpace (G n)]
  [∀ n, MeasurableSpace (G n)] [∀ n, BorelSpace (G n)]

variable (U : ∀ n, G n →* (H ≃ₗᵢ[ℂ] H))
  (hU : ∀ n x, Continuous fun g => U n g x)
  (hnest : ∀ i j, i≤j → ∀ g : G i, ∃ k : G j, U j k=U i g)

variable (μ : ∀ n, Measure (G n)) [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsMulLeftInvariant (μ n)]

variable (Y : H →L[ℂ] H)

omit [∀ n, IsMulLeftInvariant (μ n)] in
include hU in
lemma scalar_integrable (n : ℕ) (x y : H) :
    Integrable (fun g => inner ℂ (conjugate (U n) Y g x) y) (μ n) :=
  ((conjugate_continuous (U n) (hU n) Y x).inner continuous_const).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

include hU hnest μ in
theorem exists_stage_average {ι : Type*} (a : ι → H →L[ℂ] H) (C : ι → ℝ)
    (hC : ∀ i, 0≤C i)
    (hb : ∀ n g i, ‖conjugate (U n) Y g * a i-a i*conjugate (U n) Y g‖≤C i)
    (p q s : H →L[ℂ] H)
    (hc : ∀ n g, p*(conjugate (U n) Y g*s-s*conjugate (U n) Y g)*q = p*(Y*s-s*Y)*q) :
    ∃ V : H →L[ℂ] H, ‖V‖≤‖Y‖ ∧
      (∀ n g, V*(U n g : H →L[ℂ] H)=(U n g : H →L[ℂ] H)*V) ∧
      (∀ i, ‖V*a i-a i*V‖≤C i) ∧ p*(V*s-s*V)*q=p*(Y*s-s*Y)*q := by
  choose T hT hcomm hcoeff using fun n => exists_average (U n) (hU n) Y (μ n)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨V,hV,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω T ‖Y‖ (norm_nonneg _) hT
  have hconv : WeakOperatorLimit.Converges T V (ω:Filter ℕ) := hlim
  refine ⟨V,hV,?_,?_,?_⟩
  · intro n g
    apply hconv.commutes
    have he : ∀ᶠ j : ℕ in atTop, T j*(U n g : H →L[ℂ] H)=(U n g : H →L[ℂ] H)*T j := by
      filter_upwards [eventually_ge_atTop n] with j hj
      obtain ⟨k,hk⟩ := hnest n j hj g
      simpa only [hk] using hcomm j k
    exact (Ultrafilter.of_le atTop) he
  · intro i
    apply hconv.commutator_norm (a i) (hC i)
    exact Eventually.of_forall fun n => WeakOperatorIntegral.commutator_norm (μ n)
      (conjugate (U n) Y) (scalar_integrable G U hU μ Y n) (T n) (hcoeff n)
      (a i) (hC i) (fun g => hb n g i)
  · apply (hconv.commutator s).preserves_sandwich
    exact Eventually.of_forall fun n => WeakOperatorIntegral.preserves_compressed_commutator
      (μ n) (conjugate (U n) Y) (scalar_integrable G U hU μ Y n) (T n) (hcoeff n)
      p q s (p*(Y*s-s*Y)*q) (hc n)

end Kadison.CompactAverage

end

end
end

end OAI
