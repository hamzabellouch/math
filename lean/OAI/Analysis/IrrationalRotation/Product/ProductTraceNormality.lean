import OAI.Analysis.IrrationalRotation.Operators.VectorTraceNormality
import OAI.Analysis.IrrationalRotation.Spectral.ProductTracialSpectral

namespace OAI

noncomputable section
open scoped ENNReal

namespace Invariant233.ProductModel

theorem traceVectorTracialState_normal (θ : ℕ → ℝ) :
    IsNormalFaithfulTracialState (factor θ)
      (traceVector_faithfulTracial θ).toTracialState :=
  (traceVector_faithfulTracial θ).toTracialState_normal

theorem exists_normalTracialState_weightedOperator_spectral_bundle
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Set.Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hcost : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    ∃ τ : TracialState (factor θ),
      IsNormalFaithfulTracialState (factor θ) τ ∧
      (∀ A : factor θ, τ A = vectorTrace traceVector (A : Hilbert →L[ℂ] Hilbert)) ∧
      ∃ T : factor θ, (T : Hilbert →L[ℂ] Hilbert) = weightedOperator θ c ∧
        T ≠ 0 ∧ NormQuasinilpotent T ∧ spectrum ℂ T = {0} ∧
        fugledeKadisonDeterminant τ T = 0 := by
  refine ⟨(traceVector_faithfulTracial θ).toTracialState,
    traceVectorTracialState_normal θ, fun _ => rfl,
    ⟨weightedOperator θ c, weightedOperator_mem_factor θ c⟩, rfl, ?_,
    weightedOperator_normQuasinilpotent θ c (fun i => (hθ01 i).1) hc hθ hcost,
    weightedOperator_factorSpectrum_eq_singleton_zero θ c
      (fun i => (hθ01 i).1) hc hθ hcost,
    weightedOperator_tracialDeterminant_zero_of_cost_divergence θ c hθ01 hc hθ hcost⟩
  intro hz
  exact weightedOperator_ne_zero θ c (fun i => (hθ01 i).1) hc hθ
    (congrArg Subtype.val hz)

theorem exists_normalTracialState_weightedOperator_block_spectral_bundle
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, K j ^ 2 ≤ C j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Set.Ico (0 : ℝ) 1) (hθ : Summable θ)
    (hlower : ∀ i, 1 / ((m (e i).1 : ℝ) * K (e i).1) ≤ θ i) :
    ∃ τ : TracialState (factor θ),
      IsNormalFaithfulTracialState (factor θ) τ ∧
      (∀ A : factor θ, τ A = vectorTrace traceVector (A : Hilbert →L[ℂ] Hilbert)) ∧
      ∃ T : factor θ, (T : Hilbert →L[ℂ] Hilbert) =
          weightedOperator θ (fun i => C (e i).1) ∧
        T ≠ 0 ∧ NormQuasinilpotent T ∧ spectrum ℂ T = {0} ∧
        fugledeKadisonDeterminant τ T = 0 := by
  exact exists_normalTracialState_weightedOperator_spectral_bundle θ
    (fun i => C (e i).1) hθ01 (fun i => (sq_nonneg _).trans (hC _)) hθ
    (tsum_block_coordinate_cost_eq_top m hm K C hK hC e θ hlower)

end Invariant233.ProductModel

end

end OAI
