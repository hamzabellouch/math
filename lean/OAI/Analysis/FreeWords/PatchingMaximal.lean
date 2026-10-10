import Mathlib
import OAI.Analysis.FreeWords.PartialUnitaryChain
import OAI.Analysis.FreeWords.PartialWords

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKMatrixQuantization

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

variable (W : Set (PatchingWord (ConcreteAlgebra M))) (B : ℝ → ℝ) (T : ℝ)

def PatchingBounds (v : PartialUnitary (ConcreteAlgebra M)) : Prop :=
  (τ.map v.support).re ≤ T ∧ ∀ w∈W, ‖τ.map (w.value v.power)‖≤B (τ.map v.support).re

theorem maximal_patching_bounds (hB : Continuous B) (hB0 : 0≤B 0) (hT : 0≤T) :
    ∃ v : PartialUnitary (ConcreteAlgebra M), Maximal (PatchingBounds τ W B T) v := by
  classical
  apply zorn_le₀ {v | PatchingBounds τ W B T v}
  intro c hc hchain
  rcases c.eq_empty_or_nonempty with rfl | hne
  · refine ⟨PartialUnitary.zero,?_,by simp⟩
    constructor
    · simpa only [PartialUnitary.zero,PartialUnitary.support,map_zero,Complex.zero_re] using hT
    · intro w hw
      simpa only [PartialUnitary.zero,PatchingWord.value_zero,map_zero,norm_zero,
        PartialUnitary.support,Complex.zero_re] using hB0
  · let : Nonempty c := hne.to_subtype
    let : LinearOrder c := hchain.lt_of_le.linearOrder
    obtain ⟨v,hv,hlim⟩ := PartialUnitary.directed_limit τ (fun i:c => i.val) (fun _ _ h => h)
    have ht : Tendsto (fun i:c => (τ.map i.val.support).re) atTop (𝓝 (τ.map v.support).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp (tendsto_gns_trace τ (hlim 0))
    refine ⟨v,⟨?_,?_⟩,fun z hz => hv ⟨z,hz⟩⟩
    · exact le_of_tendsto ht (Eventually.of_forall (fun i:c => (hc i.property).1))
    · intro w hw
      exact le_of_tendsto_of_tendsto (PatchingWord.tendsto_value τ hlim w).norm
        (hB.continuousAt.tendsto.comp ht)
        (Eventually.of_forall (fun i:c => (hc i.property).2 w hw))

end

end KKLocalPatching
end

end OAI
