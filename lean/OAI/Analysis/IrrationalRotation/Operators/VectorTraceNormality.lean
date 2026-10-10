import OAI.Analysis.IrrationalRotation.Model.NormalAffiliation
import OAI.Analysis.IrrationalRotation.Operators.VectorTraceState

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Invariant233

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in

theorem tendsto_vectorTrace_of_strong {ι : Type*} {L : Filter ι}
    (ξ : H) (a : ι → H →L[ℂ] H) (b : H →L[ℂ] H)
    (hab : ∀ x : H, Tendsto (fun i => a i x) L (𝓝 (b x))) :
    Tendsto (fun i => vectorTrace ξ (a i)) L (𝓝 (vectorTrace ξ b)) := by
  exact tendsto_const_nhds.inner (hab ξ)

theorem IsFaithfulTracialVector.toTracialState_normal
    {M : VonNeumannAlgebra H} {ξ : H} (h : IsFaithfulTracialVector M ξ) :
    IsNormalFaithfulTracialState M h.toTracialState := by
  constructor
  · exact fun a ha hz => h.toTracialState_faithful a ha hz
  · intro ι L _ a b _ hab
    exact tendsto_vectorTrace_of_strong ξ
      (fun i => (a i : H →L[ℂ] H)) (b : H →L[ℂ] H) hab

theorem IsNormalFaithfulTracialState.tendsto_of_strong_small
    {M : VonNeumannAlgebra H} {τ : TracialState M}
    (h : IsNormalFaithfulTracialState M τ)
    {ι : Type} (L : Filter ι) [L.NeBot] (a : ι → M) (b : M)
    (hbound : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (hab : ∀ x : H, Tendsto (fun i => (a i : H →L[ℂ] H) x) L
      (𝓝 ((b : H →L[ℂ] H) x))) :
    Tendsto (fun i => τ (a i)) L (𝓝 (τ b)) := by
  have h' := h.2 (ULift.{u} ι) (Filter.map ULift.up L) inferInstance
    (fun i => a i.down) b
    (by obtain ⟨C, hC⟩ := hbound; exact ⟨C, fun i => hC i.down⟩)
    (fun x => ?_)
  · simpa only [Filter.tendsto_map'_iff, Function.comp_def, ULift.down_up] using h'
  · simpa only [Filter.tendsto_map'_iff, Function.comp_def, ULift.down_up] using hab x

end Invariant233

end

end OAI
