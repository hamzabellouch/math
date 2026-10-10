import OAI.Geometry.SurfaceImmersion.Correction.FixedMeanSubstitution
import OAI.Geometry.Immersion.ClosedSurface.MeanSupport

namespace OAI

/-! Assemble finitely many actual mean operators with a common derivative
loss while retaining their scale-independent majorants. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma MeanBounds.mono_loss {U : Set E} {s : ℝ} {reference : E → F} {r : ℝ}
    {L L' : ℕ} {T : ℝ → (E → F) → E → F} {B K : ℕ → ℝ → ℝ}
    (hT : MeanBounds U s reference r L T B K) (hL : L ≤ L') :
    MeanBounds U s reference r L' T B K := by
  refine ⟨hT.B_pos, hT.K_pos, hT.smooth, ?_, ?_⟩
  · intro η hη hη1 m C f hC hf hb hbf
    exact hT.value η hη hη1 m C f hC hf hb (hbf.mono_order (Nat.add_le_add_left hL m))
  · intro η hη hη1 m C D f g hC hD hf hg hbf hbg hF hG hFG
    exact hT.difference η hη hη1 m C D f g hC hD hf hg hbf hbg
      (hF.mono_order (Nat.add_le_add_left hL m)) (hG.mono_order (Nat.add_le_add_left hL m))
      (hFG.mono_order (Nat.add_le_add_left hL m))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma rescaledMean_finset {ι : Type*} (a : Finset ι) (η : ℝ)
    (A : ι → (E → F) → E → F) :
    rescaledMean η (fun f x => ∑ i ∈ a, A i f x) =
      fun θ f x => ∑ i ∈ a, rescaledMean η (A i) θ f x := by
  funext θ f x
  simp only [rescaledMean, Pi.smul_apply, Finset.smul_sum]

lemma MeanBounds.finset_rescaled {ι : Type*} {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} (hs : 0 ≤ s) {reference : E → F} {r η : ℝ}
    (a : Finset ι) (A : ι → (E → F) → E → F) (L : ι → ℕ) (L' : ℕ)
    (B K : ι → ℕ → ℝ → ℝ)
    (hL : ∀ i ∈ a, L i ≤ L')
    (hA : ∀ i ∈ a, MeanBounds U s reference r (L i) (rescaledMean η (A i)) (B i) (K i)) :
    MeanBounds U s reference r L' (rescaledMean η (fun f x => ∑ i ∈ a, A i f x))
      (fun m C => 1 + ∑ i ∈ a, B i m C) (fun m C => 1 + ∑ i ∈ a, K i m C) := by
  rw [rescaledMean_finset]
  exact MeanBounds.finset_sum hU hs a (fun i => rescaledMean η (A i)) B K
    (fun i hi => (hA i hi).mono_loss (hL i hi))

end ClosedSurfaceR4.FiniteMean

end

end OAI
