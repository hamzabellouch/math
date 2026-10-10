import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.FlowSmooth

namespace OAI

/-! Smooth dependence on the initial phase for a nonautonomous equation,
obtained by adjoining phase as an autonomous coordinate. -/

noncomputable section
namespace ForcedComputation.Flow
open scoped ContDiff NNReal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem transition_contDiff (V : C(ℝ × E, E))
    (hV : ContDiff ℝ ∞ (V : ℝ × E → E)) {L : ℝ≥0}
    (hL : LipschitzWith L V) {Ω : ℝ → ℝ → E → E}
    (hode : ∀ a t x, HasDerivAt (fun s => Ω a s x) (V (a + t, Ω a t x)) t)
    (hzero : ∀ a x, Ω a 0 x = x) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × E) => Ω p.1 p.2.1 p.2.2) := by
  let Z : C(ℝ × E, ℝ × E) :=
    ⟨fun p => (1, V p), continuous_const.prodMk V.continuous⟩
  have hZ : ContDiff ℝ ∞ (Z : ℝ × E → ℝ × E) := contDiff_const.prodMk hV
  have hZL : LipschitzWith L Z := by
    change LipschitzWith L (fun p : ℝ × E => ((1 : ℝ), V p))
    simpa only [max_eq_right (show (0 : ℝ≥0) ≤ L from bot_le)] using
      (LipschitzWith.const (1 : ℝ)).prodMk hL
  let Ψ : ℝ → (ℝ × E) → ℝ × E := fun t p => (p.1 + t, Ω p.1 t p.2)
  have hΨ (t : ℝ) (p : ℝ × E) :
      HasDerivAt (fun s => Ψ s p) (Z (Ψ t p)) t :=
    ((hasDerivAt_id t).const_add p.1).prodMk (hode p.1 t p.2)
  have hi (p : ℝ × E) : Ψ 0 p = p := by simp only [Ψ, add_zero, hzero]
  have hs := flow_contDiff Z hZ hZL hΨ hi
  have hq : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × E) => (p.2.1, (p.1, p.2.2))) :=
    contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd)
  exact hs.snd.comp hq

theorem transition_backward_contDiff (V : C(ℝ × E, E))
    (hV : ContDiff ℝ ∞ (V : ℝ × E → E)) {L : ℝ≥0}
    (hL : LipschitzWith L V) {Ω : ℝ → ℝ → E → E}
    (hode : ∀ a t x, HasDerivAt (fun s => Ω a s x) (V (a + t, Ω a t x)) t)
    (hzero : ∀ a x, Ω a 0 x = x) :
    ContDiff ℝ ∞ (fun p : ℝ × E => Ω p.1 (-p.1) p.2) :=
  (transition_contDiff V hV hL hode hzero).comp
    (contDiff_fst.prodMk (contDiff_fst.neg.prodMk contDiff_snd))

end ForcedComputation.Flow

end

end OAI
