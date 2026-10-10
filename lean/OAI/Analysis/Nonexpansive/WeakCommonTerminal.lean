import OAI.Analysis.Nonexpansive.CommonTerminal
import OAI.Analysis.Nonexpansive.TerminalSequence
import OAI.Analysis.Nonexpansive.Basic

namespace OAI

/-!
# A common actual resolvent terminal for weak prediction detectors

The scalar convergence is derived from weak convergence of the fully evaluated
predictions.  The displacement convergence is the proved estimate for the actual
resolvent terminal sequence and actual generated maps.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {K : Set X}

/-- A continuous linear functional converts an actual weak prediction limit to
the scalar detector limit.  No weak continuity of a nonlinear map is used. -/
theorem detector_tendsto_of_weak_tendsto {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {J : Type*} {l : Filter J} (f : X →L[ℝ] ℝ) (y z : X) (q : J → X)
    (hq : Tendsto (fun j => toWeakSpace ℝ X (q j)) l
      (𝓝 (toWeakSpace ℝ X z))) :
    Tendsto (fun j => f (y - q j)) l (𝓝 (f (y - z))) := by
  have hcont : Continuous (fun w : WeakSpace ℝ X => f ((toWeakSpace ℝ X).symm w)) :=
    WeakBilin.eval_continuous (topDualPairing ℝ X).flip f
  have heval := hcont.continuousAt.tendsto.comp hq
  simpa only [LinearEquiv.symm_apply_apply, map_sub] using
    (tendsto_const_nhds.sub heval :
      Tendsto (fun j => f y - f ((toWeakSpace ℝ X).symm (toWeakSpace ℝ X (q j)))) l
        (𝓝 (f y - f ((toWeakSpace ℝ X).symm (toWeakSpace ℝ X z)))))

/-- Choose one index of the actual terminal resolvent sequence satisfying every
finite weak prediction detector and every fixed generated map's total bound. -/
theorem exists_common_terminalSequence
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1) (x : K)
    {I J : Type*} [Finite I] [Fintype J]
    {l : Filter ℕ} [NeBot l] (hl : l ≤ atTop)
    (q : I → K → K) (y z : I → K) (f : I → X →L[ℝ] ℝ) (e : I → ℝ)
    (he : ∀ i, 0 < e i)
    (hz : ∀ i, Tendsto
      (fun j => toWeakSpace ℝ X (q i (terminalSequence hKclosed hKconvex T hT x j)))
      l (𝓝 (toWeakSpace ℝ X (z i))))
    (hdet : ∀ i, 1 - e i ≤ f i ((y i : X) - z i))
    (G : J → K → K) (hG : ∀ a, Generated hKclosed hKconvex T hT (G a))
    (M : ℝ) (hM : 0 < M) :
    ∃ j,
      (∀ i, 1 - 2 * e i ≤
        f i ((y i : X) - q i (terminalSequence hKclosed hKconvex T hT x j))) ∧
      (∑ a, ‖(G a (terminalSequence hKclosed hKconvex T hT x j) : X) -
        terminalSequence hKclosed hKconvex T hT x j‖) ≤ M := by
  apply common_terminal_of_tendsto_mono hl e
    (fun i => f i ((y i : X) - z i))
    (fun i j => f i ((y i : X) - q i (terminalSequence hKclosed hKconvex T hT x j)))
    (fun j => ∑ a, ‖(G a (terminalSequence hKclosed hKconvex T hT x j) : X) -
      terminalSequence hKclosed hKconvex T hT x j‖) M he hdet
  · intro i
    exact detector_tendsto_of_weak_tendsto (f i) (y i) (z i)
      (fun j => q i (terminalSequence hKclosed hKconvex T hT x j)) (hz i)
  · exact terminalSequence_finite_displacement_tendsto hKclosed hKconvex T hT
      hdiam G hG x
  · exact hM

end ReflexiveFixedPoints

end

end OAI
