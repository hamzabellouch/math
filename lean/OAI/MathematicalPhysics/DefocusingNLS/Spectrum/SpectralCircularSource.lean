import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularTail

namespace OAI

/-! Bounded coupled source fields for the two circular tail equations. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularSource_bound (L C : ℝ) (hL : 0 ≤ L)
    (N : ℝ → E₄ → E₄) (hN0 : ∀ t, ‖N t 0‖ ≤ C)
    (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (v : CircularTailSpace) (t : ℝ) :
    ‖N t (circularTailEvaluation v t)‖ ≤ L*‖v‖+C := by
  calc
    _ ≤ ‖N t (circularTailEvaluation v t)-N t 0‖+‖N t 0‖ := norm_le_norm_sub_add _ _
    _ ≤ L*‖circularTailEvaluation v t-0‖+C := add_le_add (hLip t _ _) (hN0 t)
    _ ≤ L*‖v‖+C := by
      rw [sub_zero]
      exact (add_le_add_iff_right C).mpr
        (mul_le_mul_of_nonneg_left (circularTailEvaluation_norm v t) hL)

noncomputable def boundedCircularSource (L C : ℝ) (hL : 0 ≤ L)
    (N : ℝ → E₄ → E₄) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (v : CircularTailSpace) : CircularTailSpace :=
  let hcont := hN.comp (continuous_id.prodMk (circularTailEvaluation_continuous v))
  (BoundedContinuousFunction.ofNormedAddCommGroup (fun t => (N t (circularTailEvaluation v t)).1)
    hcont.fst (L*‖v‖+C)
    (fun t => (norm_fst_le _).trans (circularSource_bound L C hL N hN0 hLip v t)),
   BoundedContinuousFunction.ofNormedAddCommGroup (fun t => (N t (circularTailEvaluation v t)).2)
    hcont.snd (L*‖v‖+C)
    (fun t => (norm_snd_le _).trans (circularSource_bound L C hL N hN0 hLip v t)))

theorem boundedCircularSource_evaluation (L C : ℝ) (hL : 0 ≤ L)
    (N : ℝ → E₄ → E₄) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (v : CircularTailSpace) (t : ℝ) :
    circularTailEvaluation (boundedCircularSource L C hL N hN hN0 hLip v) t=
      N t (circularTailEvaluation v t) := rfl

theorem boundedCircularSource_norm (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (N : ℝ → E₄ → E₄) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (v : CircularTailSpace) : ‖boundedCircularSource L C hL N hN hN0 hLip v‖ ≤ L*‖v‖+C := by
  apply max_le
  · apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro t
    exact (norm_fst_le _).trans (circularSource_bound L C hL N hN0 hLip v t)
  · apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro t
    exact (norm_snd_le _).trans (circularSource_bound L C hL N hN0 hLip v t)

theorem boundedCircularSource_difference (L C : ℝ) (hL : 0 ≤ L)
    (N : ℝ → E₄ → E₄) (hN : Continuous (Function.uncurry N))
    (hN0 : ∀ t, ‖N t 0‖ ≤ C) (hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖)
    (u v : CircularTailSpace) :
    ‖boundedCircularSource L C hL N hN hN0 hLip u-
      boundedCircularSource L C hL N hN hN0 hLip v‖ ≤ L*‖u-v‖ := by
  have hb (t : ℝ) : ‖N t (circularTailEvaluation u t)-N t (circularTailEvaluation v t)‖ ≤ L*‖u-v‖ := by
    apply (hLip t _ _).trans
    apply mul_le_mul_of_nonneg_left _ hL
    rw [← circularTailEvaluation_sub]
    exact circularTailEvaluation_norm (u-v) t
  apply max_le
  · apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro t
    exact (norm_fst_le (N t (circularTailEvaluation u t)-N t (circularTailEvaluation v t))).trans (hb t)
  · apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro t
    exact (norm_snd_le (N t (circularTailEvaluation u t)-N t (circularTailEvaluation v t))).trans (hb t)

end DefocusingNLS

end OAI
