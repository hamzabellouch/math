import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetConvolution

namespace OAI

/-! Fixed spatial translations on finite bounded jets, including convolution covariance. -/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets

open MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A fixed translation does not increase any derivative norm. -/
def translation (k : ℕ) (a : E) (J : Space E F k) : Space E F k :=
  ofFunction E F k (fun x => function E F k J (x+a))
    ((function_contDiff E F k J).comp (contDiff_id.add contDiff_const)) ‖J‖
    (fun n hn x => by
      rw [iteratedFDeriv_comp_add_right]
      exact norm_iteratedFDeriv_le E F k J n hn (x+a))

@[simp] theorem function_translation (k : ℕ) (a : E) (J : Space E F k) (x : E) :
    function E F k (translation E F k a J) x = function E F k J (x+a) :=
  function_ofFunction E F k _ _ _ _ x

theorem norm_translation_le (k : ℕ) (a : E) (J : Space E F k) :
    ‖translation E F k a J‖ ≤ ‖J‖ :=
  norm_ofFunction_le E F k _ _ _ _ (norm_nonneg J)

def translationCLM (k : ℕ) (a : E) : Space E F k →L[ℝ] Space E F k :=
  LinearMap.mkContinuous
    { toFun := translation E F k a
      map_add' := by
        intro J K
        apply function_injective E F k
        apply BoundedContinuousFunction.ext
        intro x
        simp only [function_translation, function_add]
      map_smul' := by
        intro c J
        apply function_injective E F k
        apply BoundedContinuousFunction.ext
        intro x
        simp only [function_translation, function_smul, RingHom.id_apply] }
    1 (fun J => (norm_translation_le E F k a J).trans_eq (one_mul ‖J‖).symm)

@[simp] theorem translationCLM_apply (k : ℕ) (a : E) (J : Space E F k) :
    translationCLM E F k a J = translation E F k a J := rfl

theorem translation_eq_self (k : ℕ) (a : E) (J : Space E F k)
    (h : ∀ x, function E F k J (x+a) = function E F k J x) :
    translationCLM E F k a J = J := by
  apply function_injective E F k
  apply BoundedContinuousFunction.ext
  intro x
  exact (function_translation E F k a J x).trans (h x)

section Convolution

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace F]

theorem translation_convolution (k : ℕ) (a : E) (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (J : Space E F k) :
    translationCLM E F k a (convolution E F k μ w hw J) =
      convolution E F k μ w hw (translationCLM E F k a J) := by
  apply function_injective E F k
  apply BoundedContinuousFunction.ext
  intro x
  rw [translationCLM_apply, function_translation, function_convolution, function_convolution]
  simp_rw [translationCLM_apply, function_translation]
  apply integral_congr_ae
  filter_upwards [] with y
  congr 2
  abel

end Convolution
end ForcedComputation.BoundedSpatialJets

end

end OAI
