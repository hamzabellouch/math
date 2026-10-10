import OAI.Analysis.OperatorAlgebra.ScalarVectorDensity
import OAI.Analysis.ModularTheory.CoreIntegrals
import Mathlib.Topology.UniformSpace.UniformApproximation

namespace OAI

/-! Strong continuity of the concrete right-regular modular action. -/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology InnerProductSpace

namespace WeakPureInfiniteness

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]

lemma isClosed_continuous_operator_orbit (V : ℝ → K →L[ℂ] K)
    (hV : ∀ t, ‖V t‖ ≤ 1) : IsClosed {x | Continuous (fun t => V t x)} := by
  apply isSeqClosed_iff_isClosed.mp
  intro x z hx hz
  have hu : TendstoUniformly (fun n t => V t (x n)) (fun t => V t z) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hz ε hε] with n hn t
    have hb : dist (V t z) (V t (x n)) ≤ dist z (x n) := by
      simp only [dist_eq_norm, ← map_sub]
      exact ((V t).le_opNorm _).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hV t) (norm_nonneg _))
    exact hb.trans_lt (by simpa only [dist_comm] using hn)
  exact hu.continuous (Filter.Eventually.of_forall hx).frequently

lemma continuous_operator_apply_varying (V : ℝ → K →L[ℂ] K)
    (hV : ∀ t, ‖V t‖ ≤ 1) (hc : ∀ x, Continuous (fun t => V t x))
    (F : ℝ → K) (hF : Continuous F) : Continuous (fun t => V t (F t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hd₁⟩ := Metric.continuousAt_iff.mp
    hF.continuousAt (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hδ₂, hd₂⟩ := Metric.continuousAt_iff.mp
    (hc (F t)).continuousAt (ε / 2) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {s} hs => ?_⟩
  have hb : dist (V s (F s)) (V s (F t)) ≤ dist (F s) (F t) := by
    simp only [dist_eq_norm, ← map_sub]
    exact ((V s).le_opNorm _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hV s) (norm_nonneg _))
  exact (dist_triangle _ _ _).trans_lt (by
    have h₁ := hd₁ (hs.trans_le (min_le_left _ _))
    have h₂ := hd₂ (hs.trans_le (min_le_right _ _))
    linarith)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma pointwise_modularUnitary_norm_le (μ : Measure ℝ)
    (D : BoundedRecovery.RealSpectralCalculus H) (t : ℝ) :
    ‖pointwiseLpRepresentation μ (D.unitary t)‖ ≤ 1 := by
  apply (ContinuousLinearMap.norm_compLpL_le _).trans
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [D.norm_unitary_apply, one_mul]

lemma pointwise_modularUnitary_continuous (μ : Measure ℝ)
    (D : BoundedRecovery.RealSpectralCalculus H) (f : Lp H 2 μ) :
    Continuous (fun t => pointwiseLpRepresentation μ (D.unitary t) f) := by
  apply scalarVectorLp_induction μ
    (fun f => Continuous (fun t => pointwiseLpRepresentation μ (D.unitary t) f))
    (isClosed_continuous_operator_orbit _ (pointwise_modularUnitary_norm_le μ D))
    (fun f g hf hg => by
      simp only [map_add]
      exact hf.add hg) ?_ f
  intro g x
  have h : (fun t => pointwiseLpRepresentation μ (D.unitary t) (scalarVectorLp μ g x)) =
      fun t => scalarVectorLpCLM μ g (D.unitary t x) := by
    funext t
    exact scalarVectorLp_pointwise μ _ g x
  rw [h]
  exact (scalarVectorLpCLM μ g).continuous.comp (D.continuous_unitary_apply x)

lemma modularRightTranslation_continuous (D : BoundedRecovery.RealSpectralCalculus H)
    (f : Lp H 2 (volume : Measure ℝ)) :
    Continuous (fun t => modularRightTranslation volume D t f) := by
  exact continuous_operator_apply_varying
    (fun t => pointwiseLpRepresentation volume (D.unitary t))
    (pointwise_modularUnitary_norm_le volume D)
    (pointwise_modularUnitary_continuous volume D)
    (fun t => modularLpTranslate volume (-t) f)
    ((continuous_modularLpTranslate f).comp continuous_neg)

end WeakPureInfiniteness

end

end OAI
