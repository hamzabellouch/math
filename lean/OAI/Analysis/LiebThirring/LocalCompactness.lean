import OAI.Analysis.LiebThirring.ContinuousRepresentative

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

def continuousRep (u : H1C) : ℝ → ℂ := (h1_exists_continuous_rep (toH1 u)).choose
lemma continuousRep_continuous (u : H1C) : Continuous (continuousRep u) :=
  (h1_exists_continuous_rep (toH1 u)).choose_spec.1
lemma continuousRep_ae (u : H1C) : (fun x ↦ valL u x) =ᵐ[volume] continuousRep u :=
  (h1_exists_continuous_rep (toH1 u)).choose_spec.2.1
lemma valL_norm_le (u : H1C) : ‖valL u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [h1_norm_sq]
  exact le_add_of_nonneg_right (sq_nonneg _)
lemma gradL_norm_le (u : H1C) : ‖gradL u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [h1_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)
lemma continuousRep_norm (u : H1C) (x : ℝ) : ‖continuousRep u x‖ ≤ 4*‖u‖ := by
  have h := (h1_exists_continuous_rep (toH1 u)).choose_spec.2.2.1 x
  simp only [toLp_toH1,grad_toLp_toH1] at h
  change ‖continuousRep u x‖ ≤ _ at h
  linarith [valL_norm_le u, gradL_norm_le u]
lemma continuousRep_holder (u : H1C) (x y : ℝ) :
    ‖continuousRep u x-continuousRep u y‖ ≤ 2*‖u‖*Real.sqrt |x-y| := by
  have h := (h1_exists_continuous_rep (toH1 u)).choose_spec.2.2.2 x y
  simp only [grad_toLp_toH1] at h
  change ‖continuousRep u x-continuousRep u y‖ ≤ _ at h
  have hg := mul_le_mul_of_nonneg_right (gradL_norm_le u) (Real.sqrt_nonneg |x-y|)
  linarith

abbrev Interval (R : ℝ) := Icc (-R) R

def localRep (R : ℝ) (u : H1C) : Interval R →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ continuousRep u x, (continuousRep_continuous u).comp continuous_subtype_val⟩

lemma localRep_compact (R : ℝ) :
    IsCompact (closure (localRep R '' Metric.closedBall 0 1)) := by
  let A := localRep R '' Metric.closedBall 0 1
  have hin : ∀ (f : Interval R →ᵇ ℂ) (x : Interval R), f ∈ A →
      f x ∈ Metric.closedBall 0 4 := by
    rintro f x ⟨u,hu,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right] at hu ⊢
    exact (continuousRep_norm u x).trans (by linarith)
  have heq : Equicontinuous ((↑) : A → Interval R → ℂ) :=
    (Metric.uniformEquicontinuous_of_continuity_modulus (fun t ↦ 2*Real.sqrt t)
      (by
        have h : Tendsto (fun t : ℝ ↦ 2*Real.sqrt t) (𝓝 0) (𝓝 (2*Real.sqrt 0)) :=
          tendsto_const_nhds.mul (Real.continuous_sqrt.tendsto (0:ℝ))
        simpa only [Real.sqrt_zero,mul_zero] using h) _ (by
        intro x y f
        rcases f.2 with ⟨u,hu,huf⟩
        have hn : ‖u‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hu
        have h : ‖continuousRep u x-continuousRep u y‖ ≤ 2*Real.sqrt |(x:ℝ)-y| := by
          exact (continuousRep_holder u x y).trans (by
            nlinarith [Real.sqrt_nonneg |(x:ℝ)-y|])
        rw [← huf]
        simpa only [dist_eq_norm,Real.norm_eq_abs,Subtype.dist_eq,localRep,
          BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk] using h)).equicontinuous
  exact BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 4)
    (isCompact_closedBall 0 4) A hin heq

end SharpLiebThirring.OperatorProof

end

end OAI
