import OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformLog

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic JointLogSeparation

 theorem interpolatedProfile_uniform (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (interpolatedProfile W a b ha hs hW σ t)≤C*(1+‖t‖)^n := by
  obtain ⟨T,A,hA,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (CompletedHeight.fixedLogReturnCLM a b ha) S
  obtain ⟨n,B,hB,hbound⟩ := compact_family_frequencyTwist
    (realInterpolatedLog W) (realInterpolatedLog_smooth W hW)
    (|Real.log a|+|Real.log b|) (by positivity) (realInterpolatedLog_support W a b ha hs)
    (Icc (0:ℝ) 1 ×ˢ ({0}:Set ℝ)) (isCompact_Icc.prod isCompact_singleton)
    (realInterpolatedLogSchwartz W a b ha hs hW) (realInterpolatedLogSchwartz_apply W a b ha hs hW) T
  refine ⟨n,A*B,mul_pos hA hB,?_⟩
  intro σ hσ t
  have hp : (σ,0)∈Icc (0:ℝ) 1 ×ˢ ({0}:Set ℝ) := ⟨hσ,rfl⟩
  have hheight : ‖t/(2*Real.pi)‖≤‖t‖ := by
    rw [norm_div,Real.norm_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])
  have hh := hcontrol (frequencyTwist (realInterpolatedLogSchwartz W a b ha hs hW (σ,0)) (t/(2*Real.pi)))
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (interpolatedProfile W a b ha hs hW σ t)≤_ at hh
  apply hh.trans
  have hb : T.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (realInterpolatedLogSchwartz W a b ha hs hW (σ,0)) (t/(2*Real.pi)))≤B*(1+‖t‖)^n :=
    (hbound (σ,0) hp (t/(2*Real.pi))).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) n) hB.le)
  exact (mul_le_mul_of_nonneg_left hb hA.le).trans_eq (by ring)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
