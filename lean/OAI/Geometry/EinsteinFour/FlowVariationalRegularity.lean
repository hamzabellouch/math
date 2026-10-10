import OAI.Geometry.EinsteinFour.FlowVariationalExistence

namespace OAI

/-! The variational lift loses exactly one finite derivative. -/

namespace PositiveEinsteinFour.FlowCalculus

open scoped ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem variationalField_contDiffAt_order (n : ℕ) (f : E → E)
    (q : VariationSpace E) (hf : ContDiffAt ℝ (n + 1 : ℕ) f q.1) :
    ContDiffAt ℝ n (variationalField f) q := by
  have hD : ContDiffAt ℝ n (fderiv ℝ f) q.1 := hf.fderiv_right (by simp)
  exact ((hf.of_le (by exact_mod_cast Nat.le_succ n)).comp q contDiffAt_fst).prodMk
    ((hD.comp q contDiffAt_fst).clm_comp contDiffAt_snd)

end
end PositiveEinsteinFour.FlowCalculus

end OAI
