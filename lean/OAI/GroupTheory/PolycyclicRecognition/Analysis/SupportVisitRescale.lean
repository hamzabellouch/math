import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportVisitImage

namespace OAI

/-! # Exact amplitude reparametrization of a support visit -/

noncomputable section

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]

/-- Rescaling the root subgroup parameter preserves every point of the
outward-switch-return path, including its parametrization. -/
theorem supportVisitPath_comp_mul
    (d : ℝ → G) (hd : Continuous d) (hd₀ : d 0 = 1)
    (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1)
    (n d₀ : G) (r b a : ℝ) (t : unitInterval) :
    supportVisitPath d hd hd₀ (fun u => f (u * a))
      (hf.comp (continuous_id.mul_const a)) (by simpa using hf₀) n d₀ r b t =
    supportVisitPath d hd hd₀ f hf hf₀ n d₀ r (b * a) t := by
  simp only [supportVisitPath, Path.trans_apply, Path.symm_apply, flowPath, flowLeg,
    Function.comp_apply]
  split_ifs <;> simp only [mul_assoc]

/-- The exact reparametrization transports the coarse metric estimate. -/
theorem supportVisitPath_comp_mul_metric
    (d : ℝ → G) (hd : Continuous d) (hd₀ : d 0 = 1)
    (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1)
    (n d₀ : G) (r b a L κ : ℝ)
    (h : PathMetricBound (supportVisitPath d hd hd₀ f hf hf₀ n d₀ r (b * a)) L κ) :
    PathMetricBound (supportVisitPath d hd hd₀ (fun u => f (u * a))
      (hf.comp (continuous_id.mul_const a)) (by simpa using hf₀) n d₀ r b) L κ := by
  intro s t
  rw [supportVisitPath_comp_mul, supportVisitPath_comp_mul]
  exact h s t

end PolycyclicRecognition

end

end OAI
