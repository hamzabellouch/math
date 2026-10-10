import Mathlib
import OAI.Geometry.HypersurfaceGerms.Germs
import OAI.Geometry.HypersurfaceGerms.Parameters

namespace OAI

/-! The common analytic construction of germs of multiplicities four and five. -/

namespace AmbientMultiplicity
noncomputable section
 

theorem common_source_construction (r : ℕ) (hr : 4 ≤ r) :
    ∃ n₀ : ℕ, Parameters.CommonConditions r n₀ ∧ Parameters.IndexConditions r n₀ ∧
      ∀ s : ℝ, 0 < s →
      let a := Parameters.exponent n₀
      let b := Parameters.exponent (Parameters.nextN r n₀)
      AnalyticAt ℂ (Preparation.f4 (s:ℂ) a b) 0 ∧
      AnalyticAt ℂ (Preparation.f5 (s:ℂ) a b) 0 ∧
      Preparation.f4 (s:ℂ) a b 0 = 0 ∧ Preparation.f5 (s:ℂ) a b 0 = 0 ∧
      ReducedAtZero (Preparation.f4 (s:ℂ) a b) ∧
      ReducedAtZero (Preparation.f5 (s:ℂ) a b) ∧
      IsolatedCriticalAtZero (Preparation.f4 (s:ℂ) a b) ∧
      IsolatedCriticalAtZero (Preparation.f5 (s:ℂ) a b) ∧
      HasOrderAtZero (Preparation.f4 (s:ℂ) a b) 4 ∧
      HasOrderAtZero (Preparation.f5 (s:ℂ) a b) 5 := by
  obtain ⟨n₀,hc⟩ := Parameters.choice_exists r
  have hh := Parameters.choice_common r n₀ hr hc
  have hi := Parameters.parameter_indices_reference r n₀ hr hc
  refine ⟨n₀,hh,hi,?_⟩
  intro s hs
  rcases hh with ⟨_,_,_,_,_,_,_,_,ha,hab,_⟩
  exact exact_source_germs (s:ℂ) (by exact_mod_cast (ne_of_gt hs)) _ _ ha (by omega)

end

 

theorem analytic_part_only :
    ∃ f4 f5 : C4 → ℂ,
      AnalyticAt ℂ f4 0 ∧ AnalyticAt ℂ f5 0 ∧
      f4 0 = 0 ∧ f5 0 = 0 ∧
      ReducedAtZero f4 ∧ ReducedAtZero f5 ∧
      IsolatedCriticalAtZero f4 ∧ IsolatedCriticalAtZero f5 ∧
      HasOrderAtZero f4 4 ∧ HasOrderAtZero f5 5 := by
  obtain ⟨n₀, _, _, hg⟩ := common_source_construction 4 (by norm_num)
  refine ⟨Preparation.f4 (1 : ℂ) (Parameters.exponent n₀)
      (Parameters.exponent (Parameters.nextN 4 n₀)),
    Preparation.f5 (1 : ℂ) (Parameters.exponent n₀)
      (Parameters.exponent (Parameters.nextN 4 n₀)), ?_⟩
  simpa using hg 1 (by norm_num)

end AmbientMultiplicity

end OAI
