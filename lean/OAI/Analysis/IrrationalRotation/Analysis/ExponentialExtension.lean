import OAI.Analysis.IrrationalRotation.Model.ExponentialWeight
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Piecewise

namespace OAI

open Filter Set Topology

namespace Invariant233

variable {X : Type*} {x₀ x : X} {g : X → ℝ}

@[simp] theorem exponentialWeight_self (x₀ : X) (g : X → ℝ) :
    exponentialWeight x₀ g x₀ = 0 := by
  classical
  simp [exponentialWeight]

theorem exponentialWeight_of_ne (h : x ≠ x₀) :
    exponentialWeight x₀ g x = Real.exp (-g x) := by
  classical
  simp [exponentialWeight, h]

@[simp] theorem exponentialWeight_eq_zero_iff :
    exponentialWeight x₀ g x = 0 ↔ x = x₀ := by
  by_cases h : x = x₀
  · subst x
    simp
  · rw [exponentialWeight_of_ne h]
    simp [Real.exp_ne_zero, h]

theorem exponentialWeight_pos (h : x ≠ x₀) :
    0 < exponentialWeight x₀ g x := by
  rw [exponentialWeight_of_ne h]
  exact Real.exp_pos _

theorem exponentialWeight_nonneg (x₀ : X) (g : X → ℝ) (x : X) :
    0 ≤ exponentialWeight x₀ g x := by
  by_cases h : x = x₀
  · subst x
    simp
  · exact (exponentialWeight_pos h).le

theorem exponentialWeight_le_one (hg : ∀ x ≠ x₀, 0 ≤ g x) (x : X) :
    exponentialWeight x₀ g x ≤ 1 := by
  by_cases h : x = x₀
  · subst x
    simp
  · rw [exponentialWeight_of_ne h, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (hg x h)

theorem exponentialWeight_mem_Icc (hg : ∀ x ≠ x₀, 0 ≤ g x) (x : X) :
    exponentialWeight x₀ g x ∈ Icc (0 : ℝ) 1 :=
  ⟨exponentialWeight_nonneg _ _ _, exponentialWeight_le_one hg x⟩

theorem exponentialWeight_zero_set (x₀ : X) (g : X → ℝ) :
    (exponentialWeight x₀ g) ⁻¹' {0} = {x₀} := by
  ext x
  simp

theorem log_exponentialWeight_of_ne (h : x ≠ x₀) :
    Real.log (exponentialWeight x₀ g x) = -g x := by
  rw [exponentialWeight_of_ne h, Real.log_exp]


variable [TopologicalSpace X] [T1Space X]

theorem continuous_exponentialWeight
    (hg : ContinuousOn g {x₀}ᶜ)
    (hlim : Tendsto g (𝓝[≠] x₀) atTop) :
    Continuous (exponentialWeight x₀ g) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  by_cases h : x = x₀
  · subst x
    rw [exponentialWeight, continuousAt_update_same]
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlim)
  · rw [exponentialWeight, continuousAt_update_of_ne h]
    exact Real.continuous_exp.continuousAt.comp
      (hg.continuousAt (isOpen_compl_singleton.mem_nhds h)).neg

omit [T1Space X] in
theorem continuous_truncatedLog {f : X → ℝ} (hf : Continuous f) (M : ℝ) :
    Continuous (fun x => Real.log (max (f x) (Real.exp (-M)))) := by
  apply Continuous.log (hf.max continuous_const)
  intro x
  exact ne_of_gt (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _))


end Invariant233

end OAI
