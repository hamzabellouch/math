import Mathlib
import OAI.Probability.SKSupport.Regularity.Regularity
import OAI.Probability.SKSupport.Control.FiniteContinuity
import OAI.Probability.SKSupport.Regularity.FamilyDifferentiation

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform
variable {Ω : Type*} [MeasurableSpace Ω]

lemma approxValue_continuousOn (γ : OrderParameter) (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => approxValue γ n p.1 p.2) (Icc (0:ℝ) 1 ×ˢ Set.univ) := by
  simpa only [approxValue,approxMesh_horizon] using finiteValue_continuousOn
    (regularDatum_softAbs (show ((n+1:ℕ):ℝ) ≠ 0 by positivity))
    (softAbs_lipschitz (show ((n+1:ℕ):ℝ) ≠ 0 by positivity)) (approxCoeff γ n) (approxMesh n) (n+1) 0

lemma value_continuousOn (W : BrownianSystem Ω) (γ : OrderParameter) :
    ContinuousOn (fun p : ℝ × ℝ => value W γ p.1 p.2) (Icc (0:ℝ) 1 ×ˢ Set.univ) :=
  (approxValue_uniform W γ).continuousOn (Filter.Eventually.of_forall (approxValue_continuousOn γ)).frequently

lemma approxValue_derivative_uniform (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    TendstoUniformlyOn (fun n (p : ℝ × ℝ) => iteratedDeriv m (approxValue γ n p.1) p.2)
      (fun p => iteratedDeriv m (value W γ p.1) p.2) atTop (Icc (0:ℝ) T ×ˢ Set.univ) := by
  induction m with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact (approxValue_uniform W γ).mono (Set.prod_mono (Icc_subset_Icc le_rfl hT1.le) (Subset.refl _))
  | succ m ih =>
    obtain ⟨C,hC,hb⟩ := approxValue_uniform_derivative_bounds γ hT0 hT1 (m+1)
    have hbg : ∀ t ∈ Icc (0:ℝ) T, ∀ x, |iteratedDeriv (m+2) (value W γ t) x| ≤ C := by
      intro t ht x
      exact iteratedDeriv_limit_bound (m+2)
        (approxValue_derivative_uniform_spatial W γ ht.1 (ht.2.trans_lt hT1) (m+2))
        (fun n y => by simpa only [Nat.add_assoc] using hb n t ht y) x
    have hh := tendstoUniformlyOn_deriv_family (S := Icc (0:ℝ) T)
      (f := fun n t => iteratedDeriv m (approxValue γ n t))
      (g := fun t => iteratedDeriv m (value W γ t))
      (fun n t _ => (contDiff_iteratedDeriv_infty (approxValue_regular γ n t).smooth m).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (fun t ht => (contDiff_iteratedDeriv_infty (value_contDiff W γ ht.1 (ht.2.trans_lt hT1)) m).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hC
      (by simpa only [show m+2=(m+1)+1 by omega,iteratedDeriv_succ] using hb)
      (by simpa only [show m+2=(m+1)+1 by omega,iteratedDeriv_succ] using hbg) ih
    simpa only [iteratedDeriv_succ] using hh

theorem value_derivative_continuousOn (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv m (value W γ p.1) p.2)
      (Icc (0:ℝ) T ×ˢ Set.univ) := by
  induction m with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact (value_continuousOn W γ).mono
      (Set.prod_mono (Icc_subset_Icc le_rfl hT1.le) (Subset.refl _))
  | succ m ih =>
    obtain ⟨C,hC,hb⟩ := value_uniform_derivative_bounds W γ hT0 hT1 (m+1)
    have hh := continuousOn_deriv_family (S := Icc (0:ℝ) T)
      (f := fun t => iteratedDeriv m (value W γ t)) ih
      (fun t ht => (contDiff_iteratedDeriv_infty (value_contDiff W γ ht.1 (ht.2.trans_lt hT1)) m).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hC
      (by simpa only [show m+2=(m+1)+1 by omega,iteratedDeriv_succ] using hb)
    simpa only [iteratedDeriv_succ] using hh

end ZeroTemperatureSK

end
end

end OAI
