import OAI.Analysis.CircleDomains.Probability.MeasureFamilyDominatedLimit
import OAI.Analysis.CircleDomains.Probability.CompactMeasureDensity

namespace OAI

/-! The L² limit representative may have arbitrary values on a reference
null set. Taking its positive part preserves all limiting admissibility. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma measureFamilyModulus_le_of_signed_L2_limit
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (f : ℕ → Z → ℝ) (g : Z → ℝ)
    (hf : ∀ n, Measurable (f n)) (hf0 : ∀ n z, 0 ≤ f n z)
    (hfL : ∀ n, MemLp (f n) 2 σ) (hg : Measurable g) (hgL : MemLp g 2 σ)
    (hlim : Tendsto (fun n => eLpNorm (fun z => f n z-g z) 2 σ) atTop (𝓝 0))
    (ha : ∀ a, ∀ᶠ n in atTop, 1 ≤ ∫⁻ z, ENNReal.ofReal (f n z) ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤ ENNReal.ofReal (‖hgL.toLp g‖^2) := by
  obtain ⟨ρ,P,hρ,hP,hP0,hPL,hpoint⟩ := exists_L2_dominated_ae_subsequence hfL hgL hlim
  have hp : ∀ᵐ z ∂σ, (∀ n, |f (ρ n) z| ≤ P z) ∧
      Tendsto (fun n => f (ρ n) z) atTop (𝓝 (max (g z) 0)) := by
    filter_upwards [hpoint] with z hz
    refine ⟨hz.1,?_⟩
    have h := hz.2.max (tendsto_const_nhds (x := (0 : ℝ)))
    convert h using 1
    funext n
    exact (max_eq_left (hf0 (ρ n) z)).symm
  have hmod := measureFamilyModulus_le_of_dominated_limit σ K
    (fun n => f (ρ n)) (fun z => max (g z) 0) P
    (fun n => hf (ρ n)) (fun n => hf0 (ρ n)) (hg.max measurable_const)
    (fun z => le_max_right _ _) hP hP0 hPL hp (fun a => hρ.eventually (ha a))
  refine hmod.trans ?_
  have heq : (∫⁻ z, ENNReal.ofReal (g z^2) ∂σ) = ENNReal.ofReal (‖hgL.toLp g‖^2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hgL.integrable_sq
      (Eventually.of_forall (fun z => sq_nonneg (g z)))]
    congr 1
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hgL.coeFn_toLp] with z hz
    simp only [hz,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  rw [← heq]
  apply lintegral_mono
  intro z
  change ENNReal.ofReal (max (g z) 0)^2 ≤ ENNReal.ofReal (g z^2)
  by_cases hz : 0 ≤ g z
  · rw [max_eq_left hz,ENNReal.ofReal_pow hz]
  · rw [max_eq_right (le_of_not_ge hz)]
    simp only [ENNReal.ofReal_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    exact bot_le

end CircleDomainRigidity

end

end OAI
