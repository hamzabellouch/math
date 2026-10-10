import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LipschitzTests
import OAI.Analysis.RieszRectifiability.Kernel.LipschitzL2Density

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Function
open scoped NNReal ContDiff

theorem integrable_mul_compact_test_of_integrableOn {d : ℕ}
    (μ : Measure (Ambient d)) (U : Set (Ambient d))
    (f g : Ambient d → ℝ) (hf : IntegrableOn f U μ)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : support g ⊆ U) :
    Integrable (fun x => f x * g x) μ := by
  obtain ⟨B, hB⟩ := hgc.exists_bound_of_continuous hg
  have hi : IntegrableOn (fun x => f x * g x) U μ :=
    hf.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall hB)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro x hx
  have hz : g x = 0 := by
    by_contra hn
    exact hx (hgs hn)
  rw [hz, mul_zero]

theorem local_mean_zero_test_annihilator_constant {d : ℕ}
    (μ : Measure (Ambient d)) (U : Set (Ambient d)) (hU : IsOpen U)
    [IsFiniteMeasure (μ.restrict U)]
    (f : Ambient d → ℝ) (hf : IntegrableOn f U μ)
    (η : Ambient d → ℝ) (Kη : ℝ≥0) (hη : LipschitzWith Kη η)
    (hηc : HasCompactSupport η) (hηs : support η ⊆ U) (hηmean : (∫ x, η x ∂μ) = 1)
    (hzero : ∀ (φ : Ambient d → ℝ) (K : ℝ≥0), LipschitzWith K φ →
      HasCompactSupport φ → support φ ⊆ U → (∫ x, φ x ∂μ) = 0 →
        (∫ x, f x * φ x ∂μ) = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂μ, x ∈ U → f x = c := by
  have hηI : Integrable η μ := by
    simpa only [one_mul] using! integrable_mul_compact_test_of_integrableOn μ U
      (fun _ => 1) η (integrable_const 1) hη.continuous hηc hηs
  have hfη := integrable_mul_compact_test_of_integrableOn μ U f η hf hη.continuous hηc hηs
  let c := ∫ x, f x * η x ∂μ
  refine ⟨c, ?_⟩
  have hfc : LocallyIntegrableOn (fun x => f x - c) U μ :=
    (hf.sub (integrable_const c)).locallyIntegrableOn
  have ha := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfc ?_
  · filter_upwards [ha] with x hx hxU
    exact sub_eq_zero.mp (hx hxU)
  intro g hgsmooth hgc hgs
  have hgsU : support g ⊆ U := subset_trans (subset_tsupport g) hgs
  have hgI : Integrable g μ := by
    simpa only [one_mul] using! integrable_mul_compact_test_of_integrableOn μ U
      (fun _ => 1) g (integrable_const 1) hgsmooth.continuous hgc hgsU
  have hfg := integrable_mul_compact_test_of_integrableOn μ U f g hf hgsmooth.continuous hgc hgsU
  obtain ⟨Kg, hKg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hgsmooth (by simp)
  let M := ∫ x, g x ∂μ
  let φ := fun x => g x - M * η x
  have hφ : LipschitzWith (Kg + ‖M‖₊ * Kη) φ := hKg.sub (lipschitz_const_mul_real hη M)
  have hφc : HasCompactSupport φ := hgc.sub hηc.mul_left
  have hφs : support φ ⊆ U := by
    intro x hx
    by_contra hn
    have hg0 : g x = 0 := by
      by_contra hz
      exact hn (hgsU hz)
    have hη0 : η x = 0 := by
      by_contra hz
      exact hn (hηs hz)
    exact hx (by simp only [φ, hg0, hη0, mul_zero, sub_zero])
  have hφmean : (∫ x, φ x ∂μ) = 0 := by
    change (∫ x, g x - M * η x ∂μ) = 0
    rw [integral_sub hgI (hηI.const_mul M), integral_const_mul, hηmean, mul_one]
    exact sub_self _
  have hz := hzero φ _ hφ hφc hφs hφmean
  have heq : (fun x => f x * φ x) = fun x => f x * g x - M * (f x * η x) := by
    funext x
    dsimp only [φ]
    ring
  rw [heq, integral_sub hfg (hfη.const_mul M), integral_const_mul] at hz
  have hfgmean : (∫ x, f x * g x ∂μ) = M * c := sub_eq_zero.mp hz
  change (∫ x, g x * (f x - c) ∂μ) = 0
  calc
    _ = ∫ x, f x * g x - c * g x ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = (∫ x, f x * g x ∂μ) - c * ∫ x, g x ∂μ := by
      rw [integral_sub hfg (hgI.const_mul c), integral_const_mul]
    _ = 0 := by rw [hfgmean]; dsimp only [M]; ring

end

end RieszRectifiability

end OAI
