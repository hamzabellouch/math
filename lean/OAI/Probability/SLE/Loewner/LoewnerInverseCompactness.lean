import OAI.Probability.SLE.Loewner.LoewnerInverseStability
import OAI.Probability.SLE.Geometry.HolomorphicFamilyCompactness

namespace OAI

/-! Compactness of inverse maps at a fixed capacity time follows directly
from their reverse-flow displacement estimate. -/
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

lemma inverse_family_compact_bounds
    (U : ℕ → ℝ≥0 → ℝ) (γ : ℕ → ℝ≥0 → ℂ) (G F : ℕ → ℝ≥0 → ℂ → ℂ)
    (h : ∀ n, IsCapacityTwoWitness (U n) (γ n) (G n) (F n)) (T : ℝ≥0)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane) :
    ∃ C : ℝ, ∀ n z, z ∈ K → ‖F n T z‖ ≤ C := by
  by_cases hne : K.Nonempty
  · obtain ⟨w,hw,hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
    have ha : 0 < w.im := hKH hw
    obtain ⟨R,_,hR⟩ := hK.isBounded.exists_pos_norm_lt
    refine ⟨R+(2*w.im⁻¹)*T, fun n z hz => ?_⟩
    have hb := (h n).inverse_displacement_bound T ha z (hmin hz)
    have ht := norm_le_norm_sub_add (F n T z) z
    rw [← dist_eq_norm] at ht
    exact le_trans ht (add_le_add hb (hR z hz).le) |>.trans_eq (add_comm _ _)
  · exact ⟨0,fun _ z hz => (hne ⟨z,hz⟩).elim⟩

theorem inverse_family_subsequence
    (U : ℕ → ℝ≥0 → ℝ) (γ : ℕ → ℝ≥0 → ℂ) (G F : ℕ → ℝ≥0 → ℂ → ℂ)
    (h : ∀ n, IsCapacityTwoWitness (U n) (γ n) (G n) (F n)) (T : ℝ≥0) :
    ∃ (σ : ℕ → ℕ) (f : ℂ → ℂ), StrictMono σ ∧
      DifferentiableOn ℂ f upperHalfPlane ∧
      TendstoLocallyUniformlyOn (fun n => F (σ n) T) f atTop upperHalfPlane := by
  classical
  obtain ⟨g,σ,hσ,hconv⟩ := holomorphic_halfPlane_family_subsequence
    (fun n => F n T) (fun n => (h n).2.2.2.2.1 T)
    (inverse_family_compact_bounds U γ G F h T)
  let f : ℂ → ℂ := fun w => if hw : w ∈ upperHalfPlane then g ⟨w,hw⟩ else 0
  have hf : TendstoLocallyUniformlyOn (fun n => F (σ n) T) f atTop upperHalfPlane := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro K hK
    have hh := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv K hK
    change TendstoUniformlyOn (fun n (w : upperHalfPlane) => F (σ n) T w)
      (fun w : upperHalfPlane => f w) atTop K
    have he : (fun w : upperHalfPlane => f w) = (g : upperHalfPlane → ℂ) := by
      funext w
      exact dite_eq_left w.property
    rwa [he]
  exact ⟨σ,f,hσ,hf.differentiableOn
    (Eventually.of_forall fun n => (h (σ n)).2.2.2.2.1 T) isOpen_upperHalfPlane,hf⟩

end SLEExactGauge

end

end OAI
