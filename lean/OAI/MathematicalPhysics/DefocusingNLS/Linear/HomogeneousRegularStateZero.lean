import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularPhysical

namespace OAI

/-! Vanishing values on a small sphere determine the entire regular state. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem homogeneousRegular_state_zero_radius (νp νm : ℂ) (m : ℕ)
    (Q : ℝ → ℂ) (hQ : Continuous Q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (eta R t : ℝ), 0 ≤ eta → 0 < t → t < R → t ≤ δ →
      ∀ U : ℝ → E₄,
      ContDiff ℝ 2 (fun r => (U r).1.1) → ContDiff ℝ 2 (fun r => (U r).2.1) →
      (∀ r ∈ Ioc 0 R, HasDerivAt U
        (spectralPhysicalCircularField νp νm (eta : ℂ) m (Q r) r (U r)) r) →
      (U t).1.1 = 0 → (U t).2.1 = 0 → U R = 0 := by
  obtain ⟨δ, hδ, _, huniq⟩ := homogeneousRegular_physical_small_ball νp νm m Q hQ
  refine ⟨δ, hδ, ?_⟩
  intro eta R t heta ht htR htδ U hF hG hU hFt hGt
  let F := fun r => (U r).1.1
  let G := fun r => (U r).2.1
  have hzero : ∀ r ∈ Icc 0 t, F r = 0 ∧ G r = 0 := by
    apply huniq t eta ht htδ heta F G hF hG hFt hGt
    · intro r hr hrt
      exact (homogeneousRegular_state_equation νp νm eta m Q U R hU r
        ⟨hr, hrt.trans_lt htR⟩).1
    · intro r hr hrt
      exact (homogeneousRegular_state_equation νp νm eta m Q U R hU r
        ⟨hr, hrt.trans_lt htR⟩).2
  let s := t / 2
  have hs : 0 < s := by dsimp only [s]; positivity
  have hst : s < t := by dsimp only [s]; linarith
  have heF : F =ᶠ[nhds s] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds hs hst] with r hr
    exact (hzero r ⟨hr.1.le, hr.2.le⟩).1
  have heG : G =ᶠ[nhds s] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds hs hst] with r hr
    exact (hzero r ⟨hr.1.le, hr.2.le⟩).2
  have hv := homogeneousRegular_state_velocity νp νm (eta : ℂ) m Q U s
    (hU s ⟨hs, hst.le.trans htR.le⟩)
  have hus : U s = 0 := by
    apply Prod.ext <;> apply Prod.ext
    · exact heF.eq_of_nhds
    · rw [← hv.1]
      exact heF.deriv_eq.trans (deriv_const s 0)
    · exact heG.eq_of_nhds
    · rw [← hv.2]
      exact heG.deriv_eq.trans (deriv_const s 0)
  obtain ⟨C, hC⟩ := spectralPhysicalCircularField_bounded_on νp νm (eta : ℂ) m Q s R hs
    hQ.continuousOn
  exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (fun r hr => (hU r ⟨hs.trans_le hr.1, hr.2⟩).continuousAt.continuousWithinAt)
    (fun r hr => (hU r ⟨hs.trans_le hr.1, hr.2.le⟩).hasDerivWithinAt) hus
    (fun r hr => hC r ⟨hr.1, hr.2.le⟩ (U r)) R ⟨hst.le.trans htR.le, le_rfl⟩

end DefocusingNLS

end OAI
