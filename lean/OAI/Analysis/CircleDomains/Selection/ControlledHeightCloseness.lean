import OAI.Analysis.CircleDomains.Selection.ControlledHeight

namespace OAI

/-! The height tolerance is uniform over all retained models with one
fixed exterior radius. Only the near-extremality error must shrink. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem controlled_heights_close {R : ℝ}
    {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ d, 0 < d → d < δ → ∀ H : ControlledHeight R d,
      ∀ z ∈ K, |H.height z-z.im| < ε := by
  let I := Σ d : {d : ℝ // 0 < d ∧ d ≤ 1}, ControlledHeight R d.1
  let v : I → C(ℂ, ℝ) := fun i => i.2.height
  have heq : Equicontinuous (fun i z => v i z) := by
    apply heights_equicontinuous_of_log_bound (B := 2*Real.pi) _ (by positivity)
    intro i c r hr hr1 z hz
    have h := i.2.log_bound c r hr hr1 z hz
    have hd : 2*Real.pi*i.1.1 ≤ 2*Real.pi :=
      mul_le_of_le_one_right (by positivity) i.1.2.2
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hb (L : Set ℂ) (hL : IsCompact L) :
      ∃ C : ℝ, ∀ i z, z ∈ L → |v i z| ≤ C := by
    obtain ⟨S, hS⟩ := hL.isBounded.subset_ball 0
    let T := max (2*R) S
    refine ⟨T+R, fun i z hz => i.2.local_bound T (le_max_left _ _) z ?_⟩
    exact ball_subset_closedBall ((ball_subset_ball (le_max_right _ _)) (hS hz))
  obtain ⟨δ, hδ, hc⟩ := uniform_height_closeness v (fun i => i.2.error₀)
    (fun i => i.2.error₁) (fun i => i.2.weak_gradient) heq hb
    (fun i => 2*Real.pi*i.1.1) (fun i => i.2.error_bound)
    (fun i => i.2.exterior_bound) hK hε
  refine ⟨min 1 (δ/(2*Real.pi)), lt_min zero_lt_one (div_pos hδ (by positivity)), ?_⟩
  intro d hd hdδ H z hz
  let i : I := ⟨⟨d, hd, hdδ.le.trans (min_le_left _ _)⟩, H⟩
  apply hc i ?_ z hz
  change 2*Real.pi*d < δ
  have h := (lt_div_iff₀ (by positivity : 0 < 2*Real.pi)).mp
    (hdδ.trans_le (min_le_right _ _))
  nlinarith

end CircleDomainRigidity

end

end OAI
