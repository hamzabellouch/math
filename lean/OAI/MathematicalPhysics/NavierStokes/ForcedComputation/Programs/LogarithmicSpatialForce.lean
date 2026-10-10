import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LogarithmicSpace

namespace OAI

/-! Every spatial derivative of the slow force has the same integrable time
decay. The phase fields are the actual acceleration and Laplacian of the
original periodic velocity. -/

noncomputable section
open scoped ContDiff
open ShearFlows

namespace ForcedComputation

theorem spatialWord_smooth {U : Space → Space} (hU : ContDiff ℝ ∞ U)
    (α : List (Fin 3)) : ContDiff ℝ ∞ (spatialWord α U) := by
  induction α with
  | nil => exact hU
  | cons j α ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem spatialWord_sub {U V : Space → Space} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) (α : List (Fin 3)) :
    spatialWord α (fun x => U x - V x) = fun x => spatialWord α U x - spatialWord α V x := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    simp only [spatialWord, ih]
    funext x
    unfold derivative
    change (fderiv ℝ (spatialWord α U - spatialWord α V) x) (basis j) = _
    rw [fderiv_sub ((spatialWord_smooth hU α).differentiable (by simp) x)
      ((spatialWord_smooth hV α).differentiable (by simp) x)]
    rfl

theorem spatialWord_slowForce {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (ν : ℝ) (α : List (Fin 3)) (t : ℝ) (x : Space) :
    spatialWord α (fun y => slowForce ν V (t, y)) x =
      logarithmicProfile 2
        (fun s => spatialPhase (fun y => quadraticPhase V y.2 y.1) α (s, x)) t -
      ν • logarithmicProfile 1
        (fun s => spatialPhase (fun y => viscousPhase V y.2 y.1) α (s, x)) t := by
  have hQ : ContDiff ℝ ∞ (fun y : Space => quadraticPhase V y (Real.log (1 + t))) :=
    (quadraticPhase_smooth hV).comp (contDiff_const.prodMk contDiff_id)
  have hD : ContDiff ℝ ∞ (fun y : Space => viscousPhase V y (Real.log (1 + t))) :=
    (viscousPhase_smooth hV).comp (contDiff_const.prodMk contDiff_id)
  change spatialWord α (fun y =>
      logarithmicProfile 2 (quadraticPhase V y) t -
        ν • logarithmicProfile 1 (viscousPhase V y) t) x = _
  have hPQ : ContDiff ℝ ∞ (fun y => logarithmicProfile 2 (quadraticPhase V y) t) :=
    hQ.const_smul ((1 + t)⁻¹ ^ 2)
  have hPD : ContDiff ℝ ∞ (fun y => ν • logarithmicProfile 1 (viscousPhase V y) t) :=
    (hD.const_smul ((1 + t)⁻¹ ^ 1)).const_smul ν
  rw [spatialWord_sub hPQ hPD, spatialWord_smul]
  exact congrArg₂ (fun a b : Space => a - ν • b)
    (spatialWord_logarithmicProfile 2 (fun y => quadraticPhase V y.2 y.1) α t x)
    (spatialWord_logarithmicProfile 1 (fun y => viscousPhase V y.2 y.1) α t x)

theorem periodic_slowForce_spatial_time_decay {L : ℝ} (hL : 0 < L)
    (ν : ℝ) {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hs : SpatiallyPeriodic L V) (ht : TimePeriodic V)
    (α : List (Fin 3)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, 0 ≤ t →
      ‖iteratedDeriv n (fun s => spatialWord α (fun y => slowForce ν V (s, y)) x) t‖ ≤
        C * (1 + t)⁻¹ ^ (1 + n) := by
  let Q : Velocity := fun y => quadraticPhase V y.2 y.1
  let D : Velocity := fun y => viscousPhase V y.2 y.1
  have hQ : ContDiff ℝ ∞ Q := quadraticPhase_smooth hV
  have hD : ContDiff ℝ ∞ D := viscousPhase_smooth hV
  obtain ⟨A, hA, hQA⟩ := periodic_profile_mixed_decay hL hQ
    (quadraticPhase_spatially_periodic hV hs) (quadraticPhase_time_periodic hV ht) 2 n α
  obtain ⟨B, hB, hDB⟩ := periodic_profile_mixed_decay hL hD
    (viscousPhase_spatially_periodic hV hs) (viscousPhase_time_periodic hV ht) 1 n α
  refine ⟨A + ‖ν‖ * B, by positivity, fun x t ht0 => ?_⟩
  have hQx : ContDiff ℝ ∞ (fun s => spatialPhase Q α (s, x)) :=
    (spatialPhase_smooth hQ α).comp (contDiff_id.prodMk contDiff_const)
  have hDx : ContDiff ℝ ∞ (fun s => spatialPhase D α (s, x)) :=
    (spatialPhase_smooth hD α).comp (contDiff_id.prodMk contDiff_const)
  have hqt := logarithmicProfile_contDiffAt 2 hQx (show -1 < t by linarith)
  have hdt := logarithmicProfile_contDiffAt 1 hDx (show -1 < t by linarith)
  have he : (fun s => spatialWord α (fun y => slowForce ν V (s, y)) x) =
      fun s => logarithmicProfile 2 (fun q => spatialPhase Q α (q, x)) s -
        ν • logarithmicProfile 1 (fun q => spatialPhase D α (q, x)) s :=
    funext (fun s => spatialWord_slowForce hV ν α s x)
  rw [he, iteratedDeriv_fun_sub (hqt.of_le (by simp))
    ((hdt.const_smul ν).of_le (by simp)), iteratedDeriv_fun_const_smul_field]
  have hQA' := hQA x t ht0
  have hDB' := hDB x t ht0
  simp_rw [spatialWord_logarithmicProfile] at hQA' hDB'
  have hinv : 0 ≤ (1 + t)⁻¹ := by positivity
  have hinvle : (1 + t)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by linarith : 0 < 1 + t)).mpr (by linarith)
  have hpow : (1 + t)⁻¹ ^ (2 + n) ≤ (1 + t)⁻¹ ^ (1 + n) := by
    calc
      _ = (1 + t)⁻¹ ^ (1 + n) * (1 + t)⁻¹ := by rw [← pow_succ]; congr 1; omega
      _ ≤ (1 + t)⁻¹ ^ (1 + n) * 1 :=
        mul_le_mul_of_nonneg_left hinvle (pow_nonneg hinv _)
      _ = _ := mul_one _
  calc
    _ ≤ ‖iteratedDeriv n (logarithmicProfile 2 (fun q => spatialPhase Q α (q, x))) t‖ +
        ‖ν • iteratedDeriv n (logarithmicProfile 1 (fun q => spatialPhase D α (q, x))) t‖ :=
      norm_sub_le _ _
    _ ≤ A * (1 + t)⁻¹ ^ (2 + n) + ‖ν‖ * (B * (1 + t)⁻¹ ^ (1 + n)) := by
      rw [norm_smul]
      exact add_le_add hQA' (mul_le_mul_of_nonneg_left hDB' (norm_nonneg ν))
    _ ≤ A * (1 + t)⁻¹ ^ (1 + n) + ‖ν‖ * (B * (1 + t)⁻¹ ^ (1 + n)) :=
      add_le_add (mul_le_mul_of_nonneg_left hpow hA) le_rfl
    _ = _ := by ring

end ForcedComputation

end

end OAI
