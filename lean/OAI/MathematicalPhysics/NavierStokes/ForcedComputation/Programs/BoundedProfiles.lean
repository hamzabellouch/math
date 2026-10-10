import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LogarithmicSpatialForce
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ForceEvaluation

namespace OAI

/-! The logarithmic estimate applies to an initialized field as soon as all
its original derivatives are bounded. Periodicity in time is unnecessary. -/

noncomputable section
open scoped ContDiff BigOperators
open ShearFlows

namespace ForcedComputation

theorem boundedMixed_derivative {V : Velocity} (hb : BoundedMixedDerivatives V)
    (β : List (Fin 4)) : BoundedMixedDerivatives (mixedDerivative V β) := by
  intro α
  simpa only [mixedDerivative_append] using hb (α ++ β)

theorem boundedMixed_sub {V W : Velocity} (hV : ContDiff ℝ ∞ V)
    (hW : ContDiff ℝ ∞ W) (hVB : BoundedMixedDerivatives V)
    (hWB : BoundedMixedDerivatives W) : BoundedMixedDerivatives (V - W) := by
  intro α
  obtain ⟨A, hA, hbA⟩ := hVB α
  obtain ⟨B, hB, hbB⟩ := hWB α
  refine ⟨A + B, add_nonneg hA hB, fun y => ?_⟩
  rw [mixedDerivative_sub hV hW]
  exact (norm_sub_le _ _).trans (add_le_add (hbA y) (hbB y))

theorem boundedMixed_sum {ι : Type*} [Fintype ι] (V : ι → Velocity)
    (hs : ∀ i, ContDiff ℝ ∞ (V i)) (hb : ∀ i, BoundedMixedDerivatives (V i)) :
    BoundedMixedDerivatives (∑ i, V i) := by
  intro α
  choose C hC hbC using fun i => hb i α
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun y => ?_⟩
  rw [mixedDerivative_sum V hs]
  simpa only [Finset.sum_apply] using
    (norm_sum_le (s := Finset.univ) (f := fun i => mixedDerivative (V i) α y)).trans
      (Finset.sum_le_sum fun i _ => hbC i y)

theorem bounded_uniformTimeBounds {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hb : BoundedMixedDerivatives V) : UniformTimeBounds (fun x s => V (s, x)) := by
  intro n
  obtain ⟨C, hC, hbound⟩ := hb (List.replicate n 0)
  exact ⟨C, hC, fun x t => by rw [iteratedDeriv_eq_mixedTime hV]; exact hbound (t, x)⟩

theorem bounded_spatialPhase {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hb : BoundedMixedDerivatives V) (α : List (Fin 3)) :
    BoundedMixedDerivatives (spatialPhase V α) := by
  rw [spatialPhase_eq_mixed hV]
  exact boundedMixed_derivative hb _

theorem bounded_quadraticPhase {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hb : BoundedMixedDerivatives V) (ha : ZeroAdvection V) :
    BoundedMixedDerivatives (fun y : SpaceTime => quadraticPhase V y.2 y.1) := by
  have he : (fun y : SpaceTime => quadraticPhase V y.2 y.1) = mixedDerivative V [0] - V := by
    funext y
    simp only [quadraticPhase, ha y.1 y.2, add_zero, timeDerivative_eq hV]
    rfl
  rw [he]
  exact boundedMixed_sub (mixedDerivative_smooth hV _) hV (boundedMixed_derivative hb _) hb

theorem bounded_viscousPhase {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hb : BoundedMixedDerivatives V) :
    BoundedMixedDerivatives (fun y : SpaceTime => viscousPhase V y.2 y.1) := by
  have he : (fun y : SpaceTime => viscousPhase V y.2 y.1) =
      ∑ j : Fin 3, mixedDerivative V [j.succ,j.succ] := by
    funext y
    simpa only [viscousPhase, Finset.sum_apply] using laplacian_eq_mixed hV y.1 y.2
  rw [he]
  exact boundedMixed_sum _ (fun _ => mixedDerivative_smooth hV _)
    (fun _ => boundedMixed_derivative hb _)

theorem bounded_profile_mixed_decay {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hb : BoundedMixedDerivatives V) (r n : ℕ) (α : List (Fin 3)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, 0 ≤ t →
      ‖iteratedDeriv n
        (fun s => spatialWord α (fun y => logarithmicProfile r (fun q => V (q, y)) s) x) t‖ ≤
        C * (1 + t)⁻¹ ^ (r + n) := by
  have hphase (x : Space) : ContDiff ℝ ∞ (fun s => spatialPhase V α (s, x)) :=
    (spatialPhase_smooth hV α).comp (contDiff_id.prodMk contDiff_const)
  obtain ⟨C, hC, hbound⟩ := logarithmicProfile_uniform_decay r n hphase
    (bounded_uniformTimeBounds (spatialPhase_smooth hV α) (bounded_spatialPhase hV hb α))
  refine ⟨C, hC, fun x t ht => ?_⟩
  have he : (fun s => spatialWord α (fun y => logarithmicProfile r (fun q => V (q, y)) s) x) =
      logarithmicProfile r (fun s => spatialPhase V α (s, x)) :=
    funext (fun s => spatialWord_logarithmicProfile r V α s x)
  rw [he]
  exact hbound x t ht

theorem bounded_slowForce_spatial_time_decay (ν : ℝ) {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hb : BoundedMixedDerivatives V) (ha : ZeroAdvection V)
    (α : List (Fin 3)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, 0 ≤ t →
      ‖iteratedDeriv n (fun s => spatialWord α (fun y => slowForce ν V (s, y)) x) t‖ ≤
        C * (1 + t)⁻¹ ^ (1 + n) := by
  let Q : Velocity := fun y => quadraticPhase V y.2 y.1
  let D : Velocity := fun y => viscousPhase V y.2 y.1
  have hQ : ContDiff ℝ ∞ Q := quadraticPhase_smooth hV
  have hD : ContDiff ℝ ∞ D := viscousPhase_smooth hV
  obtain ⟨A, hA, hQA⟩ := bounded_profile_mixed_decay hQ (bounded_quadraticPhase hV hb ha) 2 n α
  obtain ⟨B, hB, hDB⟩ := bounded_profile_mixed_decay hD (bounded_viscousPhase hV hb) 1 n α
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
