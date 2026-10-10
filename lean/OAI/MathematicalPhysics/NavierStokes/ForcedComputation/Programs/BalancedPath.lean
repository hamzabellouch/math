import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedVelocity

namespace OAI

/-! The loading trajectory and the compact planar trajectory join with zero
velocity at time one. This identifies the fixed Euclidean particle without
assuming a computational flow or a halting correspondence. -/

noncomputable section
namespace ForcedComputation.BalancedPath
open ShearFlows Recorder.Planar PlanarHamiltonian Set Filter
open scoped ContDiff Topology

def bodyPath (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (Ψ : ℝ → ℝ → Plane → Plane) (t : ℝ) : Space :=
  BalancedStretch.stretch (atHeight (Ψ 0 (t - 1) (BalancedPlanar.inputCode I hI)) 0)

def path (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (Ψ : ℝ → ℝ → Plane → Plane) (t : ℝ) : Space :=
  if t ≤ 1 then BalancedLoader.path (BalancedPlanar.inputCode I hI) t else bodyPath I hI Ψ t

private theorem body_zero_phase (M : Alternating.Machine) (hM : M.WellFormed) (x : Space) :
    BalancedBody.velocity M hM (0,x) = 0 := by
  have hz := (periodicVelocity_zero_near_zero
    (normalizedPulse_valid (BalancedPlanar.referenceInput M) (BalancedPlanar.referenceValid hM))
    (normalizedPulse_inUnit (BalancedPlanar.referenceInput M) (BalancedPlanar.referenceValid hM))).self_of_nhds
  have hv : ∀ z, BalancedPlanar.bodyVelocity M hM 0 z = 0 := hz
  simp only [BalancedBody.velocity, BalancedStretch.velocity, BalancedStretch.push,
    BalancedBody.raw, CompactLift.velocity, CompactLift.spatial,
    VelocityDetector.triangularLift, VelocityDetector.horizontalLinear_eq, hv,
    map_zero, zero_smul, add_zero, smul_zero]

theorem bodyPath_one (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (BalancedPlanar.bodyVelocity I.1 hI.1) Ψ) :
    bodyPath I hI Ψ 1 = BalancedLoader.path (BalancedPlanar.inputCode I hI) 1 := by
  rw [BalancedLoader.path_after _ (by norm_num)]
  simp only [bodyPath, sub_self, hΨ.initial]

theorem bodyPath_deriv (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (BalancedPlanar.bodyVelocity I.1 hI.1) Ψ) (t : ℝ) :
    HasDerivAt (bodyPath I hI Ψ)
      (BalancedBody.velocity I.1 hI.1 (t-1, bodyPath I hI Ψ t)) t := by
  have hp := hΨ.ode 0 (t-1) (BalancedPlanar.inputCode I hI)
  have hl := CompactLift.trajectory_atHeight
    (χ := BalancedBody.verticalCutoff) (a := 0) (z := 0)
    BalancedBody.verticalCutoff_zero hp
  have hs := BalancedStretch.trajectory hl
  have hc := hs.scomp t ((hasDerivAt_id t).sub_const 1)
  apply hasDerivAt_pi.mpr
  intro j
  simpa only [Function.comp_def, one_smul, zero_add, id_eq, bodyPath,
    BalancedBody.velocity, BalancedBody.raw] using (hasDerivAt_pi.mp hc) j

private theorem glue_deriv {f g : ℝ → Space} {v : Space}
    (hf : HasDerivAt f v 1) (hg : HasDerivAt g v 1) (he : f 1 = g 1) :
    HasDerivAt (fun t => if t ≤ 1 then f t else g t) v 1 := by
  have hl : HasDerivWithinAt (fun t => if t ≤ 1 then f t else g t) v (Iic 1) 1 :=
    (hf.hasDerivWithinAt (s := Iic (1 : ℝ))).congr_of_mem
      (fun t ht => ite_eq_left ht)
      (by change (1 : ℝ) ≤ 1; exact le_rfl)
  have hr : HasDerivWithinAt (fun t => if t ≤ 1 then f t else g t) v (Ici 1) 1 := by
    apply (hg.hasDerivWithinAt (s := Ici (1 : ℝ))).congr_of_mem _
      (by change (1 : ℝ) ≤ 1; exact le_rfl)
    intro t ht
    by_cases ht' : t ≤ 1
    · have h : t = 1 := le_antisymm ht' ht
      simpa only [h, ite_eq_left le_rfl] using he
    · exact ite_eq_right ht'
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr

theorem path_deriv (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (BalancedPlanar.bodyVelocity I.1 hI.1) Ψ) (t : ℝ) :
    HasDerivAt (path I hI Ψ) (BalancedVelocity.velocity I hI (t,path I hI Ψ t)) t := by
  have hq : ∀ j, 0 ≤ BalancedPlanar.inputCode I hI j ∧ BalancedPlanar.inputCode I hI j ≤ 1 :=
    fun j => ⟨(BalancedPlanar.inputCode_in_unit I hI j).1.le,
      (BalancedPlanar.inputCode_in_unit I hI j).2.le⟩
  rcases lt_trichotomy t 1 with ht | rfl | ht
  · have he : path I hI Ψ =ᶠ[𝓝 t] BalancedLoader.path (BalancedPlanar.inputCode I hI) := by
      filter_upwards [eventually_lt_nhds ht] with s hs
      exact ite_eq_left hs.le
    rw [he.self_of_nhds, BalancedVelocity.before I hI ht.le]
    exact (BalancedLoader.path_deriv hq t).congr_of_eventuallyEq he
  · have hl := BalancedLoader.path_deriv hq 1
    rw [BalancedLoader.velocity_after _ (by norm_num)] at hl
    have hr := bodyPath_deriv I hI hΨ 1
    rw [sub_self, body_zero_phase] at hr
    have hh := glue_deriv hl hr (bodyPath_one I hI hΨ).symm
    have hz : BalancedVelocity.velocity I hI (1,path I hI Ψ 1) = 0 := by
      rw [BalancedVelocity.before I hI le_rfl, BalancedLoader.velocity_after _ (by norm_num)]
    rw [hz]
    exact hh
  · have he : path I hI Ψ =ᶠ[𝓝 t] bodyPath I hI Ψ := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact ite_eq_right (not_le.mpr hs)
    rw [he.self_of_nhds, BalancedVelocity.tail I hI ht.le]
    have hp := BalancedBody.velocity_periodic I.1 hI.1 (t-1) (bodyPath I hI Ψ t)
    rw [sub_add_cancel] at hp
    rw [hp]
    exact (bodyPath_deriv I hI hΨ t).congr_of_eventuallyEq he

theorem path_initial (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (Ψ : ℝ → ℝ → Plane → Plane) : path I hI Ψ 0 = ![4,0,0] := by
  rw [path, ite_eq_left (by norm_num), BalancedLoader.path_before _ (by norm_num)]

theorem path_after (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {Ψ : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (BalancedPlanar.bodyVelocity I.1 hI.1) Ψ)
    {t : ℝ} (ht : 1 ≤ t) : path I hI Ψ t = bodyPath I hI Ψ t := by
  by_cases h : t ≤ 1
  · have he : t = 1 := le_antisymm h ht
    rw [he, path, ite_eq_left le_rfl, bodyPath_one I hI hΨ]
  · exact ite_eq_right h

theorem path_observation (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {Ψ Ω : ℝ → ℝ → Plane → Plane}
    (hΨ : IsPlanarTransition (BalancedPlanar.bodyVelocity I.1 hI.1) Ψ)
    (hΩ : IsPlanarTransition (planarSlice (BalancedPlanar.bodyHamiltonian I.1 hI.1)) Ω) :
    (∃ t, 0 ≤ t ∧ path I hI Ψ t ∈ BalancedStretch.observer) ↔ Alternating.Halts I := by
  have hsame (t : ℝ) : Ψ 0 t (BalancedPlanar.inputCode I hI) =
      Ω 0 t (BalancedPlanar.inputCode I hI) :=
    compactTransition_eq_slice (BalancedPlanar.referenceInput I.1)
      (BalancedPlanar.referenceValid hI.1) hΨ hΩ
      (BalancedPlanar.inputCode_in_unit I hI) 0 t
  constructor
  · rintro ⟨t, ht, he⟩
    by_contra hn
    by_cases h : t ≤ 1
    · rw [path, ite_eq_left h] at he
      exact BalancedLoader.path_safe (BalancedPlanar.inputCode_loader_guard I hI) t he
    · rw [path_after I hI hΨ (le_of_not_ge h), bodyPath, hsame] at he
      exact BalancedStretch.nonhalting_outside
        (BalancedPlanar.body_nonhalting_corridor I hI hΩ hn (by linarith)).2 he
  · intro hh
    obtain ⟨n, hx, hy⟩ := BalancedPlanar.body_halting_clearance I hI hΩ hh
    refine ⟨(n : ℝ)+1, by positivity, ?_⟩
    rw [path_after I hI hΨ (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith),
      bodyPath, add_sub_cancel_right, hsame]
    exact BalancedStretch.halting_inside hx hy

end ForcedComputation.BalancedPath

end

end OAI
