import OAI.MathematicalPhysics.NavierStokes.ShearFlows.MaterialFlow

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology NNReal
namespace ShearFlows

theorem sevenFields_invariant {n : ℕ}
    (p q : Fin n → Plane) (lam z : Fin n → ℝ) (z₀ : ℝ)
    (Am Ap : Fin n → Plane → ℝ) (Z gx gy : Fin n → ℝ → ℝ) :
    ∀ j x (c : ℝ), sevenFields p q lam z z₀ Am Ap Z gx gy j
        (x + c • sevenFields p q lam z z₀ Am Ap Z gx gy j x) =
      sevenFields p q lam z z₀ Am Ap Z gx gy j x := by
  intro j x c
  have h01 (i : Fin n) : selectTwo 0 1 (basis 2) = 0 := selectTwo_basis (by decide) (by decide)
  have h02 (i : Fin n) : selectTwo 0 2 (basis 1) = 0 := selectTwo_basis (by decide) (by decide)
  have h12 (i : Fin n) : selectTwo 1 2 (basis 0) = 0 := selectTwo_basis (by decide) (by decide)
  have hz (i : Fin n) : (ContinuousLinearMap.proj 2 : Space →L[ℝ] ℝ)
      (atHeight (q i - p i) 0) = 0 := rfl
  fin_cases j <;> simp [sevenFields]
  · exact transverseSum_invariant _ _ _ h01 x c
  · exact transverseSum_invariant _ _ _ h02 x c
  · exact transverseSum_invariant _ _ _ h12 x c
  · exact transverseSum_invariant _ _ _ h02 x c
  · exact transverseSum_invariant _ _ _ h12 x c
  · exact transverseSum_invariant _ _ _ hz x c
  · exact transverseSum_invariant _ _ _ h01 x c

theorem spatialFields_invariant (d : Input) (j : Fin 7) (x : Space) (c : ℝ) :
    d.spatialFields j (x + c • d.spatialFields j x) = d.spatialFields j x :=
  sevenFields_invariant _ _ _ _ _ _ _ _ _ _ j x c

def blockStart (j : Fin 7) : ℝ := (j : ℕ) / 8

def blockFinish (j : Fin 7) : ℝ := ((j : ℕ) + 1) / 8

theorem block_bounds (j : Fin 7) :
    0 ≤ blockStart j ∧ blockStart j < (stageStart j : ℝ) ∧
      (stageFinish j : ℝ) = blockFinish j ∧ blockFinish j < 1 := by
  fin_cases j <;> norm_num [blockStart, blockFinish, stageStart, stageFinish]

theorem other_periodPulse_zero (j k : Fin 7) (hjk : k ≠ j) {t : ℝ}
    (ht : t ∈ Icc (blockStart j) (blockFinish j)) : periodPulse k t = 0 := by
  have ht01 : t ∈ Icc (0 : ℝ) 1 :=
    ⟨(block_bounds j).1.trans ht.1, ht.2.trans (block_bounds j).2.2.2.le⟩
  rw [periodPulse_eq_on_period k ht01]
  have hab : (stageStart k : ℝ) < stageFinish k := by exact_mod_cast (stage_intervals k).2.1
  rcases lt_or_gt_of_ne hjk with h | h
  · apply smoothPulse_after hab
    have h' : (stageFinish k : ℝ) ≤ blockStart j := by
      have : (k.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
      simp only [stageFinish, blockStart, Rat.cast_div, Rat.cast_add, Rat.cast_mul,
        Rat.cast_natCast, Rat.cast_ofNat]
      linarith
    exact h'.trans ht.1
  · apply smoothPulse_before hab
    have h' : blockFinish j ≤ (stageStart k : ℝ) := by
      have : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast h
      simp only [stageStart, blockFinish, Rat.cast_div, Rat.cast_add, Rat.cast_mul,
        Rat.cast_natCast, Rat.cast_ofNat]
      linarith
    exact ht.2.trans h'

theorem realizingVelocity_on_block (d : Input) (j : Fin 7) {t : ℝ}
    (ht : t ∈ Icc (blockStart j) (blockFinish j)) (x : Space) :
    d.realizingVelocity (t,x) = smoothPulse (stageStart j) (stageFinish j) t •
      d.spatialFields j x := by
  unfold Input.realizingVelocity pulsedSum
  rw [Finset.sum_eq_single j]
  · rw [periodPulse_eq_on_period j
      ⟨(block_bounds j).1.trans ht.1, ht.2.trans (block_bounds j).2.2.2.le⟩]
  · intro k _ hkj
    rw [other_periodPulse_zero j k hkj ht, zero_smul]
  · simp

theorem IsMaterialFlow.eqOn_of_candidate {L : ℝ} {V : Velocity}
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow L V Φ)
    {K : ℝ≥0} (hV : ∀ t, LipschitzWith K (fun x => V (t,x)))
    {a b : ℝ} (x : Space) (γ : ℝ → Space)
    (hc : ContinuousOn γ (Icc a b)) (he : γ a = Φ a x)
    (hγ : ∀ t ∈ Ico a b, HasDerivAt γ (V (t,γ t)) t) :
    EqOn (fun t => Φ t x) γ (Icc a b) := by
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun t _ => (hV t).lipschitzOnWith)
    ((continuous_iff_continuousAt.mpr (fun t => (hΦ.ode t x).continuousAt)).continuousOn)
    (fun t _ => (hΦ.ode t x).hasDerivWithinAt) (fun _ _ => mem_univ _)
    hc (fun t ht => (hγ t ht).hasDerivWithinAt) (fun _ _ => mem_univ _) he.symm

theorem materialFlow_on_block {d : Input} (hd : ValidInput d)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ)
    (j : Fin 7) (x : Space) {t : ℝ} (ht : t ∈ Icc (blockStart j) (blockFinish j)) :
    Φ t x = Φ (blockStart j) x + standardSchedule.progress j t •
      d.spatialFields j (Φ (blockStart j) x) := by
  obtain ⟨K,hK⟩ := smooth_periodic_lipschitz (by exact_mod_cast hd.period_pos)
    (realizingVelocity_smooth hd) (realizingVelocity_spatially_periodic d)
    (realizingVelocity_time_periodic d)
  have hV (s : ℝ) : LipschitzWith K (fun y => d.realizingVelocity (s,y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa using hK.dist_le_mul (s,y) (s,z)
  let A := Φ (blockStart j) x
  let γ : ℝ → Space := fun s => A + standardSchedule.progress j s • d.spatialFields j A
  have hc : Continuous γ := continuous_const.add
    ((standardSchedule.smooth j).continuous.smul continuous_const)
  have he : γ (blockStart j) = Φ (blockStart j) x := by
    dsimp [γ]
    rw [standardSchedule.before j _ (block_bounds j).2.1.le, zero_smul, add_zero]
  have hγ (s : ℝ) (hs : s ∈ Ico (blockStart j) (blockFinish j)) :
      HasDerivAt γ (d.realizingVelocity (s,γ s)) s := by
    rw [realizingVelocity_on_block d j ⟨hs.1,hs.2.le⟩, spatialFields_invariant]
    exact (((smoothRamp_smooth (stageStart j) (stageFinish j)).differentiable
      (by simp) s).hasDerivAt.smul_const (d.spatialFields j A)).const_add A
  exact hΦ.eqOn_of_candidate hV x γ hc.continuousOn he hγ ht

theorem materialFlow_block_endpoint {d : Input} (hd : ValidInput d)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ)
    (j : Fin 7) (x : Space) :
    Φ (blockFinish j) x = Φ (blockStart j) x + d.spatialFields j (Φ (blockStart j) x) := by
  rw [materialFlow_on_block hd hΦ j x]
  · rw [standardSchedule.after j _ (block_bounds j).2.2.1.le, one_smul]
  · exact ⟨(block_bounds j).2.1.le.trans ((by exact_mod_cast
      (stage_intervals j).2.1.le : (stageStart j : ℝ) ≤ stageFinish j).trans
      (block_bounds j).2.2.1.le),le_refl _⟩

theorem materialFlow_period_tail {d : Input} (hd : ValidInput d)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ)
    (x : Space) {t : ℝ} (ht : t ∈ Icc (7/8 : ℝ) 1) : Φ t x = Φ (7/8) x := by
  obtain ⟨K,hK⟩ := smooth_periodic_lipschitz (by exact_mod_cast hd.period_pos)
    (realizingVelocity_smooth hd) (realizingVelocity_spatially_periodic d)
    (realizingVelocity_time_periodic d)
  have hV (s : ℝ) : LipschitzWith K (fun y => d.realizingVelocity (s,y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa using hK.dist_le_mul (s,y) (s,z)
  apply hΦ.eqOn_of_candidate hV x (fun _ => Φ (7/8) x) continuousOn_const rfl _ ht
  intro s hs
  rw [realizingVelocity_gaps d ⟨by linarith [hs.1],hs.2.le⟩]
  · exact hasDerivAt_const _ _
  · intro j hj
    have hfin : (stageFinish j : ℝ) ≤ 7/8 := by
      fin_cases j <;> norm_num [stageFinish]
    linarith [hj.2,hs.1]

end ShearFlows

end

end OAI
