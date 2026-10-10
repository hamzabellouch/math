import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ComputableResolvent
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactQuotientBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellLocalization

namespace OAI

/-! A fixed guard turns the actual heat-resolvent evaluator into an
evaluator of the compact manufactured planar well. The guard is chosen
once on the unit disk; no instance-dependent real parameter is encoded. -/

noncomputable section
namespace ContinuumCoulomb.PlanarWellNumerics

private theorem guard_exists : ∃ C : ℕ, 0 < C ∧
    ∀ r : PlanarPosition, ‖r‖ ≤ 1 → 2 ≤ (C:ℝ)*planarResolventMode r := by
  obtain ⟨r,hr,hmin⟩ := (isCompact_closedBall (0:PlanarPosition) 1).exists_isMinOn
    (Metric.nonempty_closedBall.mpr (by norm_num)) planarResolventMode_C7.continuous.continuousOn
  obtain ⟨C,hC⟩ := exists_nat_gt (2/planarResolventMode r + 1)
  have hp := planarResolventMode_positive r
  have hCp : 0 < C := by
    have hh : (0:ℝ) < C := lt_trans (by positivity) hC
    exact_mod_cast hh
  refine ⟨C,hCp,fun s hs => ?_⟩
  have hs' : s ∈ Metric.closedBall (0:PlanarPosition) 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hs
  have hbase : 2 ≤ (C:ℝ)*planarResolventMode r := by
    have hc : 2/planarResolventMode r ≤ C := by linarith
    exact (div_le_iff₀ hp).mp hc
  exact hbase.trans (mul_le_mul_of_nonneg_left (hmin hs') (Nat.cast_nonneg C))

def guard : ℕ := Classical.choose guard_exists

theorem guard_positive : 0 < guard := (Classical.choose_spec guard_exists).1

theorem guard_bound (r : PlanarPosition) (hr : ‖r‖ ≤ 1) :
    2 ≤ (guard:ℝ)*planarResolventMode r := (Classical.choose_spec guard_exists).2 r hr

def precision (p : ℕ) : ℕ := 4*guard^2*(p+1)

def outside (q : ℚ×ℚ) : Prop := 1 ≤ q.1^2+q.2^2
instance (q : ℚ×ℚ) : Decidable (outside q) := inferInstanceAs (Decidable (1 ≤ q.1^2+q.2^2))

def approximate (p : ℕ) (q : ℚ×ℚ) : ℚ :=
  if outside q then 0 else
    -PlanarForcingProgram.value q /
      (2*ResolventSchedule.approximate ((2,precision p),q))

theorem outside_norm {q : ℚ×ℚ} (hq : outside q) :
    1 ≤ ‖PlanarForcingProgram.position q‖ := by
  have hqR : (1:ℝ) ≤ (q.1:ℝ)^2+(q.2:ℝ)^2 := by exact_mod_cast hq
  rw [← PlanarForcingProgram.position_norm_sq] at hqR
  nlinarith [norm_nonneg (PlanarForcingProgram.position q)]

theorem inside_norm {q : ℚ×ℚ} (hq : ¬ outside q) :
    ‖PlanarForcingProgram.position q‖ ≤ 1 := by
  have hqR : (q.1:ℝ)^2+(q.2:ℝ)^2 < 1 := by exact_mod_cast lt_of_not_ge hq
  rw [← PlanarForcingProgram.position_norm_sq] at hqR
  nlinarith [norm_nonneg (PlanarForcingProgram.position q)]

theorem approximation_error (p : ℕ) (q : ℚ×ℚ) :
    |(approximate p q:ℝ)-manufacturedPlanarWell (PlanarForcingProgram.position q)| ≤
      ((p:ℝ)+1)⁻¹ := by
  by_cases hq : outside q
  · rw [approximate,ite_eq_left hq,manufacturedPlanarWell_zero_of_norm_ge_one (outside_norm hq)]
    simp only [Rat.cast_zero,sub_self,abs_zero]
    positivity
  · have hr := inside_norm hq
    let r := PlanarForcingProgram.position q
    let ε : ℝ := ((precision p:ℝ)+1)⁻¹
    have hC : (1:ℝ) ≤ guard := by exact_mod_cast guard_positive
    have hCp : (0:ℝ) < guard := by linarith
    have hp : (0:ℝ) < (p:ℝ)+1 := by positivity
    have hprec : (precision p:ℝ) = 4*(guard:ℝ)^2*((p:ℝ)+1) := by
      simp only [precision,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    have hsmall : (guard:ℝ)*ε ≤ 1 := by
      dsimp [ε]
      apply (mul_inv_le_iff₀ (by positivity)).mpr
      rw [hprec]
      nlinarith [sq_nonneg ((guard:ℝ)-1),Nat.cast_nonneg (α := ℝ) p]
    have heval := ResolventSchedule.approximation_error ((2,precision p),q)
      (by exact hr.trans (by norm_num))
    have hb : |-planarForcing r| ≤ 4 := by
      rw [abs_neg,abs_of_nonneg (planarForcing_nonnegative r)]
      linarith [planarForcing_le_one r]
    have h := contact_quotient_error hC (planarResolventMode_positive r)
      (guard_bound r hr) (by dsimp [ε]; positivity) hsmall hb heval
      (show |-planarForcing r - -planarForcing r| ≤ ε by simp only [sub_self,abs_zero]; dsimp [ε]; positivity)
    have hlast : 3*(guard:ℝ)^2*ε ≤ ((p:ℝ)+1)⁻¹ := by
      dsimp [ε]
      rw [hprec]
      apply (mul_le_mul_iff_left₀ hp).mp
      field_simp
      nlinarith [sq_nonneg (guard:ℝ)]
    apply (le_trans ?_ hlast)
    simpa only [approximate,ite_eq_right hq,manufacturedPlanarWell,PlanarForcingProgram.value_cast,
      Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_neg,r] using h

end ContinuumCoulomb.PlanarWellNumerics

end

end OAI
