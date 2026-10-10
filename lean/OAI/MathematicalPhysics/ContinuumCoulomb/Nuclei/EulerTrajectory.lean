import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.EulerGeometry

namespace OAI

/-! The actual clipped-register iteration obeys the proved Euler error
estimate. All numerical values here are the rational register values;
the hypotheses concern the usual velocity error, speed and Lipschitz bounds. -/

noncomputable section
namespace ContinuumCoulomb.EulerRegisters
open CappedKernelProgram (Triple position)

variable {E : Type}

def initial (e : E) (N D B : ℕ) (r : Registers) : Config E :=
  ((e,(D,(B,(N:ℚ)⁻¹))),(0,r))

def trajectory (evaluate : E → ℚ → Triple → Triple) (e : E) (N D B : ℕ)
    (r : Registers) (n : ℕ) : Triple :=
  point D (((advance evaluate)^[n] (initial e N D B r)).2.2)

theorem trajectory_zero (evaluate : E → ℚ → Triple → Triple) (e : E) (N D B : ℕ)
    (r : Registers) : trajectory evaluate e N D B r 0 = point D r := rfl

theorem trajectory_succ (evaluate : E → ℚ → Triple → Triple) (e : E) (N D B : ℕ)
    (r : Registers) (n : ℕ) :
    trajectory evaluate e N D B r (n+1) =
      point D (round D B (proposal (N:ℚ)⁻¹ (trajectory evaluate e N D B r n)
        (evaluate e ((n:ℚ)*(N:ℚ)⁻¹) (trajectory evaluate e N D B r n)))) := by
  unfold trajectory
  rw [Function.iterate_succ_apply']
  simp only [advance,iterate_parameters,iterate_counter,initial,Nat.zero_add]

/-- Final error for the exact rational register recurrence. The box
condition is only imposed on the true solution, not on numerical proposals. -/
theorem trajectory_error (evaluate : E → ℚ → Triple → Triple) (e : E)
    {N D : ℕ} (hN : 0 < N) (hD : 0 < D) (B : ℕ) (r : Registers)
    (v : ℝ → Position → Position) (z : ℝ → Position)
    {L M δ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hz : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt z (v t (z t)) (Set.Icc (0:ℝ) 1) t)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖v t (z t)‖ ≤ M)
    (hLip : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x w,
      ‖v s x-v t w‖ ≤ L*(|s-t|+‖x-w‖))
    (hbox : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ a, |z t a| ≤ (B:ℝ)/(D:ℝ))
    (heval : ∀ n < N,
      ‖position (evaluate e ((n:ℚ)*(N:ℚ)⁻¹) (trajectory evaluate e N D B r n))-
        v ((n:ℝ)/N) (position (trajectory evaluate e N D B r n))‖ ≤ δ) :
    ‖position (trajectory evaluate e N D B r N)-z 1‖ ≤
      (‖position (point D r)-z 0‖+δ+L*(1+M)/(N:ℝ)+3*(N:ℝ)/(D:ℝ))*Real.exp L := by
  let y : ℕ → Position := fun n => position (trajectory evaluate e N D B r n)
  let sample : ℕ → Position → Position := fun n _ =>
    position (evaluate e ((n:ℚ)*(N:ℚ)⁻¹) (trajectory evaluate e N D B r n))
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hp (n : ℕ) (hn : n < N) :
      ‖y (n+1)-z (((n:ℝ)+1)/N)‖ ≤
        ‖y n+(N:ℝ)⁻¹ • sample n (y n)-z (((n:ℝ)+1)/N)‖+3/(D:ℝ) := by
    have ht : ((n:ℝ)+1)/(N:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · positivity
      · apply (div_le_one hNp).mpr
        exact_mod_cast (show n+1 ≤ N by omega)
    have he := round_position_error hD
      (proposal (N:ℚ)⁻¹ (trajectory evaluate e N D B r n)
        (evaluate e ((n:ℚ)*(N:ℚ)⁻¹) (trajectory evaluate e N D B r n)))
      (z (((n:ℝ)+1)/N)) (hbox _ ht)
    simpa only [y,sample,trajectory_succ,proposal_position,Rat.cast_inv,Rat.cast_natCast] using he
  have he := EulerApproximation.sampled_unit_error v z sample y hN hL hM hδ
    (show 0 ≤ 3/(D:ℝ) by positivity) hz hbound hLip heval hp
  have hmul : (N:ℝ)*(3/(D:ℝ)) = 3*(N:ℝ)/(D:ℝ) := by ring
  simpa only [y,trajectory_zero,hmul] using he

end ContinuumCoulomb.EulerRegisters

end

end OAI
