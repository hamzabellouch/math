import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedVelocityEvaluation
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserNumericalBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.EulerInitialBox

namespace OAI

/-! The literal clipped Euler iteration approximates the actual manufactured
Moser flow. Its step count and denominator are fixed polynomials in the
requested unary precision, uniformly over all valid input geometries. -/

noncomputable section
namespace ContinuumCoulomb.ManufacturedEuler
open CappedKernelProgram (Triple position)
open EulerRegisters

abbrev Environment := ℕ×((ℚ×ℚ)×List (ℚ×ℚ))

def evaluate (rho : ℕ) (e : Environment) (t : ℚ) (q : Triple) : Triple :=
  ManufacturedVelocityEvaluation.value rho e.1 e.2.1.1 e.2.1.2 e.2.2 t q

def approximate (rho U C P : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ)) (q : Triple) : Triple :=
  let N := steps C P
  let D := denominator C P
  let B := boxNumerator U D q
  trajectory (evaluate rho) (N,((scale,S),sites)) N D B (round D B q) N

theorem approximation_error (rho U C P : ℕ) (hrho : 0 < rho) (hC : 0 < C)
    (hExp : Real.exp (U:ℝ) ≤ C) (hUC : (U:ℝ)*(1+(U:ℝ)) ≤ C)
    {scale S : ℚ} (hscale : (1:ℝ) ≤ scale) (hS : (1:ℝ) ≤ S)
    {m : ℕ} (u : Fin m → ℚ×ℚ) (hu : Function.Injective u)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale)
    (hcharge : ∀ x, |manufacturedCharge (manufacturedWellField (GaussianFrequency.frequency rho)
      scale S (fun i => PlanarForcingProgram.position (u i))) x| ≤ (rho:ℝ)/2)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x,
      ‖moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i))) t x‖ ≤ U)
    (hLip : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x y,
      ‖moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i))) s x-
        moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i))) t y‖ ≤
        (U:ℝ)*(|s-t|+‖x-y‖))
    (G : Position → ℝ → Position)
    (hG : IsUnitTimeFlow (moserVelocity (rho:ℝ)
      (manufacturedWellField (GaussianFrequency.frequency rho) scale S
        (fun i => PlanarForcingProgram.position (u i)))) G)
    (q : Triple) :
    ‖position (approximate rho U C P scale S (List.ofFn u) q)-G (position q) 1‖ ≤
      ((P:ℝ)+1)⁻¹ := by
  let V := manufacturedWellField (GaussianFrequency.frequency rho) scale S
    (fun i => PlanarForcingProgram.position (u i))
  let N := steps C P
  let D := denominator C P
  let B := boxNumerator U D q
  let e : Environment := (N,((scale,S),List.ofFn u))
  let z := G (position q)
  have hN : 0 < N := steps_positive hC
  have hD : 0 < D := pow_pos hN _
  have hz0 : z 0 = position q := hG.1 _
  have hz : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt z (moserVelocity (rho:ℝ) V t (z t)) (Set.Icc (0:ℝ) 1) t := hG.2 _
  have hzbox : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ a, |z t a| ≤ (B:ℝ)/(D:ℝ) := by
    have hh := trajectory_coordinate_box (moserVelocity (rho:ℝ) V) z
      (Nat.cast_nonneg U) hz (fun t ht => hbound t ht _) (fun a => by
        rw [hz0]
        exact inputRadius_bound q a)
    intro t ht a
    dsimp [B]
    rw [boxNumerator_ratio hD]
    exact (hh t ht a).trans (by linarith)
  have heval (n : ℕ) (hn : n < N) :
      ‖position (evaluate rho e ((n:ℚ)*(N:ℚ)⁻¹)
        (trajectory (evaluate rho) e N D B (round D B q) n))-
        moserVelocity (rho:ℝ) V ((n:ℝ)/N)
          (position (trajectory (evaluate rho) e N D B (round D B q) n))‖ ≤ ((N:ℝ)+1)⁻¹ := by
    have htime : (((n:ℚ)*(N:ℚ)⁻¹ : ℚ):ℝ) ∈ Set.Icc (0:ℝ) 1 := by
      rw [Rat.cast_mul,Rat.cast_natCast,Rat.cast_inv,Rat.cast_natCast,← div_eq_mul_inv]
      constructor
      · positivity
      · exact (div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast hn.le)
    have hh := ManufacturedVelocityEvaluation.approximation_error rho N hrho hscale hS u hu
      hsep hc hcharge (t := (n:ℚ)*(N:ℚ)⁻¹) htime (trajectory (evaluate rho) e N D B (round D B q) n)
    simpa only [evaluate,e,V,Rat.cast_mul,Rat.cast_natCast,Rat.cast_inv,div_eq_mul_inv] using hh
  have he := trajectory_error (evaluate rho) e hN hD B (round D B q)
    (moserVelocity (rho:ℝ) V) z (Nat.cast_nonneg U) (Nat.cast_nonneg U)
    (show 0 ≤ ((N:ℝ)+1)⁻¹ by positivity) hz (fun t ht => hbound t ht _) hLip hzbox heval
  rw [hz0] at he
  have hinit := initial_round_error (C := U) hD q
  have hb : (‖position (point D (round D B q))-position q‖+((N:ℝ)+1)⁻¹+
      (U:ℝ)*(1+(U:ℝ))/(N:ℝ)+3*(N:ℝ)/(D:ℝ))*Real.exp (U:ℝ) ≤
      (3/(D:ℝ)+((N:ℝ)+1)⁻¹+(U:ℝ)*(1+(U:ℝ))/(N:ℝ)+
        3*(N:ℝ)/(D:ℝ))*Real.exp (U:ℝ) := by
    exact mul_le_mul_of_nonneg_right
      (add_le_add (add_le_add (add_le_add hinit le_rfl) le_rfl) le_rfl)
      (Real.exp_pos _).le
  exact he.trans (hb.trans (schedule_budget hC hExp hUC))

/-- Fixed program constants work simultaneously for every valid manufactured
field. No oracle for a potential, derivative, or flow value is used. -/
theorem exists_uniform_constants (rho : ℕ) (hrho : 0 < rho) :
    ∃ U C : ℕ, 0 < U ∧ 0 < C ∧ ∀ (P : ℕ) (scale S : ℚ),
      (1:ℝ) ≤ scale → (1:ℝ) ≤ S → ∀ (m : ℕ) (u : Fin m → ℚ×ℚ),
      Function.Injective u →
      (∀ i j, i ≠ j → 3 ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖) →
      (∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
        (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) →
      (∀ x, |manufacturedCharge (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i))) x| ≤ (rho:ℝ)/2) →
      ∀ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i)))) G →
      ∀ q : Triple,
        ‖position (approximate rho U C P scale S (List.ofFn u) q)-G (position q) 1‖ ≤
          ((P:ℝ)+1)⁻¹ := by
  obtain ⟨U,hU,hUb⟩ := exists_uniform_velocity_integer rho hrho
  obtain ⟨C,hC⟩ := exists_nat_gt (max (Real.exp (U:ℝ)) ((U:ℝ)*(1+(U:ℝ))))
  have hCp : 0 < C := by
    have hp : (0:ℝ) < C := (Real.exp_pos _).trans ((le_max_left _ _).trans_lt hC)
    exact_mod_cast hp
  refine ⟨U,C,hU,hCp,?_⟩
  intro P scale S hs hS m u hu hsep hc hcharge G hG q
  let V := manufacturedWellField (GaussianFrequency.frequency rho) scale S
    (fun i => PlanarForcingProgram.position (u i))
  have hV : ContDiff ℝ 6 V := (manufacturedWellField_C7 _ _ _ _).of_le (by norm_num)
  have hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ (MoserDifferenceBudget.guard:ℝ) := by
    intro k hk x
    exact (manufacturedWellField_derivative_bound (GaussianFrequency.frequency rho)
      (show (0:ℝ) < scale by linarith) hS _ hsep hc hk x).trans MoserDifferenceBudget.guard_bound
  obtain ⟨hbound,hLip⟩ := hUb V hV hb hcharge
  exact approximation_error rho U C P hrho hCp ((le_max_left _ _).trans_lt hC).le
    ((le_max_right _ _).trans_lt hC).le hs hS u hu hsep hc hcharge hbound hLip G hG q

end ContinuumCoulomb.ManufacturedEuler

end

end OAI
