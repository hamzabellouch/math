import OAI.MathematicalPhysics.NavierStokes.ShearFlows.MaterialFlow

namespace OAI

/-! Integer-time sampling of the material flow of a periodic program. -/

noncomputable section

namespace ShearFlows

theorem TimePeriodic.nat_shift {V : Velocity} (hV : TimePeriodic V)
    (n : ℕ) (t : ℝ) (x : Space) : V (t + (n : ℝ), x) = V (t, x) := by
  have hp : Function.Periodic (fun s => V (s, x)) 1 := fun s => hV s x
  simpa only [mul_one] using hp.nat_mul n t

theorem IsMaterialFlow.nat_shift {L : ℝ} {V : Velocity}
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow L V Φ) (hV : TimePeriodic V)
    (n : ℕ) (t : ℝ) (a : Space) :
    Φ (t + (n : ℝ)) a = Φ t (Φ n a) := by
  apply hΦ.unique (Φ n a) (fun s => Φ (s + (n : ℝ)) a)
  · simp
  · intro s
    have hd := (hΦ.ode (s + (n : ℝ)) a).scomp s ((hasDerivAt_id s).add_const (n : ℝ))
    simpa only [one_smul, Function.comp_def, id_eq, hV.nat_shift] using hd

theorem IsMaterialFlow.nat_eq_iterate {L : ℝ} {V : Velocity}
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow L V Φ) (hV : TimePeriodic V)
    (n : ℕ) (a : Space) : Φ n a = (Φ 1)^[n] a := by
  induction n with
  | zero => simpa using hΦ.initial a
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_comm, hΦ.nat_shift hV, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

end ShearFlows

end

end OAI
