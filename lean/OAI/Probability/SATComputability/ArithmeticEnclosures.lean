import OAI.Probability.SATComputability.EffectiveLog
import OAI.MathematicalPhysics.RapidForcing.ComputableProfiles

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Filter RapidForcing.EffectiveProfile RapidForcing.EffectiveArithmetic
open PeriodicLattice.CertifiedReal
open scoped Topology
local instance arithmeticEnclosuresRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

@[fun_prop] theorem rat_max_computable : Computable (fun p : ℚ × ℚ => max p.1 p.2) := by
  simpa only [max_def] using
    (show Computable (fun p : ℚ × ℚ => if p.1 ≤ p.2 then p.2 else p.1) by fun_prop)

private theorem exp_effective : Effective (fun q : ℚ => Real.exp (q : ℝ)) :=
  (rational (Computable.id : Computable (id : ℚ → ℚ))).exp

private theorem log_effective : Effective (fun q : ℚ => Real.log (max 1 (q : ℝ))) := by
  have he : Effective (fun q : ℚ => ((max 1 q : ℚ) : ℝ)) :=
    rational (show Computable (fun q : ℚ => max 1 q) by fun_prop)
  simpa only [Rat.cast_max, Rat.cast_one] using he.log
    (fun q => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by exact_mod_cast le_max_left (1 : ℚ) q))

noncomputable def expApprox : ℚ × ℕ → ℚ := Classical.choose exp_effective
noncomputable def logApprox : ℚ × ℕ → ℚ := Classical.choose log_effective

@[fun_prop] theorem expApprox_computable : Computable expApprox := (Classical.choose_spec exp_effective).1
@[fun_prop] theorem logApprox_computable : Computable logApprox := (Classical.choose_spec log_effective).1

theorem expApprox_error (q : ℚ) (n : ℕ) :
    |Real.exp (q : ℝ) - (expApprox (q,n) : ℝ)| ≤ error n :=
  (Classical.choose_spec exp_effective).2 q n

theorem logApprox_error (q : ℚ) (n : ℕ) :
    |Real.log (max 1 (q : ℝ)) - (logApprox (q,n) : ℝ)| ≤ error n :=
  (Classical.choose_spec log_effective).2 q n

noncomputable def interval (l u : ℚ) : Ball := ⟨(l+u)/2, (u-l)/2⟩

@[fun_prop] theorem interval_computable : Computable (fun p : ℚ × ℚ => interval p.1 p.2) := by
  unfold interval
  fun_prop

theorem interval_covers {l u : ℚ} {x : ℝ} (hl : (l : ℝ) ≤ x) (hu : x ≤ (u : ℝ)) :
    (interval l u).Covers x := by
  unfold interval Ball.Covers
  push_cast
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem interval_encloses {l u : ℕ → ℚ} {x : ℝ}
    (hl : ∀ n, (l n : ℝ) ≤ x) (hu : ∀ n, x ≤ (u n : ℝ))
    (htl : Tendsto (fun n => (l n : ℝ)) atTop (nhds x))
    (htu : Tendsto (fun n => (u n : ℝ)) atTop (nhds x)) :
    Encloses (fun n => interval (l n) (u n)) x := by
  refine ⟨fun n => interval_covers (hl n) (hu n), ?_⟩
  simpa only [interval, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat, sub_self, zero_div]
    using (htu.sub htl).div_const 2

theorem approximate_tendsto {f : ℚ → ℝ} {a : ℚ × ℕ → ℚ}
    (ha : ∀ q n, |f q - (a (q,n) : ℝ)| ≤ error n)
    {q : ℕ → ℚ} {x : ℝ} (hq : Tendsto (fun n => f (q n)) atTop (nhds x)) :
    Tendsto (fun n => (a (q n,n) : ℝ)) atTop (nhds x) := by
  have hz : Tendsto (fun n => (a (q n,n) : ℝ)-f (q n)) atTop (nhds 0) := by
    apply squeeze_zero_norm (fun n => ?_) error_tendsto
    simpa only [Real.norm_eq_abs, abs_sub_comm] using ha (q n) n
  simpa only [sub_add_cancel, zero_add] using hz.add hq

noncomputable def expBall (b : Ball) (n : ℕ) : Ball :=
  interval (expApprox (b.center-b.radius,n)-qerror n)
    (expApprox (b.center+b.radius,n)+qerror n)

noncomputable def logBall (b : Ball) (n : ℕ) : Ball :=
  interval (logApprox (b.center-b.radius,n)-qerror n)
    (logApprox (b.center+b.radius,n)+qerror n)

@[fun_prop] theorem expBall_computable : Computable (fun p : Ball × ℕ => expBall p.1 p.2) := by
  unfold expBall
  fun_prop
@[fun_prop] theorem logBall_computable : Computable (fun p : Ball × ℕ => logBall p.1 p.2) := by
  unfold logBall
  fun_prop

theorem expBall_covers {b : Ball} {x : ℝ} (hb : b.Covers x) (n : ℕ) :
    (expBall b n).Covers (Real.exp x) := by
  have he := abs_le.mp hb
  have hl := (abs_le.mp (expApprox_error (b.center-b.radius) n)).1
  have hu := (abs_le.mp (expApprox_error (b.center+b.radius) n)).2
  apply interval_covers
  · push_cast
    have := Real.exp_le_exp.mpr (show (b.center : ℝ)-b.radius ≤ x by linarith)
    simp only [Rat.cast_sub, cast_qerror] at hl ⊢
    linarith
  · push_cast
    have := Real.exp_le_exp.mpr (show x ≤ (b.center : ℝ)+b.radius by linarith)
    simp only [Rat.cast_add, cast_qerror] at hu ⊢
    linarith

theorem logBall_covers {b : Ball} {x : ℝ} (hb : b.Covers x) (n : ℕ) :
    (logBall b n).Covers (Real.log (max 1 x)) := by
  have he := abs_le.mp hb
  have hl := (abs_le.mp (logApprox_error (b.center-b.radius) n)).1
  have hu := (abs_le.mp (logApprox_error (b.center+b.radius) n)).2
  have hp (y : ℝ) : 0 < max 1 y := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  apply interval_covers
  · push_cast
    have := Real.log_le_log (hp ((b.center : ℝ)-b.radius))
      (max_le_max_left 1 (show (b.center : ℝ)-b.radius ≤ x by linarith))
    simp only [Rat.cast_sub, cast_qerror] at hl ⊢
    linarith
  · push_cast
    have := Real.log_le_log (hp x)
      (max_le_max_left 1 (show x ≤ (b.center : ℝ)+b.radius by linarith))
    simp only [Rat.cast_add, cast_qerror] at hu ⊢
    linarith

theorem Encloses.exp {b : ℕ → Ball} {x : ℝ} (hb : Encloses b x) :
    Encloses (fun n => expBall (b n) n) (Real.exp x) := by
  have hbl : Tendsto (fun n => (((b n).center-(b n).radius : ℚ) : ℝ)) atTop (nhds x) := by
    simpa only [Rat.cast_sub, sub_zero] using hb.centers.sub hb.2
  have hbu : Tendsto (fun n => (((b n).center+(b n).radius : ℚ) : ℝ)) atTop (nhds x) := by
    simpa only [Rat.cast_add, add_zero] using hb.centers.add hb.2
  have hl := approximate_tendsto expApprox_error
    (q := fun n => (b n).center-(b n).radius) (Real.continuous_exp.tendsto x |>.comp hbl)
  have hu := approximate_tendsto expApprox_error
    (q := fun n => (b n).center+(b n).radius) (Real.continuous_exp.tendsto x |>.comp hbu)
  refine ⟨fun n => expBall_covers (hb.1 n) n, ?_⟩
  have hlim := ((hu.add error_tendsto).sub (hl.sub error_tendsto)).div_const 2
  simpa only [expBall, interval, Rat.cast_div, Rat.cast_sub, Rat.cast_add,
    Rat.cast_ofNat, cast_qerror, add_zero, sub_zero, sub_self, zero_div] using hlim

theorem Encloses.log {b : ℕ → Ball} {x : ℝ} (hb : Encloses b x) :
    Encloses (fun n => logBall (b n) n) (Real.log (max 1 x)) := by
  have hp : max (1 : ℝ) x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hbl : Tendsto (fun n => (((b n).center-(b n).radius : ℚ) : ℝ)) atTop (nhds x) := by
    simpa only [Rat.cast_sub, sub_zero] using hb.centers.sub hb.2
  have hbu : Tendsto (fun n => (((b n).center+(b n).radius : ℚ) : ℝ)) atTop (nhds x) := by
    simpa only [Rat.cast_add, add_zero] using hb.centers.add hb.2
  have hl := approximate_tendsto logApprox_error
    (q := fun n => (b n).center-(b n).radius) ((tendsto_const_nhds.max hbl).log hp)
  have hu := approximate_tendsto logApprox_error
    (q := fun n => (b n).center+(b n).radius) ((tendsto_const_nhds.max hbu).log hp)
  refine ⟨fun n => logBall_covers (hb.1 n) n, ?_⟩
  have hlim := ((hu.add error_tendsto).sub (hl.sub error_tendsto)).div_const 2
  simpa only [logBall, interval, Rat.cast_div, Rat.cast_sub, Rat.cast_add,
    Rat.cast_ofNat, cast_qerror, add_zero, sub_zero, sub_self, zero_div] using hlim

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
