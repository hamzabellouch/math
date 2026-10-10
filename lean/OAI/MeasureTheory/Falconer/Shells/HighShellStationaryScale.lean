import OAI.MeasureTheory.Falconer.Angular.AngularFarStationaryScale
import OAI.MeasureTheory.Falconer.Recursion.MinimalDescriptorLength
import OAI.MeasureTheory.Falconer.Estimates.PositiveDistanceWeight

namespace OAI

namespace PlanarFalconer

theorem high_shell_gap {sig : ℝ} {N q a t : ℕ} {v : ℝ}
    (hq : sig*(N:ℝ) ≤ (q:ℝ)) (hw : a+100*q < t)
    (hv : (t:ℝ)-sig*N ≤ v) : 99*sig*N ≤ v-a := by
  have hw' : (a:ℝ)+100*(q:ℝ) < (t:ℝ) := by exact_mod_cast hw
  linarith

theorem high_shell_stationary_slack {sig v Λ : ℝ} (hsig : 0 ≤ sig)
    (N L a t : ℕ) (hL : 2*(L:ℝ) ≤ (t:ℝ)-a)
    (hgap : 99*sig*N ≤ v-a) (hv : (t:ℝ)-sig*N ≤ v)
    (hΛ : (2:ℝ)^(v-a) ≤ Λ) :
    ((2:ℝ)^N)^(90*sig) ≤ Λ ∧
    sourceSymbolScale N sig L^2/Λ ≤ ((2:ℝ)^N)^(-90*sig) := by
  have hn : 0 ≤ (N:ℝ)*sig := mul_nonneg (Nat.cast_nonneg _) hsig
  have hΛpos : 0 < Λ := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hΛ
  have hD : sourceSymbolScale N sig L ≤ (2:ℝ)^((v-a-90*(N:ℝ)*sig)/2) := by
    rw [sourceSymbolScale_dyadic]
    apply max_le <;> apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    · nlinarith
    · nlinarith
  have hD2 : sourceSymbolScale N sig L^2 ≤ (2:ℝ)^(v-a)*((2:ℝ)^N)^(-90*sig) := by
    apply (pow_le_pow_left₀ (sourceSymbolScale_pos N sig L).le hD 2).trans_eq
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    push_cast
    ring
  refine ⟨?_,(div_le_iff₀ hΛpos).mpr ?_⟩
  · apply le_trans _ hΛ
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    nlinarith
  · exact hD2.trans (by simpa [mul_comm] using
      mul_le_mul_of_nonneg_right hΛ (by positivity : 0 ≤ ((2:ℝ)^N)^(-90*sig)))

theorem high_shell_frequency {a v r d : ℝ}
    (hr : (2:ℝ)^(v-1) ≤ r) (hd : 96*(2:ℝ)^(-a) ≤ d) :
    (2:ℝ)^(v-a) ≤ r*d := by
  have hprod := mul_le_mul hr hd (by positivity : 0 ≤ 96*(2:ℝ)^(-a))
    ((Real.rpow_pos_of_pos (by norm_num) _).trans_le hr).le
  have he : (2:ℝ)^(v-1)*(96*(2:ℝ)^(-a)) = 48*(2:ℝ)^(v-a) := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2),Real.rpow_one]
    rw [show v-a = v+(-a) by ring,Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    ring
  rw [he] at hprod
  linarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (v-a)]

namespace PositiveDistanceData

theorem actual_high_shell_stationary_slack (d : PositiveDistanceData)
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (hsig : 0 ≤ d.sig)
    (hq : d.sig*d.N ≤ (d.q:ℝ)) (hw : d.a+100*d.q < d.t)
    {v r : ℝ} (hv : (d.t:ℝ)-d.sig*d.N ≤ v) (hr : (2:ℝ)^(v-1) ≤ r)
    {z : Plane × Plane} (hx : z.1 ∈ (d.Q.descendant d.X).carrier)
    (hy : z.2 ∈ (d.Q.descendant d.Y).carrier) :
    ((2:ℝ)^d.N)^(90*d.sig) ≤ r*dist z.1 z.2 ∧
    sourceSymbolScale d.N d.sig ((d.t-d.a)/2)^2/(r*dist z.1 z.2) ≤
      ((2:ℝ)^d.N)^(-90*d.sig) := by
  have hat : d.a ≤ d.t := by omega
  have hl : 2*(((d.t-d.a)/2:ℕ):ℝ) ≤ (d.t:ℝ)-d.a := by
    have hh : 2*((d.t-d.a)/2) ≤ d.t-d.a := by omega
    have := (show (2:ℝ)*(((d.t-d.a)/2:ℕ):ℝ) ≤ ((d.t-d.a:ℕ):ℝ) by exact_mod_cast hh)
    simpa [Nat.cast_sub hat] using this
  have hd := (le_div_iff₀ (by positivity)).mp (d.separated_distance_ratio hQ hs hx hy).1
  exact high_shell_stationary_slack hsig d.N _ d.a d.t hl
    (high_shell_gap hq hw hv) hv (high_shell_frequency hr hd)

end PositiveDistanceData

end PlanarFalconer

end OAI
