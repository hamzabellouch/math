import OAI.Analysis.Laughlin.Asymptotics.Bound
import OAI.Analysis.Laughlin.Spin.Highest

namespace OAI

namespace Laughlin.Spin

noncomputable def highestReadout (Q z : ℕ) : ℝ :=
  if z = 0 then -highestUnit (2*Q-2) Q z 0 else
    -highestUnit (2*Q-2) Q z (z-1) * (z : ℝ) *
      Real.sqrt ((Q.choose z : ℝ)/((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ))) +
    highestUnit (2*Q-2) Q z z * ((z : ℝ)-1) *
      Real.sqrt ((Q.choose z : ℝ)/((2*Q-2).choose z : ℝ))

theorem source_readout_rational_identity (Q z : ℕ) (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hz₀ : 1 ≤ z) :
    (z : ℝ)^2*(Q.choose z : ℝ)/((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ)) +
      ((z : ℝ)-1)*(Q.choose z : ℝ)/((2*Q-2).choose z : ℝ) =
    (Q.choose z : ℝ)/((2*Q-2).choose z : ℝ)*
      (3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/Q) := by
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hc : (((2*Q-2).choose z : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega : z ≤ 2*Q-2))
  have hp : (((2*Q-2).choose (z-1) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega : z-1 ≤ 2*Q-2))
  have he := choose_step_real (2*Q-2) (z-1) (by omega)
  rw [show z-1+1=z by omega] at he
  have hcast : ((z-1 : ℕ) : ℝ)+1 = (z : ℝ) := by
    rw [Nat.cast_sub hz₀]; push_cast; ring
  have hcast' : ((2*Q-2-(z-1) : ℕ) : ℝ) = 2*(Q : ℝ)-1-z := by
    rw [Nat.cast_sub (by omega : z-1 ≤ 2*Q-2),Nat.cast_sub (by omega : 2 ≤ 2*Q),
      Nat.cast_sub hz₀]; push_cast; ring
  rw [hcast,hcast'] at he
  field_simp
  linear_combination (z : ℝ)*(Q.choose z : ℝ)*he

theorem highestReadout_eq_formula (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    highestReadout Q z = gramEigenvalueFormula Q z * highestUnit (2*Q-2) Q z 0 := by
  by_cases hz₀ : z = 0
  · subst z
    simp [highestReadout,gramEigenvalueFormula,fallingRatio]
  have hzpos : 1 ≤ z := by omega
  have hA : z ≤ 2*Q-2 := by omega
  have hs := highestUnit_ne_zero (2*Q-2) Q z 0 hA hz (by omega)
  have hend := highest_end_ratio (2*Q-2) Q z hA hz
  have hprev := highest_penultimate_ratio (2*Q-2) Q z hA hz hzpos
  have hsign : (-1 : ℝ)^z = -((-1 : ℝ)^(z-1)) := by
    have hh : z = (z-1)+1 := by omega
    conv_lhs => rw [hh,pow_succ]
    ring
  have hprev' := (div_eq_iff hs).mp hprev
  have hend' := (div_eq_iff hs).mp hend
  rw [highestReadout,ite_eq_right hz₀,hprev',hend']
  rw [show ((2*Q-2).choose (z-1) : ℝ)*(Q : ℝ) =
    (Q : ℝ)*((2*Q-2).choose (z-1) : ℝ) by ring]
  have he := source_readout_rational_identity Q z hQ hz hzpos
  have hc := choose_ratio_descFactorial (2*Q-2) Q z
  change (Q.choose z : ℝ)/((2*Q-2).choose z : ℝ) = fallingRatio Q z at hc
  calc
    _ = (-1 : ℝ)^z * ((z : ℝ)^2 * (Q.choose z : ℝ) /
        ((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ)) +
      ((z : ℝ)-1)*(Q.choose z : ℝ)/((2*Q-2).choose z : ℝ)) *
      highestUnit (2*Q-2) Q z 0 := by
      rw [hsign]
      have h₁ := Real.sq_sqrt (show 0 ≤ (Q.choose z : ℝ)/
        ((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ)) by positivity)
      have h₂ := Real.sq_sqrt (show 0 ≤ (Q.choose z : ℝ)/((2*Q-2).choose z : ℝ) by positivity)
      linear_combination
        -((-1 : ℝ)^(z-1))*(z : ℝ)^2*highestUnit (2*Q-2) Q z 0*h₁ +
        -((-1 : ℝ)^(z-1))*((z : ℝ)-1)*highestUnit (2*Q-2) Q z 0*h₂
    _ = _ := by rw [he,hc]; unfold gramEigenvalueFormula; ring

end Laughlin.Spin

end OAI
