import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

namespace OAI

/-! The short initial shell turns the tiny free logarithmic slope strictly negative. -/

open Set
namespace DefocusingNLS

theorem radial_phase_nonneg (u v : ℝ → ℝ) (R U : ℝ)
    (hv : ContinuousOn v (Icc R U)) (hvR : 0 ≤ v R)
    (hvd : ∀ r ∈ Icc R U,
      HasDerivAt v (-(2*u r+11/r)*v r+3) r) :
    ∀ r ∈ Icc R U, 0 ≤ v r := by
  have h := image_le_of_deriv_right_lt_deriv_boundary
    (f := fun r => -v r) (f' := fun r => -(-(2*u r+11/r)*v r+3))
    hv.neg (fun r hr => (hvd r ⟨hr.1,hr.2.le⟩).neg.hasDerivWithinAt)
    (B := fun _ => 0) (B' := fun _ => 0) (by linarith)
    (fun r => hasDerivAt_const r 0) (by
      intro r _ he
      have hz : v r=0 := by linarith
      simp only [hz,mul_zero,zero_add]
      norm_num)
  intro r hr
  have := h hr
  linarith

theorem radial_free_potential_lower (b r v : ℝ) (hb : (334/1000 : ℝ) ≤ b)
    (_hr : 0 ≤ r) (hr2 : r^2 ≤ (49/4 : ℝ)) (hv : 0 ≤ v) (hvu : v ≤ (543/2000 : ℝ)*r) :
    (18/100 : ℝ) < b+r^2/16-v^2 := by
  have hs : v^2 ≤ ((543/2000 : ℝ)*r)^2 :=
    pow_le_pow_left₀ hv hvu 2
  nlinarith

theorem radial_riccati_shell (u v : ℝ → ℝ) (b R S : ℝ)
    (hR : (3 : ℝ) ≤ R) (hRS : R ≤ S) (hwidth : S-R ≤ (1/1000 : ℝ))
    (hgap : (1/100000 : ℝ) ≤ S-R) (huc : ContinuousOn u (Icc R S))
    (hstart : u R ≤ (1/100000000 : ℝ))
    (hud : ∀ r ∈ Icc R S,
      HasDerivAt u (-(u r)^2-11/r*u r+(v r)^2-r^2/16-b) r)
    (hpot : ∀ r ∈ Icc R S, (18/100 : ℝ) < b+r^2/16-(v r)^2) :
    u S < 0 := by
  let B := fun r : ℝ => (1/100000000 : ℝ)-(r-R)/10
  have h := image_le_of_deriv_right_lt_deriv_boundary huc
    (fun r hr => (hud r ⟨hr.1,hr.2.le⟩).hasDerivWithinAt)
    (B := B) (B' := fun _ => -(1/10 : ℝ)) (by simpa [B] using hstart)
    (fun r => by
      convert (((hasDerivAt_id r).sub_const R).div_const 10).const_sub (1/100000000 : ℝ)
        using 1
      norm_num [B]) (by
      intro r hr he
      have hr0 : 0 < r := by linarith [hr.1]
      have hd : 0 ≤ 11/r := div_nonneg (by norm_num) hr0.le
      have hdu : 11/r ≤ (11/3 : ℝ) := (div_le_iff₀ hr0).mpr (by linarith [hr.1])
      have hul : -(1/1000 : ℝ) ≤ u r := by dsimp [B] at he; linarith [hr.2]
      have hmul := mul_le_mul_of_nonneg_left hul hd
      have hpotr := hpot r ⟨hr.1,hr.2.le⟩
      nlinarith [sq_nonneg (u r)])
  have hS := h ⟨hRS,le_rfl⟩
  dsimp [B] at hS
  linarith

theorem radial_riccati_nonpos (u v : ℝ → ℝ) (b S U : ℝ)
    (huc : ContinuousOn u (Icc S U)) (hstart : u S ≤ 0)
    (hud : ∀ r ∈ Icc S U,
      HasDerivAt u (-(u r)^2-11/r*u r+(v r)^2-r^2/16-b) r)
    (hpot : ∀ r ∈ Icc S U, 0 < b+r^2/16-(v r)^2) :
    ∀ r ∈ Icc S U, u r ≤ 0 := by
  apply image_le_of_deriv_right_lt_deriv_boundary huc
    (fun r hr => (hud r ⟨hr.1,hr.2.le⟩).hasDerivWithinAt)
    (B := fun _ => 0) (B' := fun _ => 0) hstart (fun r => hasDerivAt_const r 0)
  intro r hr he
  have hp := hpot r ⟨hr.1,hr.2.le⟩
  rw [he]
  nlinarith

end DefocusingNLS

end OAI
