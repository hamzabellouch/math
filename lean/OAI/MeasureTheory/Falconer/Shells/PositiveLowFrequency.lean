import OAI.MeasureTheory.Falconer.Fourier.PositiveFourier
import OAI.MeasureTheory.Falconer.Shells.PositiveTerminal
import OAI.MeasureTheory.Falconer.Estimates.RegularizedCellCounts

namespace OAI

/-! # The low-frequency stopping term for the actual tested pair law -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem testedCellDistance_low_frequency (Q : DyadicCube d) (ρ : Measure (Space d))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m)
    {a : ℕ} (ha : a ≤ N) (X Y : List (Fin d → Bool))
    (hX : X.length = a) (hY : Y.length = a) (G : Set (Space d × Space d)) :
    (((2:ℝ)^N)^(4*m ((a:ℝ)/N))/(2:ℝ)^a) *
      (∫ r in Icc (-(2:ℝ)^a) ((2:ℝ)^a),
        ‖charFun (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y) G) r‖^2) ≤
      2*((2:ℝ)^N)^(4*((d:ℝ)+1)*lam) := by
  let := hreg.probability
  let θ := testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y) G
  let R := (2:ℝ)^N
  let L := ((d:ℝ)+1)*lam-m ((a:ℝ)/N)
  have hR : 0 < R := by dsimp [R]; positivity
  have hm : θ.real univ ≤ R^(2*L) := by
    have ht := ENNReal.toReal_mono (by finiteness)
      (testedCellDistance_mass_le ρ (Q.descendant X) (Q.descendant Y) G)
    have hp := mul_le_mul (hreg.cell_mass_upper ha X hX) (hreg.cell_mass_upper ha Y hY)
      (ENNReal.toReal_nonneg) (by positivity)
    change θ.real univ ≤ _
    apply (show θ.real univ ≤ (ρ (Q.descendant X).carrier).toReal *
        (ρ (Q.descendant Y).carrier).toReal from by
      simpa only [θ,measureReal_def,ENNReal.toReal_mul] using ht).trans
    apply hp.trans_eq
    rw [← Real.rpow_add hR]
    congr 1
    dsimp only [L]
    ring
  have hb (r : ℝ) : ‖charFun θ r‖^2 ≤ R^(4*L) := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) ((norm_charFun_le r).trans hm) 2
    rw [← Real.rpow_mul_natCast hR.le] at hh
    convert hh using 1
    congr 1
    ring
  have hi : IntegrableOn (fun r => ‖charFun θ r‖^2) (Icc (-(2:ℝ)^a) ((2:ℝ)^a)) := by
    simpa only [one_mul,IntegrableOn] using
      PlanarFalconer.charFun_sq_integrable_finite θ
        (volume.restrict (Icc (-(2:ℝ)^a) ((2:ℝ)^a))) 1
  have h := integral_mono hi (integrable_const (R^(4*L))) hb
  rw [integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (neg_le_self (by positivity)))] at h
  have hscale := mul_le_mul_of_nonneg_left h
    (show 0 ≤ R^(4*m ((a:ℝ)/N))/(2:ℝ)^a by positivity)
  apply hscale.trans_eq
  change (R^(4*m ((a:ℝ)/N))/(2:ℝ)^a)*
    (((2:ℝ)^a-(-(2:ℝ)^a))*R^(4*L)) = 2*R^(4*((d:ℝ)+1)*lam)
  calc
    _ = 2*(R^(4*m ((a:ℝ)/N))*R^(4*L)) := by field_simp; ring
    _ = _ := by rw [← Real.rpow_add hR]; congr 2; dsimp only [L]; ring

end Falconer

end OAI
