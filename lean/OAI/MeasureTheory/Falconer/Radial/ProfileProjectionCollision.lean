import OAI.MeasureTheory.Falconer.Radial.ProjectionCollisionCount
import OAI.MeasureTheory.Falconer.Estimates.ActualRegularizedClasses
import OAI.MeasureTheory.Falconer.Recursion.DescriptorMasks

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem profile_projection_collision (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) {N B p u J i : ℕ} {δ lam sig : ℝ} {m : ℝ → ℝ}
    (hprof : RegularizedProfileData Q ρ N B δ lam m)
    (hpu : p ≤ u) (hu : u ≤ N) {P : CellPath} (hP : P.length = p)
    {ω e : UnitCircle} {w d : ℝ} (hd : dist (ω:Plane) (e:Plane) ≤ d)
    (hgap : w+4/(2:ℝ)^u+(2/(2:ℝ)^p)*d ≤ sourceAngularWidth N sig J i u)
    (hgood : ω ∈ descriptorGoodSet Q ρ m N lam sig J i P (.projection p u)) :
    ((ρ.restrict (Q.descendant P).carrier).prod (ρ.restrict (Q.descendant P).carrier))
      {z : Plane × Plane | |planeDot (z.1-z.2) (e:Plane)| ≤ w} ≤
      (ρ (Q.descendant P).carrier)^2 * ENNReal.ofReal (((2:ℝ)^N)^
        (-(m u-m p)+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+
          2000*(lam+sig)+12*lam)) := by
  have := hprof.probability
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  by_cases hz : ρ (Q.descendant P).carrier = 0
  · simp [Measure.restrict_eq_zero.mpr hz,hz]
  have hpos : 0 < ρ (Q.descendant P).carrier := bot_lt_iff_ne_bot.mpr hz
  let R : ℝ := (2:ℝ)^N
  let k : ℝ := height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u
  have hR : 0 < R := by dsimp [R]; positivity
  let H : ℝ := R^(3*lam)*R^(-m u)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hcount : (projectionTestCount Q ρ p u P (w+4*Q.side/(2:ℝ)^u) (e:Plane):ℝ) ≤
      R^(m u-m p+k+2000*(lam+sig)) := by
    apply le_trans (Nat.cast_le.mpr (projectionTestCount_transfer Q hside ρ p u hP hd ?_)) hgood
    simpa only [hQ,mul_one] using hgap
  have hbound := projection_collision_le_count Q hside ρ hpu hP (by simpa using e.property.le) w
    (H := ENNReal.ofReal H) (fun C hC => by
      have hc := hprof.cells u hu C ((mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hC).1)
        (Finset.mem_filter.mp hC).2.1
      rw [← ENNReal.ofReal_toReal (measure_ne_top ρ _)]
      exact ENNReal.ofReal_le_ofReal hc.2)
  have hcoarse := (hprof.cells p (hpu.trans hu) P hP hpos).1
  have hsq : (R^(-3*lam)*R^(-m p))^2 ≤ (ρ (Q.descendant P).carrier).toReal^2 :=
    pow_le_pow_left₀ (by positivity) hcoarse 2
  have he : R^(m u-m p+k+2000*(lam+sig))*H^2 =
      (R^(-3*lam)*R^(-m p))^2 * R^(-(m u-m p)+k+2000*(lam+sig)+12*lam) := by
    dsimp [H]
    simp only [pow_two,← Real.rpow_add hR]
    congr 1
    ring
  calc
    _ ≤ _ := hbound
    _ ≤ ENNReal.ofReal (R^(m u-m p+k+2000*(lam+sig)))*ENNReal.ofReal H^2 := by
      apply mul_le_mul' _ le_rfl
      have hh := ENNReal.ofReal_le_ofReal hcount
      simpa only [ENNReal.ofReal_natCast] using hh
    _ = ENNReal.ofReal (R^(m u-m p+k+2000*(lam+sig))*H^2) := by
      rw [← ENNReal.ofReal_pow hH,← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
    _ ≤ ENNReal.ofReal ((ρ (Q.descendant P).carrier).toReal^2 *
        R^(-(m u-m p)+k+2000*(lam+sig)+12*lam)) := by
      rw [he]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hsq (by positivity))
    _ = _ := by
      rw [ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_pow ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top ρ _)]

end PlanarFalconer

end OAI
