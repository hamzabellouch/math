import OAI.Geometry.RCD.Sobolev.WeakBallMassBounds

namespace OAI

/-! # Identifying open and closed ball masses from strict-radius bounds -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [BorelSpace Y] in
theorem interior_ball_mass_identification (μ : Measure Y) [IsFiniteMeasure μ]
    (z : Y) (n : ℕ) {S U t : ℝ} (_hS : 0 < S) (ht : 0 < t) (htU : t < U)
    (hbound : ∀ a s b : ℝ, 0 < a → a < s → s < b → b < U →
      (a/S)^n ≤ μ.real (closedBall z s) ∧ μ.real (ball z s) ≤ (b/S)^n) :
    μ.real (ball z t) = (t/S)^n ∧ μ.real (closedBall z t) = (t/S)^n := by
  have hlo (a : ℝ) (ha : 0 < a) (hat : a < t) : (a/S)^n ≤ μ.real (ball z t) := by
    let s := (a+t)/2
    let b := (s+U)/2
    have hs : a < s := by dsimp only [s]; linarith
    have hst : s < t := by dsimp only [s]; linarith
    have hsb : s < b := by dsimp only [b]; linarith
    have hb : b < U := by dsimp only [b]; linarith
    exact (hbound a s b ha hs hsb hb).1.trans
      (measureReal_mono (closedBall_subset_ball hst) (measure_ne_top _ _))
  have hup (b : ℝ) (htb : t < b) (hbU : b < U) : μ.real (closedBall z t) ≤ (b/S)^n := by
    let s := (t+b)/2
    have hs : 0 < s := by dsimp only [s]; linarith
    have hts : t < s := by dsimp only [s]; linarith
    have hsb : s < b := by dsimp only [s]; linarith
    exact (measureReal_mono (closedBall_subset_ball hts) (measure_ne_top _ _)).trans
      (hbound (s/2) s b (by positivity) (by linarith) hsb hbU).2
  let d := fun j : ℕ => 1/((j:ℝ)+1)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdpos j : 0 < d j := by dsimp only [d]; positivity
  have hdle j : d j ≤ 1 := by
    dsimp only [d]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have halim : Tendsto (fun j => t*(1-d j/2)) atTop (𝓝 t) := by
    simpa only [zero_div,sub_zero,mul_one] using
      ((tendsto_const_nhds (x := (1:ℝ))).sub (hd.div_const 2)).const_mul t
  have hblim : Tendsto (fun j => t+(U-t)*d j/2) atTop (𝓝 t) := by
    simpa only [mul_zero,zero_div,add_zero] using
      (tendsto_const_nhds (x := t)).add ((hd.const_mul (U-t)).div_const 2)
  have hlower : (t/S)^n ≤ μ.real (ball z t) := by
    apply le_of_tendsto ((halim.div_const S).pow n)
    exact Eventually.of_forall (fun j => hlo _
      (by nlinarith [hdle j]) (by nlinarith [hdpos j]))
  have hupper : μ.real (closedBall z t) ≤ (t/S)^n := by
    apply ge_of_tendsto ((hblim.div_const S).pow n)
    exact Eventually.of_forall (fun j => hup _
      (by nlinarith [hdpos j]) (by nlinarith [hdle j]))
  have hmono : μ.real (ball z t) ≤ μ.real (closedBall z t) :=
    measureReal_mono ball_subset_closedBall (measure_ne_top _ _)
  exact ⟨le_antisymm (hmono.trans hupper) hlower,
    le_antisymm hupper (hlower.trans hmono)⟩

end RegularPointCoordinates

end

end OAI
