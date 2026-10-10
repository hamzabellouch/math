import OAI.Geometry.RCD.Heat.HeatGeneratorTimeContinuity

namespace OAI

/-! # Joint time data for a positive scaled logarithmic heat flow -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ Q ker)

theorem scaled_positive_heat_log_continuous (f : Lp ℝ 2 μ) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ t, 0 < t → ∀ x, 0 < kernelHeat μ Q hk t f x) :
    ContinuousOn (fun q : ℝ × X => ε * Real.log (kernelHeat μ Q hk (ε*q.1/2) f q.2))
      (Ioi 0 ×ˢ univ) := by
  let T := fun q : ℝ × X => (ε*q.1/2,q.2)
  have hT : Continuous T := (continuous_const.mul continuous_fst |>.div_const 2).prodMk continuous_snd
  have hTpos : MapsTo T (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := by
    intro q hq
    exact ⟨div_pos (mul_pos hε hq.1) (by norm_num),mem_univ _⟩
  have hp : ∀ q ∈ Ioi (0:ℝ) ×ˢ (univ : Set X), kernelHeat μ Q hk q.1 f q.2 ≠ 0 :=
    fun q hq => (hpos q.1 hq.1 q.2).ne'
  have hh := ((kernelHeat_continuousOn_time_space μ Q hk f).log hp).comp hT.continuousOn hTpos
  have hm := hh.const_mul ε
  dsimp only [Function.comp_def,T] at hm
  exact hm

theorem scaled_positive_heat_source_continuous (f : Lp ℝ 2 μ) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ t, 0 < t → ∀ x, 0 < kernelHeat μ Q hk t f x) :
    ContinuousOn (fun q : ℝ × X => ε*(ε/2) *
      (kernelHeatGeneratorSource μ Q hk (ε*q.1/2) f q.2 / kernelHeat μ Q hk (ε*q.1/2) f q.2))
      (Ioi 0 ×ˢ univ) := by
  let T := fun q : ℝ × X => (ε*q.1/2,q.2)
  have hT : Continuous T := (continuous_const.mul continuous_fst |>.div_const 2).prodMk continuous_snd
  have hTpos : MapsTo T (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := by
    intro q hq
    exact ⟨div_pos (mul_pos hε hq.1) (by norm_num),mem_univ _⟩
  have hp : ∀ q ∈ Ioi (0:ℝ) ×ˢ (univ : Set X), kernelHeat μ Q hk q.1 f q.2 ≠ 0 :=
    fun q hq => (hpos q.1 hq.1 q.2).ne'
  have hh := (kernelHeat_log_derivative_continuousOn μ Q hk f (Subset.refl _) hp).comp
    hT.continuousOn hTpos
  have hm := hh.const_mul (ε*(ε/2))
  dsimp only [Function.comp_def,T] at hm
  exact hm

theorem scaled_positive_heat_log_hasDerivAt (f : Lp ℝ 2 μ) {ε t : ℝ}
    (hε : 0 < ε) (ht : 0 < t) (x : X) (hpos : 0 < kernelHeat μ Q hk (ε*t/2) f x) :
    HasDerivAt (fun s => ε * Real.log (kernelHeat μ Q hk (ε*s/2) f x))
      (ε*(ε/2) *
        (kernelHeatGeneratorSource μ Q hk (ε*t/2) f x / kernelHeat μ Q hk (ε*t/2) f x)) t := by
  have ht' : 0 < ε*t/2 := div_pos (mul_pos hε ht) (by norm_num)
  have hlin : HasDerivAt (fun s : ℝ => ε*s/2) (ε/2) t := by
    simpa only [mul_one,id_eq] using ((hasDerivAt_id t).const_mul ε).div_const 2
  have hh := (((kernelHeat_generator_hasDerivAt μ Q hk f ht' x).log hpos.ne').comp t hlin).const_mul ε
  convert hh using 1
  · rfl
  · ring

theorem scaled_positive_heat_log_time_data (f : Lp ℝ 2 μ) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ t, 0 < t → ∀ x, 0 < kernelHeat μ Q hk t f x) :
    let H := fun t x => ε * Real.log (kernelHeat μ Q hk (ε*t/2) f x)
    let D := fun t x => ε*(ε/2) *
      (kernelHeatGeneratorSource μ Q hk (ε*t/2) f x / kernelHeat μ Q hk (ε*t/2) f x)
    ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ univ) ∧
      ContinuousOn (Function.uncurry D) (Ioi 0 ×ˢ univ) ∧
      ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => H s x) (D t x) t := by
  exact ⟨scaled_positive_heat_log_continuous μ Q hk f hε hpos,
    scaled_positive_heat_source_continuous μ Q hk f hε hpos,
    fun t ht x => scaled_positive_heat_log_hasDerivAt μ Q hk f hε ht x
      (hpos _ (div_pos (mul_pos hε ht) (by norm_num)) x)⟩

end RegularPointCoordinates

end

end OAI
