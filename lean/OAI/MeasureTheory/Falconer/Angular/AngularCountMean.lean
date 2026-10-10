import OAI.MeasureTheory.Falconer.Angular.AngularStripMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def stripHitBound (W : ℝ) (z : Plane) : ℝ≥0∞ :=
  if z=0 then ENNReal.ofReal (2*Real.pi)
  else ENNReal.ofReal (4*Real.pi*min 1 (W/‖z‖))

theorem sourceArcLength_strip_le_bound (z : Plane) {W : ℝ} (hW : 0 ≤ W) :
    sourceArcLength {ω : UnitCircle | |planeDot z (ω:Plane)| ≤ W} ≤ stripHitBound W z := by
  by_cases hz : z=0
  · simp only [stripHitBound,ite_eq_left hz]
    exact (measure_mono (subset_univ _)).trans_eq sourceArcLength_univ
  · simpa only [stripHitBound,ite_eq_right hz] using sourceArcLength_strip z hz hW

theorem stripCount_lintegral {ι : Type*} (S : Finset ι) (v : ι → Plane) (W : ℝ) :
    (∫⁻ ω : UnitCircle, (stripCount S v W (ω:Plane):ℝ≥0∞) ∂sourceArcLength) =
      ∑ i ∈ S, sourceArcLength {ω : UnitCircle | |planeDot (v i) (ω:Plane)| ≤ W} := by
  classical
  let f : ι → UnitCircle → ℝ≥0∞ := fun i =>
    {ω : UnitCircle | |planeDot (v i) (ω:Plane)| ≤ W}.indicator (fun _ => 1)
  have he (ω : UnitCircle) : (stripCount S v W (ω:Plane):ℝ≥0∞) = ∑ i ∈ S, f i ω := by
    rw [stripCount,Finset.card_filter,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : |planeDot (v i) (ω:Plane)| ≤ W <;> simp [hi,f]
  simp_rw [he]
  rw [lintegral_finsetSum S (fun i _ => measurable_const.indicator (measurableSet_directionStrip (v i) W))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_indicator (measurableSet_directionStrip (v i) W)]
  simp

theorem stripCount_mean_bound {ι : Type*} (S : Finset ι) (v : ι → Plane) {W : ℝ} (hW : 0 ≤ W) :
    (∫⁻ ω : UnitCircle, (stripCount S v W (ω:Plane):ℝ≥0∞) ∂sourceArcLength) ≤
      ∑ i ∈ S, stripHitBound W (v i) := by
  rw [stripCount_lintegral]
  exact Finset.sum_le_sum (fun i _ => sourceArcLength_strip_le_bound (v i) hW)

theorem stripCount_exceptional_bound {ι : Type*} (S : Finset ι) (v : ι → Plane)
    {W T : ℝ} (hW : 0 ≤ W) (hT : 0 < T) :
    sourceArcLength {ω : UnitCircle | T < (stripCount S v W (ω:Plane):ℝ)} ≤
      (∑ i ∈ S, stripHitBound W (v i))/ENNReal.ofReal T := by
  have hm : Measurable (fun ω : UnitCircle => (stripCount S v W (ω:Plane):ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
      ((measurable_stripCount S v W).comp continuous_subtype_val.measurable)
  have hsub : {ω : UnitCircle | T < (stripCount S v W (ω:Plane):ℝ)} ⊆
      {ω : UnitCircle | ENNReal.ofReal T ≤ (stripCount S v W (ω:Plane):ℝ≥0∞)} := by
    intro ω hω
    simpa using ENNReal.ofReal_le_ofReal hω.le
  apply (measure_mono hsub).trans
  apply (meas_ge_le_lintegral_div hm.aemeasurable
    (by positivity : ENNReal.ofReal T ≠ 0) ENNReal.ofReal_ne_top).trans
  gcongr
  exact stripCount_mean_bound S v hW

theorem planeDot_quarterTurn (z ω : Plane) :
    planeDot z (quarterTurn ω) = -planeDot (quarterTurn z) ω := by
  simp [planeDot,quarterTurn]

theorem parallelTestCount_as_strip (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) :
    parallelTestCount Q ρ g p P W ω =
      stripCount (parallelTestCells Q ρ g p P)
        (fun c => quarterTurn ((Q.descendant c).center-(Q.descendant P).center)) W ω := by
  classical
  simp only [parallelTestCount,stripCount,planeDot_quarterTurn,abs_neg]

theorem parallelGoodSet_compl_bound (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) {W T : ℝ} (hW : 0 ≤ W) (hT : 0 < T) :
    sourceArcLength (parallelGoodSet Q ρ g p P W T)ᶜ ≤
      (∑ c ∈ parallelTestCells Q ρ g p P,
        stripHitBound W (quarterTurn ((Q.descendant c).center-(Q.descendant P).center)))/
          ENNReal.ofReal T := by
  have he : (parallelGoodSet Q ρ g p P W T)ᶜ =
      {ω : UnitCircle | T < (stripCount (parallelTestCells Q ρ g p P)
        (fun c => quarterTurn ((Q.descendant c).center-(Q.descendant P).center)) W (ω:Plane):ℝ)} := by
    ext ω
    simp [parallelGoodSet,parallelTestCount_as_strip]
  rw [he]
  exact stripCount_exceptional_bound _ _ hW hT

theorem projectionGoodSet_compl_bound (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) {W T : ℝ} (hW : 0 ≤ W) (hT : 0 < T) :
    sourceArcLength (projectionGoodSet Q ρ p u P W T)ᶜ ≤
      (∑ cc ∈ (projectionTestCells Q ρ p u P).product (projectionTestCells Q ρ p u P),
        stripHitBound W ((Q.descendant cc.1).center-(Q.descendant cc.2).center))/
          ENNReal.ofReal T := by
  have he : (projectionGoodSet Q ρ p u P W T)ᶜ =
      {ω : UnitCircle | T < (stripCount
        ((projectionTestCells Q ρ p u P).product (projectionTestCells Q ρ p u P))
        (fun cc => (Q.descendant cc.1).center-(Q.descendant cc.2).center) W (ω:Plane):ℝ)} := by
    ext ω
    simp [projectionGoodSet,projectionTestCount]
  rw [he]
  exact stripCount_exceptional_bound _ _ hW hT

end PlanarFalconer

end OAI
