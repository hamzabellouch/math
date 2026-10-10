import OAI.Probability.SLE.Gauge.PrescribedGridLower

namespace OAI

/-! Summable bad-cell mass leaves positive restrictions satisfying every
sufficiently late prescribed-grid bound. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def badGridCells (μ : Measure ℂ) (r H : ℝ) : Set ℂ :=
  ⋃ i : ℤ×ℤ, if ENNReal.ofReal H < μ (closedBall (coverGridCenter r i) (2*r)) then
    closedBall (coverGridCenter r i) (2*r) else ∅

lemma measurableSet_badGridCells (μ : Measure ℂ) (r H : ℝ) :
    MeasurableSet (badGridCells μ r H) := by
  classical
  apply MeasurableSet.iUnion
  intro i
  split_ifs <;> simp only [measurableSet_closedBall,MeasurableSet.empty]

def prescribedBadGrid (μ : Measure ℂ) (κ : ℝ) (W : Target.WienerLaw) (D : ℝ)
    (e : Target.GaugeIndex κ W) : Set ℂ :=
  badGridCells μ (Target.radii κ W e)
    (D*Target.weights κ W e*(Target.radii κ W e)^Target.d κ)

def prescribedGoodGrid (μ : Measure ℂ) (κ : ℝ) (W : Target.WienerLaw) (D : ℝ)
    (N : ℕ) : Set ℂ :=
  ⋂ e : Target.GaugeIndex κ W,
    if N ≤ e.val.1 then (prescribedBadGrid μ κ W D e)ᶜ else univ

lemma measurableSet_prescribedGoodGrid (μ : Measure ℂ) (κ : ℝ)
    (W : Target.WienerLaw) (D : ℝ) (N : ℕ) :
    MeasurableSet (prescribedGoodGrid μ κ W D N) := by
  classical
  apply MeasurableSet.iInter
  intro e
  split_ifs
  · exact (measurableSet_badGridCells _ _ _).compl
  · exact MeasurableSet.univ

lemma ae_mem_prescribedGoodGrid_of_summable
    (μ : Measure ℂ) (κ : ℝ) (W : Target.WienerLaw) (D : ℝ)
    (hsum : (∑' e : Target.GaugeIndex κ W, μ (prescribedBadGrid μ κ W D e)) ≠ ∞) :
    ∀ᵐ x ∂μ, ∃ N : ℕ, x ∈ prescribedGoodGrid μ κ W D N := by
  classical
  filter_upwards [ae_finite_setOfPred_mem hsum] with x hx
  obtain ⟨N,hN⟩ := (hx.image (fun e => e.val.1)).bddAbove
  refine ⟨N+1,mem_iInter.mpr ?_⟩
  intro e
  by_cases he : N+1 ≤ e.val.1
  · rw [ite_eq_left he]
    intro hbad
    have hh := hN (mem_image_of_mem (fun e : Target.GaugeIndex κ W => e.val.1) hbad)
    omega
  · rw [ite_eq_right he]
    trivial

lemma exists_positive_prescribedGoodGrid
    (μ : Measure ℂ) (κ : ℝ) (W : Target.WienerLaw) (D : ℝ)
    (hsum : (∑' e : Target.GaugeIndex κ W, μ (prescribedBadGrid μ κ W D e)) ≠ ∞)
    (E : Set ℂ) (hE : 0 < μ E) :
    ∃ N : ℕ, 0 < μ (E ∩ prescribedGoodGrid μ κ W D N) := by
  by_contra! hn
  have hz : μ (⋃ N : ℕ, E ∩ prescribedGoodGrid μ κ W D N)=0 :=
    measure_iUnion_null (fun N => le_zero_iff.mp (hn N))
  have he : E =ᵐ[μ] ⋃ N : ℕ, E ∩ prescribedGoodGrid μ κ W D N := by
    filter_upwards [ae_mem_prescribedGoodGrid_of_summable μ κ W D hsum] with x hx
    obtain ⟨N,hN⟩ := hx
    apply propext
    constructor
    · intro hEx
      exact mem_iUnion.mpr ⟨N,hEx,hN⟩
    · intro hEx
      obtain ⟨_,hEx,_⟩ := mem_iUnion.mp hEx
      exact hEx
  exact hE.ne' ((measure_congr he).trans hz)

lemma prescribedGoodGrid_cell_bound
    (μ : Measure ℂ) (κ : ℝ) (W : Target.WienerLaw) (D : ℝ) (N : ℕ)
    (e : Target.Entry) (he : Target.ValidEntry κ W e) (hN : N ≤ e.1) (i : ℤ×ℤ) :
    (μ.restrict (prescribedGoodGrid μ κ W D N))
      (closedBall (coverGridCenter (Target.entryRadius κ W e) i) (2*Target.entryRadius κ W e)) ≤
      ENNReal.ofReal (D*Target.entryValue e*(Target.entryRadius κ W e)^Target.d κ) := by
  classical
  let Q := closedBall (coverGridCenter (Target.entryRadius κ W e) i) (2*Target.entryRadius κ W e)
  let H := ENNReal.ofReal (D*Target.entryValue e*(Target.entryRadius κ W e)^Target.d κ)
  change (μ.restrict (prescribedGoodGrid μ κ W D N)) Q ≤ H
  by_cases hbad : H < μ Q
  · have hd : Q ∩ prescribedGoodGrid μ κ W D N=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hxQ,hxG⟩
      have hn := mem_iInter.mp hxG (⟨e,he⟩ : Target.GaugeIndex κ W)
      rw [ite_eq_left hN] at hn
      apply hn
      apply mem_iUnion.mpr
      refine ⟨i,?_⟩
      change x ∈ if H < μ Q then Q else ∅
      rw [ite_eq_left hbad]
      exact hxQ
    rw [Measure.restrict_apply measurableSet_closedBall,hd,measure_empty]
    exact bot_le
  · exact (Measure.restrict_le_self Q).trans (le_of_not_gt hbad)

lemma positive_prescribed_hausdorff_of_summable_bad_mass
    (μ : Measure ℂ) [IsFiniteMeasure μ] (κ : ℝ) (W : Target.WienerLaw)
    (hg : Target.IsHausdorffGauge (Target.gauge κ W))
    (hm1 : 0 < Target.moment κ W 1)
    (hJ : ∀ n : ℕ, 1 ≤ n → Target.moment κ W 1^n ≤ Target.moment κ W n)
    (D : ℝ) (hD : 0 ≤ D)
    (hsum : (∑' e : Target.GaugeIndex κ W, μ (prescribedBadGrid μ κ W D e)) ≠ ∞)
    (E : Set ℂ) (hE : MeasurableSet E) (hpos : 0 < μ E) :
    0 < Target.hausdorff (Target.gauge κ W) E := by
  obtain ⟨N,hN⟩ := exists_positive_prescribedGoodGrid μ κ W D hsum E hpos
  let ν := μ.restrict (prescribedGoodGrid μ κ W D N)
  obtain ⟨C,hC,hbound⟩ := prescribed_grid_mass_distribution ν κ W hg hm1 hJ N D hD
    (prescribedGoodGrid_cell_bound μ κ W D N)
  have hp : 0 < ν E := by
    simpa only [ν,Measure.restrict_apply hE] using hN
  have hb := hbound E
  change ν E ≤ ENNReal.ofReal C*Target.hausdorff (Target.gauge κ W) E at hb
  by_contra! hz
  rw [le_zero_iff.mp hz,mul_zero] at hb
  exact hp.not_ge hb

end SLEExactGauge

end

end OAI
