import OAI.Probability.SLE.Gauge.RibbonConcatenation
import OAI.Probability.SLE.Gauge.RibbonCoordinateLimit
import OAI.Probability.SLE.Gauge.FiniteCoverAssembly
import OAI.Probability.SLE.Mass.StoppedConformalPassageMass

namespace OAI

/-! The actual source middle strips of an embedded ribbon are disjoint,
measurable spatial regions. Their stopped passage masses can therefore be
charged to one whole-trace sausage at the common prescribed mesh. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.RibbonCoordinates

def middleStrip (k ε : ℝ) : Set ℂ :=
  {z | (1 / 3 : ℝ) < z.re - k ∧ z.re - k < 2 / 3 ∧ |z.im| < ε}

theorem middleStrip_open (k ε : ℝ) : IsOpen (middleStrip k ε) :=
  (isOpen_lt continuous_const (Complex.continuous_re.sub continuous_const)).inter
    ((isOpen_lt (Complex.continuous_re.sub continuous_const) continuous_const).inter
      (isOpen_lt Complex.continuous_im.abs continuous_const))

theorem middleStrip_subset_closedRibbon {k ε : ℝ} (hk : 0 ≤ k) (hε : ε ≤ 1) :
    middleStrip k ε ⊆ closedRibbon := by
  intro z hz
  exact ⟨by linarith [hz.1], hz.2.2.le.trans hε⟩

theorem physicalMiddleRegion_eq_image_middleStrip
    (P : ℂ → ℂ) {k ε : ℝ} (hk : 0 ≤ k) (hε : ε ≤ 1) :
    physicalMiddleRegion P closedRibbon k ε = P '' middleStrip k ε := by
  unfold physicalMiddleRegion
  apply congrArg (fun R : Set ℂ => P '' R)
  ext z
  exact ⟨fun hz => hz.2,
    fun hz => ⟨middleStrip_subset_closedRibbon hk hε hz, hz⟩⟩

theorem middleStrip_pairwise_disjoint (ε : ℝ) :
    Pairwise (fun i j : ℕ => Disjoint (middleStrip i ε) (middleStrip j ε)) := by
  intro i j hij
  rw [disjoint_left]
  intro z hi hj
  have hh : (i : ℝ) < (j : ℝ) ∨ (j : ℝ) < (i : ℝ) := by
    exact_mod_cast lt_or_gt_of_ne hij
  rcases hh with hh | hh
  · have hn : i + 1 ≤ j := by exact_mod_cast hh
    have hnR : (i : ℝ) + 1 ≤ j := by exact_mod_cast hn
    linarith [hi.2.1, hj.1]
  · have hn : j + 1 ≤ i := by exact_mod_cast hh
    have hnR : (j : ℝ) + 1 ≤ i := by exact_mod_cast hn
    linarith [hi.1, hj.2.1]

theorem physical_middle_regions_pairwise_disjoint
    (P : ℂ → ℂ) (hiP : InjOn P closedRibbon) {ε : ℝ} (hε : ε ≤ 1) :
    Pairwise (fun i j : ℕ => Disjoint
      (physicalMiddleRegion P closedRibbon i ε) (physicalMiddleRegion P closedRibbon j ε)) := by
  intro i j hij
  rw [physicalMiddleRegion_eq_image_middleStrip P (Nat.cast_nonneg _) hε,
    physicalMiddleRegion_eq_image_middleStrip P (Nat.cast_nonneg _) hε, disjoint_left]
  rintro z ⟨u, hu, he⟩ ⟨v, hv, hve⟩
  have huv : u = v := hiP
    (middleStrip_subset_closedRibbon (Nat.cast_nonneg _) hε hu)
    (middleStrip_subset_closedRibbon (Nat.cast_nonneg _) hε hv) (he.trans hve.symm)
  exact Set.disjoint_left.mp (middleStrip_pairwise_disjoint ε hij) hu (huv ▸ hv)

theorem isOpen_embedded_middle_region
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hiP : InjOn P closedRibbon)
    {k ε : ℝ} (hk : 0 ≤ k) (hε : ε ≤ 1) :
    IsOpen (physicalMiddleRegion P closedRibbon k ε) := by
  rw [physicalMiddleRegion_eq_image_middleStrip P hk hε]
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨u, hu, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (middleStrip_open k ε) u hu
  have hclosed := hball.trans (middleStrip_subset_closedRibbon hk hε)
  exact mem_of_superset
    ((hpublished P u r hr (hP.mono hclosed) (hiP.mono hclosed)).mem_nhds
      (mem_image_of_mem P (mem_ball_self hr))) (image_mono hball)

theorem segmentSausageCharge_le_whole
    (κ : ℝ) (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) (v : ℝ) (R : Set ℂ) :
    segmentSausageCharge κ γ s t v R ≤ wholeSausageCharge κ γ v R := by
  apply mul_le_mul' le_rfl
  apply measure_mono
  rintro z ⟨hz, u, _, hd⟩
  exact ⟨hz, u, by simpa only [dist_comm] using hd⟩

/-- Exactly the source middle strips are counted, even if their sausages
also meet other parts of the curve. Spatial disjointness alone suffices. -/
theorem whole_sausage_charge_from_ribbon_steps
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hiP : InjOn P closedRibbon)
    {ε : ℝ} (hε : ε ≤ 1) (I : Finset ℕ)
    (κ : ℝ) (γ : ℝ≥0 → ℂ) (s t : ℕ → ℝ≥0) (v b : ℝ) (A : Set ℂ)
    (hregions : ∀ i ∈ I, physicalMiddleRegion P closedRibbon i ε ⊆ A)
    (hmass : ∀ i ∈ I, ENNReal.ofReal b ≤
      segmentSausageCharge κ γ (s i) (t i) v (physicalMiddleRegion P closedRibbon i ε)) :
    (I.card : ℝ≥0∞) * ENNReal.ofReal b ≤ wholeSausageCharge κ γ v A := by
  let ν := wholeSausageMeasure κ γ v
  have hmeas i : MeasurableSet (physicalMiddleRegion P closedRibbon (i : ℕ) ε) :=
    (isOpen_embedded_middle_region hpublished P hP hiP (Nat.cast_nonneg _) hε).measurableSet
  calc
    _ = ∑ _i ∈ I, ENNReal.ofReal b := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ I, ν (physicalMiddleRegion P closedRibbon i ε) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [wholeSausageMeasure_apply κ γ v (hmeas i)]
      exact (hmass i hi).trans (segmentSausageCharge_le_whole κ γ (s i) (t i) v _)
    _ = ν (⋃ i ∈ I, physicalMiddleRegion P closedRibbon i ε) :=
      (measure_biUnion_finset
        (fun i _ j _ hij => physical_middle_regions_pairwise_disjoint P hiP hε hij)
        (fun i _ => hmeas i)).symm
    _ ≤ wholeSausageCharge κ γ v A := by
      rw [wholeSausageMeasure_apply κ γ v
        (I.measurableSet_biUnion (fun i _ => hmeas i))]
      apply mul_le_mul' le_rfl
      exact measure_mono (inter_subset_inter (iUnion₂_subset hregions) Subset.rfl)

theorem dense_ribbon_mass_from_steps
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hiP : InjOn P closedRibbon)
    {ε : ℝ} (hε : ε ≤ 1) (I : Finset ℕ)
    (κ : ℝ) (γ : ℝ≥0 → ℂ) (s t : ℕ → ℝ≥0) (v c ell : ℝ)
    (hell : 0 < ell) (m : ℕ) (hm : 0 < m) (hcard : I.card = m ^ 2)
    (A : Set ℂ)
    (hregions : ∀ i ∈ I, physicalMiddleRegion P closedRibbon i ε ⊆ A)
    (hmass : ∀ i ∈ I, ENNReal.ofReal (c * (ell / (m : ℝ)) ^ dimension κ) ≤
      segmentSausageCharge κ γ (s i) (t i) v (physicalMiddleRegion P closedRibbon i ε)) :
    ENNReal.ofReal (c * ell ^ dimension κ * (m : ℝ) ^ codimension κ) ≤
      wholeSausageCharge κ γ v A := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (m : ℝ) ^ 2 * (c * (ell / (m : ℝ)) ^ dimension κ) =
      c * ell ^ dimension κ * (m : ℝ) ^ codimension κ := by
    rw [div_eq_mul_one_div, Real.mul_rpow hell.le (one_div_nonneg.mpr hmR.le)]
    calc
      _ = c * ell ^ dimension κ *
          ((m : ℝ) ^ 2 * (1 / (m : ℝ)) ^ dimension κ) := by ring
      _ = _ := by rw [ribbon_mass_power_cancellation κ hmR]
  have hh := whole_sausage_charge_from_ribbon_steps hpublished P hP hiP hε I κ γ s t v
    (c * (ell / (m : ℝ)) ^ dimension κ) A hregions hmass
  rw [hcard, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    Nat.cast_pow, he] at hh
  exact hh

end SLEExactGauge.RibbonCoordinates

end

end OAI
