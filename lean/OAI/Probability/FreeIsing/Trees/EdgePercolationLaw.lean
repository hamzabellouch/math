import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.EdgePercolationLaw

def edgeInterval (theta : ℝ) (openEdge : Bool) : Set ℝ :=
  if openEdge then Set.Iic theta else Set.Ioi theta

theorem measurableSet_edgeInterval (theta : ℝ) (b : Bool) :
    MeasurableSet (edgeInterval theta b) := by
  cases b <;> simp [edgeInterval]

theorem uniform01_Iic {theta : ℝ} (h1 : theta ≤ 1) :
    uniform01 (Set.Iic theta) = ENNReal.ofReal theta := by
  rw [uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic theta ∩ Set.Icc 0 1 = Set.Icc 0 theta := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun hx => ⟨hx.2.1, hx.1⟩,
      fun hx => ⟨hx.2, hx.1, hx.2.trans h1⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

theorem uniform01_Ioi {theta : ℝ} (h0 : 0 ≤ theta) :
    uniform01 (Set.Ioi theta) = ENNReal.ofReal (1 - theta) := by
  rw [uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi theta ∩ Set.Icc 0 1 = Set.Ioc theta 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩,
      fun hx => ⟨hx.1, h0.trans hx.1.le, hx.2⟩⟩
  rw [h, Real.volume_Ioc]

theorem uniform01_edgeInterval {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (b : Bool) :
    uniform01 (edgeInterval theta b) =
      if b then ENNReal.ofReal theta else ENNReal.ofReal (1 - theta) := by
  cases b
  · exact uniform01_Ioi h0
  · exact uniform01_Iic h1

def cylinder {E : Type*} (theta : ℝ) (D : Finset E) (status : E → Bool) :
    Set (E → ℝ) :=
  Set.pi (D : Set E) (fun e => edgeInterval theta (status e))

theorem measurableSet_cylinder {E : Type*} (theta : ℝ) (D : Finset E)
    (status : E → Bool) : MeasurableSet (cylinder theta D status) :=
  MeasurableSet.pi D.countable_toSet fun e _ => measurableSet_edgeInterval theta (status e)

theorem infinitePi_cylinder {E : Type*} {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (D : Finset E) (status : E → Bool) :
    Measure.infinitePi (fun _ : E => uniform01) (cylinder theta D status) =
      ∏ e ∈ D, if status e then ENNReal.ofReal theta else ENNReal.ofReal (1 - theta) := by
  classical
  rw [cylinder, Measure.infinitePi_pi _ (fun e _ => measurableSet_edgeInterval theta (status e))]
  exact Finset.prod_congr rfl fun e _ => uniform01_edgeInterval h0 h1 (status e)

theorem infinitePi_all_open {E : Type*} {theta : ℝ}
    (h1 : theta ≤ 1) (D : Finset E) :
    Measure.infinitePi (fun _ : E => uniform01) {U | ∀ e ∈ D, U e ≤ theta} =
      ENNReal.ofReal theta ^ D.card := by
  classical
  change Measure.infinitePi (fun _ : E => uniform01)
    (Set.pi (D : Set E) (fun _ => Set.Iic theta)) = _
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_Iic)]
  simp only [uniform01_Iic h1, Finset.prod_const]

theorem cylinder_of_measurePreserving {Ω E : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U : Ω → E → ℝ}
    (hU : MeasurePreserving U μ (Measure.infinitePi (fun _ : E => uniform01)))
    {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (D : Finset E) (status : E → Bool) :
    μ {ω | ∀ e ∈ D, U ω e ∈ edgeInterval theta (status e)} =
      ∏ e ∈ D, if status e then ENNReal.ofReal theta else ENNReal.ofReal (1 - theta) := by
  rw [← infinitePi_cylinder h0 h1 D status]
  exact hU.measure_preimage (measurableSet_cylinder theta D status).nullMeasurableSet

theorem all_open_of_measurePreserving {Ω E : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U : Ω → E → ℝ}
    (hU : MeasurePreserving U μ (Measure.infinitePi (fun _ : E => uniform01)))
    {theta : ℝ} (h1 : theta ≤ 1) (D : Finset E) :
    μ {ω | ∀ e ∈ D, U ω e ≤ theta} = ENNReal.ofReal theta ^ D.card := by
  rw [← infinitePi_all_open h1 D]
  exact hU.measure_preimage
    (MeasurableSet.pi D.countable_toSet (fun _ _ => measurableSet_Iic)).nullMeasurableSet

theorem joint_cylinder_of_measurePreserving {Ω A E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    {μ : Measure Ω} {ν : Measure A} [SFinite ν]
    {env : Ω → A} {U : Ω → E → ℝ}
    (hU : MeasurePreserving (fun ω => (env ω, U ω)) μ
      (ν.prod (Measure.infinitePi (fun _ : E => uniform01))))
    {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (B : Set A) (hB : MeasurableSet B) (D : Finset E) (status : E → Bool) :
    μ {ω | env ω ∈ B ∧ ∀ e ∈ D, U ω e ∈ edgeInterval theta (status e)} =
      ν B * ∏ e ∈ D, if status e then ENNReal.ofReal theta else ENNReal.ofReal (1 - theta) := by
  change μ ((fun ω => (env ω, U ω)) ⁻¹' (B ×ˢ cylinder theta D status)) = _
  rw [hU.measure_preimage (hB.prod (measurableSet_cylinder theta D status)).nullMeasurableSet,
    Measure.prod_prod, infinitePi_cylinder h0 h1]

end Problem367.EdgePercolationLaw

end

end OAI
