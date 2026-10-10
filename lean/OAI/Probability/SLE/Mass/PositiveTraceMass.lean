import OAI.Probability.SLE.Mass.PositiveRestartMass
import OAI.Probability.SLE.Mass.CanonicalMassScaling

namespace OAI

/-! Positive increments and trace support force positive canonical mass
in each open set visited at a positive time. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

lemma positive_trace_mass_of_positive_increments
    (γ : ℝ≥0 → ℂ) (hγ : Continuous γ) (N : ℝ≥0 → Measure upperHalfPlane)
    (hmono : Monotone N)
    (hinc : ∀ s t, s ≤ t → (N t-N s)
      {z : upperHalfPlane | (z:ℂ) ∉ (fun r : ℝ => γ r.toNNReal) '' Icc (s:ℝ) t}=0)
    (hpos : ∀ s t, s < t → N t-N s ≠ 0)
    (V : Set ℂ) (hV : IsOpen V) (u T : ℝ≥0) (hu : 0 < u) (huT : u ≤ T)
    (hvisit : γ u ∈ V) : 0 < N T (Subtype.val ⁻¹' V) := by
  have hpre : γ ⁻¹' V ∈ 𝓝 u := hγ.continuousAt.preimage_mem_nhds (hV.mem_nhds hvisit)
  obtain ⟨a,ha,haV⟩ := exists_Ioc_subset_of_mem_nhds' hpre hu
  obtain ⟨b,hab,hbu⟩ := exists_between ha.2
  have hseg : (fun r : ℝ => γ r.toNNReal) '' Icc (b:ℝ) u ⊆ V := by
    rintro _ ⟨r,hr,rfl⟩
    apply haV
    have hbr : b ≤ r.toNNReal := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_mono hr.1
    have hru : r.toNNReal ≤ u := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_mono hr.2
    exact ⟨hab.trans_le hbr,hru⟩
  have hnull : (N u-N b) (Subtype.val ⁻¹' V)ᶜ=0 := by
    apply le_antisymm ?_ bot_le
    apply (measure_mono (show (Subtype.val ⁻¹' V)ᶜ ⊆
      {z : upperHalfPlane | (z:ℂ) ∉ (fun r : ℝ => γ r.toNNReal) '' Icc (b:ℝ) u} from ?_)).trans_eq
      (hinc b u hbu.le)
    intro z hz hs
    exact hz (hseg hs)
  have hVmeas : MeasurableSet ((Subtype.val : upperHalfPlane → ℂ) ⁻¹' V) :=
    (hV.preimage (continuous_subtype_val : Continuous (Subtype.val : upperHalfPlane → ℂ))).measurableSet
  have he := measure_add_measure_compl (μ:=N u-N b) hVmeas
  rw [hnull,add_zero] at he
  have hp : 0 < (N u-N b) (Subtype.val ⁻¹' V) := by
    rw [he]
    exact Measure.measure_univ_pos.mpr (hpos b u hbu)
  exact hp.trans_le (((Measure.sub_le : N u-N b ≤ N u).trans (hmono huT)) _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}

lemma CanonicalMass.positive_open_visited
    (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0) (hκ : 0 < κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t)) :
    ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → ∀ u T : ℝ≥0,
      0 < u → u ≤ T → γ ω u ∈ V → 0 < C.process T ω (Subtype.val ⁻¹' V) := by
  have hp := C.positive_all_times hB hc h0 F hw
  have hi := C.positive_increment_all_times hB hc hκ F hw hpublished hp
  filter_upwards [C.paths,hi] with ω hω hωi
  exact positive_trace_mass_of_positive_increments (γ ω) (hw ω).1 (fun t => C.process t ω)
    hω.monotone hω.increment_support hωi

end SLEExactGauge.Multipoint

end

end OAI
