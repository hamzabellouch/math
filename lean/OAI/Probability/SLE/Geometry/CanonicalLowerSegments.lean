import OAI.Probability.SLE.Gauge.CanonicalGridLower
import OAI.Probability.SLE.Mass.PositiveTraceMass

namespace OAI

/-! Compact lower bounds give positivity simultaneously on every trace segment.
Only a countable compact exhaustion is used before choosing the time interval. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma exists_compact_covering_positive_inter (μ : Measure upperHalfPlane)
    (A : Set upperHalfPlane) (hA : 0 < μ A) :
    ∃ n : ℕ, 0 < μ (compactCovering upperHalfPlane n ∩ A) := by
  by_contra! hn
  have he : (⋃ n : ℕ, compactCovering upperHalfPlane n ∩ A) = A := by
    rw [← iUnion_inter,iUnion_compactCovering,univ_inter]
  have hz : μ A = 0 := by
    apply le_antisymm ?_ bot_le
    rw [← he]
    calc
      _ ≤ ∑' n : ℕ, μ (compactCovering upperHalfPlane n ∩ A) := measure_iUnion_le _
      _ = 0 := by simp only [fun n => le_zero_iff.mp (hn n),tsum_zero]
  exact hA.ne' hz

namespace CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
  (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω = 0)
  (hκ : 0 < κ) (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
  (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))

include C hB hc h0 hκ F hw hpublished

/-- A countable compact lower criterion and the proved positivity of every
canonical increment imply the required simultaneous segment lower bound. -/
theorem positive_all_segments_of_compact_lower (h : ℝ → ℝ)
    (hlower : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ E : Set ℂ, MeasurableSet E →
      0 < C.rational.terminal ω (compactCovering upperHalfPlane n ∩ Subtype.val ⁻¹' E) →
      0 < Target.hausdorff h E) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < t →
      0 < Target.hausdorff h (γ ω '' Icc s t) := by
  have hp := C.positive_all_times hB hc h0 F hw
  have hi := C.positive_increment_all_times hB hc hκ F hw hpublished hp
  filter_upwards [ae_all_iff.mpr hlower,C.paths,hi] with ω hω hpath hinc
  intro s t hst
  let E := γ ω '' Icc s t
  have hE : MeasurableSet E := (isCompact_Icc.image (hw ω).1).measurableSet
  let A : Set upperHalfPlane := Subtype.val ⁻¹' E
  have hA : MeasurableSet A := hE.preimage measurable_subtype_coe
  have hsupp : (C.process t ω-C.process s ω) Aᶜ = 0 := by
    have hh := hpath.increment_support s t hst.le
    have he : (fun r : ℝ => γ ω r.toNNReal) '' Icc (s:ℝ) t = E := by
      ext z
      constructor
      · rintro ⟨r,hr,rfl⟩
        exact ⟨r.toNNReal,⟨by simpa using Real.toNNReal_mono hr.1,
          by simpa using Real.toNNReal_mono hr.2⟩,rfl⟩
      · rintro ⟨r,hr,rfl⟩
        exact ⟨r,⟨by exact_mod_cast hr.1,by exact_mod_cast hr.2⟩,by simp⟩
    change (C.process t ω-C.process s ω) {z : upperHalfPlane | (z:ℂ) ∉ E} = 0
    rw [he] at hh
    exact hh
  have hpos : 0 < (C.process t ω-C.process s ω) A := by
    have he := measure_add_measure_compl (μ := C.process t ω-C.process s ω) hA
    rw [hsupp,add_zero] at he
    rw [he]
    exact Measure.measure_univ_pos.mpr (hinc s t hst)
  have hterminal : 0 < C.rational.terminal ω A :=
    hpos.trans_le ((Measure.sub_le.trans (hpath.dominated t)) A)
  obtain ⟨n,hn⟩ := exists_compact_covering_positive_inter (C.rational.terminal ω) A hterminal
  exact hω n E hE hn

end CanonicalMass
end SLEExactGauge.Multipoint

end

end OAI
