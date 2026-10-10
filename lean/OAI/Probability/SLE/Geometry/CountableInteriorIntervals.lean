import OAI.Probability.SLE.Gauge.CoverEvents
import Mathlib.Topology.Compactness.SigmaCompact

namespace OAI

/-! The deterministic countable certificates for the retained middle-strip
intervals. An actual open interior visit contains a nondegenerate rational
time interval, whose image lies in one fixed countable compact exhaustion. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace SLEExactGauge

theorem exists_countable_compact_exhaustion_open (O : Set ℂ) (hO : IsOpen O) :
    ∃ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ O) ∧
      (∀ S : Set ℂ, IsCompact S → S ⊆ O → ∃ n, S ⊆ K n) := by
  let : LocallyCompactSpace O := hO.locallyCompactSpace
  let L := CompactExhaustion.choice O
  refine ⟨fun n => Subtype.val '' L n, ?_, ?_, ?_⟩
  · intro n
    exact (L.isCompact n).image continuous_subtype_val
  · rintro n z ⟨w, _, rfl⟩
    exact w.property
  · intro S hS hSO
    have hpre : IsCompact ((Subtype.val : O → ℂ) ⁻¹' S) :=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
        hS (by simpa only [Subtype.range_coe] using hSO)
    obtain ⟨n, hn⟩ := L.exists_superset_of_isCompact hpre
    refine ⟨n, ?_⟩
    intro z hz
    exact ⟨⟨z, hSO hz⟩, hn hz, rfl⟩

theorem exists_rational_interval_in_open_visit
    (f : ℝ → ℂ) (hf : Continuous f) (O : Set ℂ) (hO : IsOpen O)
    (a b : ℝ) (hvisit : ∃ u ∈ Ioo a b, f u ∈ O) :
    ∃ s t : ℚ, a < (s : ℝ) ∧ (s : ℝ) < t ∧ (t : ℝ) < b ∧
      MapsTo f (Icc (s : ℝ) t) O := by
  have hU : IsOpen (Ioo a b ∩ f ⁻¹' O) := isOpen_Ioo.inter (hO.preimage hf)
  have hUn : (Ioo a b ∩ f ⁻¹' O).Nonempty := by
    obtain ⟨u, hu, hfu⟩ := hvisit
    exact ⟨u, hu, hfu⟩
  obtain ⟨l, r, hlr, hsub⟩ := hU.exists_Ioo_subset hUn
  obtain ⟨s, hls, hsr⟩ := exists_rat_btwn hlr
  obtain ⟨t, hst, htr⟩ := exists_rat_btwn hsr
  refine ⟨s, t, (hsub ⟨hls, hsr⟩).1.1, hst,
    (hsub ⟨hls.trans hst, htr⟩).1.2, ?_⟩
  intro u hu
  exact (hsub ⟨hls.trans_le hu.1, hu.2.trans_lt htr⟩).2

/-- One countable compact family captures every open visit, at rational
times strictly between the entry and the later crossing. -/
theorem rational_interval_compact_certificate
    (O : Set ℂ) (hO : IsOpen O) :
    ∃ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ O) ∧
      ∀ (f : ℝ → ℂ), Continuous f → ∀ a b : ℝ,
        (∃ u ∈ Ioo a b, f u ∈ O) →
        ∃ (s t : ℚ) (n : ℕ), a < (s : ℝ) ∧ (s : ℝ) < t ∧
          (t : ℝ) < b ∧ f '' Icc (s : ℝ) t ⊆ K n := by
  obtain ⟨K, hK, hKO, hcap⟩ := exists_countable_compact_exhaustion_open O hO
  refine ⟨K, hK, hKO, ?_⟩
  intro f hf a b hvisit
  obtain ⟨s, t, has, hst, htb, hmap⟩ :=
    exists_rational_interval_in_open_visit f hf O hO a b hvisit
  obtain ⟨n, hn⟩ := hcap (f '' Icc (s : ℝ) t)
    (isCompact_Icc.image hf) hmap.image_subset
  exact ⟨s, t, n, has, hst, htb, hn⟩

local instance compactIntervalPathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance compactIntervalPathBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem isClosed_interval_compact_certificate (s t : ℝ≥0)
    {K : Set ℂ} (hK : IsClosed K) :
    IsClosed {f : C(ℝ≥0, ℂ) | MapsTo f (Icc s t) K} := by
  have he : {f : C(ℝ≥0, ℂ) | MapsTo f (Icc s t) K} =
      ⋂ u ∈ Icc s t, (fun f : C(ℝ≥0, ℂ) => f u) ⁻¹' K := by
    ext f
    simp only [mem_ofPred_eq, MapsTo, mem_iInter, mem_preimage]
  rw [he]
  exact isClosed_iInter (fun u => isClosed_iInter (fun _ =>
    hK.preimage (continuous_eval_const u)))

theorem measurableSet_interval_compact_certificate
    {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (s t : ℝ≥0) {K : Set ℂ} (hK : IsCompact K) :
    MeasurableSet {ω | MapsTo (f ω) (Icc s t) K} :=
  hf (isClosed_interval_compact_certificate s t hK.isClosed).measurableSet

end SLEExactGauge

end

end OAI
