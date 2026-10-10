import OAI.GroupTheory.PolycyclicRecognition.Analysis.FixedSlicePacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasedImagePaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeCellVolume

namespace OAI

/-! # Separated source counts for the retained probe volume -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped ENNReal NNReal

variable {N D G : Type*} [Group N] [Group D] [Group G]
  [TopologicalSpace N] [MeasurableSpace N] [MeasurableMul N]
  [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
  (μ : Measure N) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
  (hι : Topology.IsClosedEmbedding ι)
  (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
  (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)

include hι hφ hconj

/-- Positive probe volume supplies genuinely separated image endpoints.
The constant is independent of the source sheet, its Cartan pivot, the
normalized map and the point at which its image is centered. -/
theorem exists_fixedSlice_image_net_constant
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : NormalizedPair G Λ) (x a : G) (d : D)
      (S : Set N), IsCompact S →
      ∃ t : Finset G,
        (↑t : Set G) ⊆ (fun n => basedImage p.val.1 a (x * ι n * κ d)) '' S ∧
        (∀ u ∈ t, ∀ v ∈ t, u ≠ v → 1 ≤ dist u v) ∧
        c * (μ S).toReal ≤ (t.card : ℝ) := by
  classical
  let ρ := (Λ : ℝ) * ((Λ : ℝ) + 1)
  have hρ : 0 < ρ := mul_pos hΛ (by positivity)
  let C := μ (ι ⁻¹' closedBall (1 : G) ρ)
  have hC : C ≠ ⊤ := (fixedSlice_packing_constant_lt_top ι μ hι ρ).ne
  let c := 1 / (C.toReal + 1)
  have hden : 0 < C.toReal + 1 := by positivity
  refine ⟨c, div_pos zero_lt_one hden, ?_⟩
  intro p x a d S hS
  obtain ⟨s, hs, hsep, hmass⟩ := exists_fixedSlice_separated_net_of_compact
    ι κ φ μ hφ hconj hι.continuous x d hS (Subset.refl S) hρ
  obtain ⟨hcard, hsep'⟩ := basedImage_separated_card p hΛ a s hsep
  refine ⟨s.image (basedImage p.val.1 a), ?_, hsep', ?_⟩
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨n, hn, rfl⟩ := hs hv
    exact ⟨n, hn, rfl⟩
  · have hm := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hC) hmass
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hm
    rw [hcard]
    have hm' : (μ S).toReal ≤ (s.card : ℝ) * (C.toReal + 1) := by
      calc
        _ ≤ (s.card : ℝ) * C.toReal := hm
        _ ≤ (s.card : ℝ) * (C.toReal + 1) := by gcongr; linarith
    dsimp only [c]
    calc
      (1 / (C.toReal + 1)) * (μ S).toReal = (μ S).toReal / (C.toReal + 1) := by ring
      _ ≤ (s.card : ℝ) := (div_le_iff₀ hden).mpr hm'

/-- Apply the uniform fixed-slice count directly to a compact set retained
from the original uniform probe distribution. Its probability loss becomes
only a fixed multiplicative constant in the separated count. -/
theorem exists_fixedSlice_probe_net_constant
    {P : Type*} [TopologicalSpace P] [MeasurableSpace P]
    (ν : Measure P) (e : P → N) (he : MeasurableEmbedding e) (hec : Continuous e)
    (hμ : μ = Measure.map e ν) {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : NormalizedPair G Λ) (x a : G) (d : D)
      (A K : Set P) (hA0 : ν A ≠ 0) (hAt : ν A ≠ ⊤),
      IsCompact K → MeasurableSet K → K ⊆ A →
      ∀ q : ℝ, 0 ≤ q →
      ENNReal.ofReal q ≤ (cellProbabilityMeasure ν A hA0 hAt : Measure P) K →
      ∃ t : Finset G,
        (↑t : Set G) ⊆ (fun y => basedImage p.val.1 a (x * ι (e y) * κ d)) '' K ∧
        (∀ u ∈ t, ∀ v ∈ t, u ≠ v → 1 ≤ dist u v) ∧
        (c * q) * (ν A).toReal ≤ (t.card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := exists_fixedSlice_image_net_constant
    ι κ φ μ hι hφ hconj hΛ
  refine ⟨c, hc, ?_⟩
  intro p x a d A K hA0 hAt hK hKm hKA q hq hmass
  obtain ⟨t, ht, hsep, hcard⟩ := hcount p x a d (e '' K) (hK.image hec)
  have hvol := probe_cell_image_volume_lower ν e he A K hA0 hAt hKm hKA hq hmass
  rw [← hμ] at hvol
  refine ⟨t, ?_, hsep, ?_⟩
  · simpa only [image_image, Function.comp_def] using ht
  · calc
      (c * q) * (ν A).toReal = c * (q * (ν A).toReal) := by ring
      _ ≤ c * (μ (e '' K)).toReal := mul_le_mul_of_nonneg_left hvol hc.le
      _ ≤ (t.card : ℝ) := hcard

/-- A quarter of the original probe cell yields the full source exponent,
uniformly over a sequence of maps, centers and moving Cartan pivots. -/
theorem exists_probe_source_count_sequence
    {P : Type*} [TopologicalSpace P] [MeasurableSpace P]
    (ν : Measure P) (e : ℕ → P → N)
    (he : ∀ n, MeasurableEmbedding (e n)) (hec : ∀ n, Continuous (e n))
    (hμ : ∀ n, μ = Measure.map (e n) ν)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (x a : ℕ → G) (d : ℕ → D) (A K : ℕ → Set P)
    (hA0 : ∀ n, ν (A n) ≠ 0) (hAt : ∀ n, ν (A n) ≠ ⊤)
    (hK : ∀ n, IsCompact (K n)) (hKm : ∀ n, MeasurableSet (K n))
    (hKA : ∀ n, K n ⊆ A n)
    (hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellProbabilityMeasure ν (A n) (hA0 n) (hAt n) : Measure P) (K n))
    (scale : ℕ → ℝ) (P₁ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (ν (A n)).toReal) :
    ∃ (c : ℝ) (source : ℕ → Finset G), 0 < c ∧
      (∀ n, (↑(source n) : Set G) ⊆
        (fun y => basedImage (p n).val.1 (a n) (x n * ι (e n y) * κ (d n))) '' K n) ∧
      (∀ n, ∀ u ∈ source n, ∀ w ∈ source n, u ≠ w → 1 ≤ dist u w) ∧
      ∀ n, c * Real.exp (scale n * P₁) ≤ ((source n).card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := exists_fixedSlice_image_net_constant
    ι κ φ μ hι hφ hconj hΛ
  have ht (n : ℕ) : ∃ t : Finset G,
      (↑t : Set G) ⊆
        (fun y => basedImage (p n).val.1 (a n) (x n * ι (e n y) * κ (d n))) '' K n ∧
      (∀ u ∈ t, ∀ w ∈ t, u ≠ w → 1 ≤ dist u w) ∧
      (c * v / 4) * Real.exp (scale n * P₁) ≤ (t.card : ℝ) := by
    obtain ⟨t, ht, hsep, hcard⟩ := hcount (p n) (x n) (a n) (d n)
      (e n '' K n) ((hK n).image (hec n))
    have hm := probe_cell_image_volume_lower ν (e n) (he n) (A n) (K n)
      (hA0 n) (hAt n) (hKm n) (hKA n) (by norm_num : (0 : ℝ) ≤ 1 / 4) (hmass n)
    rw [← hμ n] at hm
    refine ⟨t, ?_, hsep, ?_⟩
    · simpa only [image_image, Function.comp_def] using ht
    · calc
        (c * v / 4) * Real.exp (scale n * P₁) =
            c * ((1 / 4) * (v * Real.exp (scale n * P₁))) := by ring
        _ ≤ c * ((1 / 4) * (ν (A n)).toReal) := by gcongr; exact hvol n
        _ ≤ c * (μ (e n '' K n)).toReal := mul_le_mul_of_nonneg_left hm hc.le
        _ ≤ (t.card : ℝ) := hcard
  choose source hsub hsep hcount using ht
  exact ⟨c * v / 4, source, by positivity, hsub, hsep, hcount⟩

end PolycyclicRecognition

end

end OAI
