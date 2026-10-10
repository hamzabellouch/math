import OAI.Probability.InvariantIsing.Spectral.PositiveSpectralLabels
import OAI.Probability.InvariantIsing.Spectral.SpectralPartitionLaw
import Mathlib.MeasureTheory.Measure.Support

namespace OAI

/-! Positive-mass cells carry the same spectral law as the original partition. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Classical BigOperators Function

namespace InvariantIsing

lemma ae_spectralPartitionIndex_pos {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) :
    ∀ᵐ x ∂μ, 0 < μ.real (S (spectralPartitionIndex S hcover x)) := by
  have hi (i : ι) : ∀ᵐ x ∂μ, x∈S i → 0 < μ.real (S i) := by
    by_cases hp : 0 < μ.real (S i)
    · exact Filter.Eventually.of_forall (fun _ _ => hp)
    · have hz : μ (S i)=0 := (measureReal_eq_zero_iff).mp
        (le_antisymm (le_of_not_gt hp) measureReal_nonneg)
      filter_upwards [compl_mem_ae_iff.mpr hz] with x hx
      exact fun h => (hx h).elim
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact hx _ (spectralPartitionIndex_mem S hcover x)

lemma positive_spectral_partition_map {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S))
    (hS : ∀ i, MeasurableSet (S i)) (lam : ι → ℝ)
    (fallback : {i // 0 < μ.real (S i)}) :
    μ.map (fun x => lam (positiveSpectralLabel (fun i => μ.real (S i)) fallback
      (spectralPartitionIndex S hcover x)))=
      finiteSpectralMeasure (fun i : {i // 0 < μ.real (S i)} => μ.real (S i))
        (fun i => lam i) := by
  have he : (fun x => lam (positiveSpectralLabel (fun i => μ.real (S i)) fallback
      (spectralPartitionIndex S hcover x))) =ᵐ[μ]
        (fun x => lam (spectralPartitionIndex S hcover x)) := by
    filter_upwards [ae_spectralPartitionIndex_pos μ S hcover] with x hx
    simp only [positiveSpectralLabel,dite_eq_left hx]
  rw [Measure.map_congr he,spectralPartition_pushforward μ S hcover hdis hS lam,
    finiteSpectralMeasure_positive _ _ (fun _ => measureReal_nonneg)]

lemma positive_spectral_edge_bounds {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (lam : ι → ℝ) (δ a b : ℝ)
    (ha : a∈μ.support) (hb : b∈μ.support)
    (aMin aMax : {i // 0 < μ.real (S i)})
    (hmin : ∀ i : {i // 0 < μ.real (S i)}, lam aMin ≤ lam i)
    (hmax : ∀ i : {i // 0 < μ.real (S i)}, lam i ≤ lam aMax)
    (hclose : ∀ᵐ x ∂μ, dist (lam (spectralPartitionIndex S hcover x)) x ≤ δ) :
    lam aMin-δ ≤ a ∧ b ≤ lam aMax+δ := by
  have hl : ∀ᵐ x ∂μ, x∈Ici (lam aMin-δ) := by
    filter_upwards [ae_spectralPartitionIndex_pos μ S hcover,hclose] with x hx hc
    have hh := hmin ⟨spectralPartitionIndex S hcover x,hx⟩
    rw [Real.dist_eq,abs_le] at hc
    change lam aMin-δ ≤ x
    linarith
  have hu : ∀ᵐ x ∂μ, x∈Iic (lam aMax+δ) := by
    filter_upwards [ae_spectralPartitionIndex_pos μ S hcover,hclose] with x hx hc
    have hh := hmax ⟨spectralPartitionIndex S hcover x,hx⟩
    rw [Real.dist_eq,abs_le] at hc
    change x ≤ lam aMax+δ
    linarith
  exact ⟨μ.support_subset_of_isClosed isClosed_Ici hl ha,
    μ.support_subset_of_isClosed isClosed_Iic hu hb⟩

end InvariantIsing

end

end OAI
