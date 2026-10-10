import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.RestrictedCellEnergy

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

def partitionMean (μ : Measure X) (s : ι → Set X) (w : X → ℝ) : X → ℝ := by
  classical
  exact fun x => ∑ i, (s i).indicator (fun _ => cellMean (μ.restrict (s i)) w) x

theorem partitionMean_eq_cell (μ : Measure X) (s : ι → Set X) (w : X → ℝ)
    (hd : Pairwise (Disjoint on s)) (i : ι) (x : X) (hx : x ∈ s i) :
    partitionMean μ s w x = cellMean (μ.restrict (s i)) w := by
  classical
  unfold partitionMean
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    have hxj : x ∉ s j := fun hj => (Set.disjoint_left.mp (hd hji)) hj hx
    exact indicator_of_notMem hxj _
  · simp

theorem partition_error_eq_sum (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (w : X → ℝ) (hw : MemLp w 2 μ) :
    (∫ x in ⋃ i, s i, (w x - partitionMean μ s w x) ^ 2 ∂μ) =
      ∑ i, ∫ x in s i, (w x - cellMean (μ.restrict (s i)) w) ^ 2 ∂μ := by
  have heq (i : ι) : (fun x => (w x - partitionMean μ s w x) ^ 2) =ᵐ[μ.restrict (s i)]
      (fun x => (w x - cellMean (μ.restrict (s i)) w) ^ 2) := by
    filter_upwards [ae_restrict_mem (hs i)] with x hx
    rw [partitionMean_eq_cell μ s w hd i x hx]
  have hi (i : ι) : IntegrableOn (fun x => (w x - partitionMean μ s w x) ^ 2) (s i) μ :=
    (integrable_congr (heq i)).mpr
      (((hw.restrict (s i)).sub (memLp_const _)).integrable_sq)
  rw [integral_iUnion_fintype hs hd hi]
  exact Finset.sum_congr rfl fun i _ => integral_congr_ae (heq i)

theorem iterated_cell_energy_eq_product (μ : Measure X) [IsFiniteMeasure μ]
    (s : Set X) (E : X × X → ℝ) (hE : Integrable E (μ.prod μ)) :
    (∫ x in s, ∫ y in s, E (x, y) ∂μ ∂μ) = ∫ p in s ×ˢ s, E p ∂μ.prod μ := by
  have hi : Integrable E ((μ.restrict s).prod (μ.restrict s)) := by
    rw [Measure.prod_restrict]
    exact hE.restrict
  rw [← Measure.prod_restrict]
  exact (integral_prod E hi).symm

theorem sum_cell_energy_le (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (E : X × X → ℝ)
    (hE : Integrable E (μ.prod μ)) (hEpos : ∀ p, 0 ≤ E p) :
    (∑ i, ∫ x in s i, ∫ y in s i, E (x, y) ∂μ ∂μ) ≤ ∫ p, E p ∂μ.prod μ := by
  have hprod : Pairwise (Disjoint on (fun i => s i ×ˢ s i)) :=
    fun i j hij => Set.disjoint_prod.mpr (Or.inl (hd hij))
  calc
    _ = ∑ i, ∫ p in s i ×ˢ s i, E p ∂μ.prod μ :=
      Finset.sum_congr rfl fun i _ => iterated_cell_energy_eq_product μ (s i) E hE
    _ = ∫ p in ⋃ i, s i ×ˢ s i, E p ∂μ.prod μ :=
      (integral_iUnion_fintype (fun i => (hs i).prod (hs i)) hprod (fun i => hE.restrict)).symm
    _ ≤ _ := setIntegral_le_integral hE (Filter.Eventually.of_forall hEpos)

variable [MetricSpace X]

theorem partition_error_le_scale_times_energy (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (m : ℕ) (w : X → ℝ) (hw : MemLp w 2 μ)
    (a h c : ℝ) (ha : 0 ≤ a) (hh : 0 < h) (hc : 0 < c)
    (hmass : ∀ i, c * h ^ m ≤ μ.real (s i))
    (hdiam : ∀ i, ∀ x ∈ s i, ∀ y ∈ s i, dist x y ≤ a * h)
    (hE : Integrable (fun p : X × X => fractionalPairEnergy m w p.1 p.2) (μ.prod μ)) :
    (∫ x in ⋃ i, s i, (w x - partitionMean μ s w x) ^ 2 ∂μ) ≤
      (a ^ (m + 1) / (2 * c) * h) *
        (∫ p : X × X, fractionalPairEnergy m w p.1 p.2 ∂μ.prod μ) := by
  have hi (i : ι) : Integrable (fun p : X × X => fractionalPairEnergy m w p.1 p.2)
      ((μ.restrict (s i)).prod (μ.restrict (s i))) := by
    rw [Measure.prod_restrict]
    exact hE.restrict
  rw [partition_error_eq_sum μ s hs hd w hw]
  calc
    _ ≤ ∑ i, (a ^ (m + 1) / (2 * c) * h) *
        (∫ x in s i, ∫ y in s i, fractionalPairEnergy m w x y ∂μ ∂μ) :=
      Finset.sum_le_sum fun i _ => restricted_cell_variance_le_scale_times_energy
        μ (s i) (hs i) m w (hw.restrict (s i)) a h c ha hh hc (hmass i) (hdiam i) (hi i)
    _ = (a ^ (m + 1) / (2 * c) * h) *
        (∑ i, ∫ x in s i, ∫ y in s i, fractionalPairEnergy m w x y ∂μ ∂μ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_cell_energy_le μ s hs hd _ hE (fun p => fractionalPairEnergy_nonneg m w p.1 p.2))
      (by positivity)

end

end RieszRectifiability

end OAI
