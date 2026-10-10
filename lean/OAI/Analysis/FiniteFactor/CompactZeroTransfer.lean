import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

/-- Compact subsets carrying uniformly almost all approximating mass carry
all limiting mass as their uniform losses tend to zero. -/
theorem finiteMeasure_ae_of_compact_approximation {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μ : ℕ → FiniteMeasure X) (ν : FiniteMeasure X)
    (hlim : Tendsto μ atTop (𝓝 ν)) (Z : Set X) (hZ : MeasurableSet Z)
    (hcompact : ∀ ε : ℝ≥0, 0 < ε → ∃ K, IsCompact K ∧ K ⊆ Z ∧
      ∀ n, (μ n : Measure X) Kᶜ ≤ ε) :
    ∀ᵐ x ∂(ν : Measure X), x ∈ Z := by
  have hmass : Tendsto (fun n => (μ n : Measure X) Set.univ) atTop
      (𝓝 ((ν : Measure X) Set.univ)) := by
    simpa only [Function.comp_def, FiniteMeasure.ennreal_mass] using
      (ENNReal.continuous_coe.tendsto ν.mass).comp hlim.mass
  have hfull : (ν : Measure X) Set.univ ≤ (ν : Measure X) Z := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨K,hK,hKZ,hbound⟩ := hcompact ε hε
    have hle : ∀ n, (μ n : Measure X) Set.univ ≤ (μ n : Measure X) K + ε := by
      intro n
      rw [← measure_add_measure_compl hK.isClosed.measurableSet]
      exact add_le_add le_rfl (hbound n)
    have hsup := Filter.limsup_le_limsup (f := atTop) (Eventually.of_forall hle)
    rw [hmass.limsup_eq, limsup_add_const atTop _ _ (by isBoundedDefault) (by isBoundedDefault)] at hsup
    exact hsup.trans (add_le_add
      ((FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim hK.isClosed).trans
        (measure_mono hKZ)) le_rfl)
  rw [ae_iff]
  change (ν : Measure X) Zᶜ = 0
  rw [measure_compl hZ (by finiteness), tsub_eq_zero_of_le hfull]

/-- The loss outside a product compact set is bounded by its two marginal
losses. The identity set itself may only be Borel. -/
theorem measure_pair_compact_loss {X : Type*} [MeasurableSpace X]
    (μ : Measure (X × X)) (Q : Set X) (hQ : MeasurableSet Q)
    (Z : Set (X × X)) (hZ : ∀ᵐ z ∂μ, z ∈ Z) :
    μ ((Q ×ˢ Q) ∩ Z)ᶜ ≤ (μ.map Prod.fst) Qᶜ + (μ.map Prod.snd) Qᶜ := by
  have he : (((Q ×ˢ Q) ∩ Z)ᶜ : Set (X × X)) =ᵐ[μ] ((Q ×ˢ Q)ᶜ : Set (X × X)) := by
    filter_upwards [hZ] with z hz
    apply propext
    change (¬ (z ∈ Q ×ˢ Q ∧ z ∈ Z)) ↔ ¬ z ∈ Q ×ˢ Q
    simp [hz]
  rw [measure_congr he]
  have hs : (Q ×ˢ Q)ᶜ = (Prod.fst ⁻¹' Qᶜ) ∪ (Prod.snd ⁻¹' Qᶜ) := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_union, Set.mem_preimage]
    tauto
  rw [hs, Measure.map_apply measurable_fst hQ.compl,
    Measure.map_apply measurable_snd hQ.compl]
  exact measure_union_le _ _

end FiniteFactor

end OAI
