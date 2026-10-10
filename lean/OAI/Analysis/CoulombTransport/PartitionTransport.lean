import Mathlib

namespace OAI

universe uAlpha uBeta uIndex uKappa

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.PartitionTransport

variable {α : Type uAlpha} {β : Type uBeta} {ι : Type uIndex} [MeasurableSpace α] [MeasurableSpace β]

/-- Gluing measurable transports on a countable measurable partition gives the
sum of their restricted pushforwards. The partition need only cover almost everywhere. -/
theorem exists_map_eq_sum_of_partition [Countable ι] [Nonempty ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T : ι → α → β) (hT : ∀ i, Measurable (T i)) :
    ∃ f : α → β, Measurable f ∧
      (∀ i, EqOn f (T i) (B i)) ∧
      Measure.map f μ = Measure.sum (fun i => Measure.map (T i) (μ.restrict (B i))) := by
  obtain ⟨f, hf, hfg⟩ := exists_measurable_piecewise B hB T hT (by
    intro i j hij x hx
    exact False.elim (Set.disjoint_left.mp (hdisj hij) hx.1 hx.2))
  refine ⟨f, hf, hfg, ?_⟩
  have hdecomp : μ = Measure.sum (fun i => μ.restrict (B i)) := by
    rw [← Measure.restrict_iUnion hdisj hB, Measure.restrict_eq_self_of_ae_mem hcover]
  calc
    Measure.map f μ = Measure.map f (Measure.sum (fun i => μ.restrict (B i))) :=
      congrArg (Measure.map f) hdecomp
    _ = Measure.sum (fun i => Measure.map f (μ.restrict (B i))) :=
      Measure.map_sum hf.aemeasurable
    _ = _ := by
      congr 1
      funext i
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (hB i)] with x hx
      exact hfg i hx

/-- Prescribed laws on partition pieces can be glued into a transport to their sum. -/
theorem exists_map_eq_of_partition [Countable ι] [Nonempty ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T : ι → α → β) (hT : ∀ i, Measurable (T i))
    (ν : ι → Measure β)
    (hmap : ∀ i, Measure.map (T i) (μ.restrict (B i)) = ν i) :
    ∃ f : α → β, Measurable f ∧
      (∀ i, EqOn f (T i) (B i)) ∧ Measure.map f μ = Measure.sum ν := by
  obtain ⟨f, hf, hfg, hsum⟩ :=
    exists_map_eq_sum_of_partition μ B hB hdisj hcover T hT
  refine ⟨f, hf, hfg, ?_⟩
  simpa only [hmap] using hsum

/-- The finite form, using the usual finite sum of target measures. -/
theorem exists_map_eq_finset_sum_of_partition [Fintype ι] [Nonempty ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T : ι → α → β) (hT : ∀ i, Measurable (T i))
    (ν : ι → Measure β)
    (hmap : ∀ i, Measure.map (T i) (μ.restrict (B i)) = ν i) :
    ∃ f : α → β, Measurable f ∧
      (∀ i, EqOn f (T i) (B i)) ∧ Measure.map f μ = ∑ i, ν i := by
  simpa only [Measure.sum_fintype] using
    exists_map_eq_of_partition μ B hB hdisj hcover T hT ν hmap

/-- The pushforward law of a label that is constant almost everywhere on each
partition piece is the atomic measure with those piece masses. -/
theorem map_eq_sum_dirac_of_partition [Countable ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (L : α → β) (hL : Measurable L) (label : ι → β)
    (hlabel : ∀ i, ∀ᵐ x ∂μ.restrict (B i), L x = label i) :
    Measure.map L μ = Measure.sum (fun i => μ (B i) • Measure.dirac (label i)) := by
  have hdecomp : μ = Measure.sum (fun i => μ.restrict (B i)) := by
    rw [← Measure.restrict_iUnion hdisj hB, Measure.restrict_eq_self_of_ae_mem hcover]
  calc
    Measure.map L μ = Measure.map L (Measure.sum (fun i => μ.restrict (B i))) :=
      congrArg (Measure.map L) hdecomp
    _ = Measure.sum (fun i => Measure.map L (μ.restrict (B i))) :=
      Measure.map_sum hL.aemeasurable
    _ = _ := by
      congr 1
      funext i
      rw [Measure.map_congr (hlabel i), Measure.map_const]
      simp

/-- An exact agreement on a measurable piece gives equality of restricted laws. -/
theorem map_restrict_eq_of_eqOn (μ : Measure α) {B : Set α}
    (hB : MeasurableSet B) {f g : α → β} (heq : EqOn f g B) :
    Measure.map f (μ.restrict B) = Measure.map g (μ.restrict B) := by
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem hB] with x hx
  exact heq hx

/-- Glue two families of transports simultaneously. Their marginal laws and
joint finite-cell law are all explicit. This is the graph-plan step in the
cellwise approximation construction. -/
theorem exists_pair_maps_with_label_law [Countable ι] [Nonempty ι]
    {κ : Type uKappa} [MeasurableSpace κ]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T₂ T₃ : ι → α → α)
    (hT₂ : ∀ i, Measurable (T₂ i)) (hT₃ : ∀ i, Measurable (T₃ i))
    (ν₂ ν₃ : ι → Measure α)
    (hmap₂ : ∀ i, Measure.map (T₂ i) (μ.restrict (B i)) = ν₂ i)
    (hmap₃ : ∀ i, Measure.map (T₃ i) (μ.restrict (B i)) = ν₃ i)
    (hsum₂ : Measure.sum ν₂ = μ) (hsum₃ : Measure.sum ν₃ = μ)
    (p : α → κ) (hp : Measurable p) (l₁ l₂ l₃ : ι → κ)
    (hlabel₁ : ∀ i, ∀ᵐ x ∂μ.restrict (B i), p x = l₁ i)
    (hlabel₂ : ∀ i, ∀ᵐ x ∂ν₂ i, p x = l₂ i)
    (hlabel₃ : ∀ i, ∀ᵐ x ∂ν₃ i, p x = l₃ i) :
    ∃ f g : α → α,
      Measurable f ∧ Measurable g ∧
      Measure.map f μ = μ ∧ Measure.map g μ = μ ∧
      Measure.map (fun x => (p x, (p (f x), p (g x)))) μ =
        Measure.sum (fun i => μ (B i) • Measure.dirac (l₁ i, (l₂ i, l₃ i))) := by
  obtain ⟨f, hf, hfB, hfmap⟩ :=
    exists_map_eq_of_partition μ B hB hdisj hcover T₂ hT₂ ν₂ hmap₂
  obtain ⟨g, hg, hgB, hgmap⟩ :=
    exists_map_eq_of_partition μ B hB hdisj hcover T₃ hT₃ ν₃ hmap₃
  refine ⟨f, g, hf, hg, hfmap.trans hsum₂, hgmap.trans hsum₃, ?_⟩
  apply map_eq_sum_dirac_of_partition μ B hB hdisj hcover
    (fun x => (p x, (p (f x), p (g x))))
    (hp.prodMk ((hp.comp hf).prodMk (hp.comp hg)))
    (fun i => (l₁ i, (l₂ i, l₃ i)))
  intro i
  have hfmapB : Measure.map f (μ.restrict (B i)) = ν₂ i :=
    (map_restrict_eq_of_eqOn μ (hB i) (hfB i)).trans (hmap₂ i)
  have hgmapB : Measure.map g (μ.restrict (B i)) = ν₃ i :=
    (map_restrict_eq_of_eqOn μ (hB i) (hgB i)).trans (hmap₃ i)
  have hfLabel : ∀ᵐ x ∂μ.restrict (B i), p (f x) = l₂ i := by
    refine ae_of_ae_map (μ := μ.restrict (B i)) (p := fun y => p y = l₂ i) hf.aemeasurable ?_
    rw [hfmapB]
    exact hlabel₂ i
  have hgLabel : ∀ᵐ x ∂μ.restrict (B i), p (g x) = l₃ i := by
    refine ae_of_ae_map (μ := μ.restrict (B i)) (p := fun y => p y = l₃ i) hg.aemeasurable ?_
    rw [hgmapB]
    exact hlabel₃ i
  filter_upwards [hlabel₁ i, hfLabel, hgLabel] with x hx hx₂ hx₃
  simp only [hx, hx₂, hx₃]

/-- Redistributing weights to the normalized restrictions of a finite partition
preserves the measure when the weights have the prescribed marginal sums.
Zero-mass cells require no positivity assumption. -/
theorem sum_normalized_restrict_eq [Fintype ι]
    {κ : Type uKappa} [Fintype κ] [DecidableEq κ]
    (μ : Measure α) [IsFiniteMeasure μ] (A : κ → Set α)
    (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ j, A j)
    (label : ι → κ) (w : ι → ℝ≥0∞)
    (hweights : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => label i = j), w i = μ (A j)) :
    (∑ i, (w i / μ (A (label i))) • μ.restrict (A (label i))) = μ := by
  classical
  calc
    (∑ i, (w i / μ (A (label i))) • μ.restrict (A (label i))) =
        ∑ j, ∑ i ∈ Finset.univ.filter (fun i => label i = j),
          (w i / μ (A (label i))) • μ.restrict (A (label i)) :=
      (Finset.sum_fiberwise Finset.univ label _).symm
    _ = ∑ j, μ.restrict (A j) := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (∑ i ∈ Finset.univ.filter (fun i => label i = j),
            (w i / μ (A (label i))) • μ.restrict (A (label i))) =
            ∑ i ∈ Finset.univ.filter (fun i => label i = j),
              (w i / μ (A j)) • μ.restrict (A j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = μ.restrict (A j) := by
          by_cases hz : μ (A j) = 0
          · simp [Measure.restrict_eq_zero.mpr hz]
          · rw [← Finset.sum_smul]
            simp_rw [ENNReal.div_eq_inv_mul]
            rw [← Finset.mul_sum, hweights j,
              ENNReal.inv_mul_cancel hz (measure_ne_top μ (A j)), one_smul]
    _ = μ := by
      rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdisj hA,
        Measure.restrict_eq_self_of_ae_mem hcover]

end Problem356.PartitionTransport

end

end OAI
