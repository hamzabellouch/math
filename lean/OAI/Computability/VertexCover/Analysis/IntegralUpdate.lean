import Mathlib
import OAI.Computability.VertexCover.Fourier.SourceOccurrences
import OAI.Computability.VertexCover.Analysis.OwnPrivateListsDecoding

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open MeasureTheory

theorem listHitMaximum_measurable {E : Type*} [MeasurableSpace E]
    (Φ : LabelCover) {d : ℕ} (L : E → Φ.PrivateLists d)
    (hL : ∀ i (a : i.LocalLabel), MeasurableSet {x | a ∈ L x i})
    (seed : Φ.Seeds d) (J : Finset (Fin d)) :
    Measurable (fun x => Φ.listHitMaximum (L x) seed J) := by
  classical
  have hhit : ∀ I : Finset (Φ.Coordinate d), ∀ j : Fin d,
      MeasurableSet {x | Φ.ListHit (L x) seed I j} := by
    intro I j
    change MeasurableSet {x | ∃ a : (Φ.query seed j).LocalLabel,
      a ∈ L x (Φ.query seed j) ∧ (⟨Φ.query seed j, a⟩ : Φ.Coordinate d) ∈ I}
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro a
    exact (hL _ a).inter (MeasurableSet.const _)
  have hcard : ∀ I : Finset (Φ.Coordinate d),
      Measurable (fun x => (Φ.hitPositions (L x) seed I J).card) := by
    intro I
    simp only [hitPositions, Finset.card_filter]
    apply Finset.measurable_sum
    intro j _
    exact Measurable.ite (hhit I j) measurable_const measurable_const
  have hsup : ∀ S : Finset (Finset (Φ.Coordinate d)),
      Measurable (fun x => S.sup (fun I => (Φ.hitPositions (L x) seed I J).card)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert I S hi ih =>
      simp only [Finset.sup_insert]
      exact (hcard I).sup ih
  exact hsup _

theorem ownPrivateLists_hits_integrable (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen seed : Φ.Seeds d) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (β : ℝ) :
    Integrable (fun s => (Φ.listHitMaximum
      (Φ.ownPrivateLists J frozen c0 A hA s β) seed J : ℝ)) (Φ.batchLaw J) := by
  classical
  have hmeas := Φ.listHitMaximum_measurable
    (fun s => Φ.ownPrivateLists J frozen c0 A hA s β)
    (Φ.ownPrivateLists_membership_measurable J frozen c0 A hA β) seed J
  have hcast : Measurable (fun s => (Φ.listHitMaximum
      (Φ.ownPrivateLists J frozen c0 A hA s β) seed J : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hmeas
  apply Integrable.of_bound hcast.aestronglyMeasurable (J.card : ℝ)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  apply Nat.cast_le.mpr
  apply Finset.sup_le
  intro I _
  exact Finset.card_le_card (Finset.filter_subset _ _)

end VertexCover.LabelCover

namespace VertexCover.Product
open MeasureTheory

theorem update_measurePreserving {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι) :
    MeasurePreserving (fun p : E × (ι → E) => Function.update p.2 j p.1)
      (μ.prod (Measure.pi (fun _ : ι => μ))) (Measure.pi (fun _ : ι => μ)) := by
  have hm : Measurable (fun p : E × (ι → E) => Function.update p.2 j p.1) :=
    Measurable.of_eval (fun k => by
      by_cases hk : k = j
      · subst k; simpa using measurable_fst
      · simpa only [Function.update_of_ne hk, Function.comp_def] using
          (measurable_pi_apply k).comp measurable_snd)
  refine ⟨hm, (Measure.pi_eq (fun S hS => ?_)).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hS)]
  have hpre : (fun p : E × (ι → E) => Function.update p.2 j p.1) ⁻¹' Set.univ.pi S =
      S j ×ˢ Set.univ.pi (Function.update S j Set.univ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro hp
      refine ⟨?_, ?_⟩
      · simpa using hp j
      · intro k
        by_cases hk : k = j
        · subst k; simp
        · simpa [Function.update_of_ne hk] using hp k
    · rintro ⟨hp, hq⟩ k
      by_cases hk : k = j
      · subst k; simpa using hp
      · simpa [Function.update_of_ne hk] using hq k
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have hfun : (fun k => μ (Function.update S j Set.univ k)) =
      Function.update (fun k => μ (S k)) j 1 := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ j), one_mul]
  simpa only [Finset.sdiff_singleton_eq_erase] using
    Finset.mul_prod_erase Finset.univ (fun k => μ (S k)) (Finset.mem_univ j)

theorem update_ae {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι)
    {P : (ι → E) → Prop} (hP : ∀ᵐ s ∂Measure.pi (fun _ : ι => μ), P s) :
    ∀ᵐ x ∂μ, ∀ᵐ s ∂Measure.pi (fun _ : ι => μ), P (Function.update s j x) := by
  exact Measure.ae_ae_of_ae_prod ((update_measurePreserving μ j).quasiMeasurePreserving.ae hP)

theorem integral_update {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι)
    {f : (ι → E) → ℝ} (hf : Integrable f (Measure.pi (fun _ : ι => μ))) :
    (∫ x, ∫ s, f (Function.update s j x) ∂Measure.pi (fun _ : ι => μ) ∂μ) =
      ∫ s, f s ∂Measure.pi (fun _ : ι => μ) := by
  have hp := update_measurePreserving μ j
  calc
    _ = ∫ p, f (Function.update p.2 j p.1)
        ∂(μ.prod (Measure.pi (fun _ : ι => μ))) := by
      simpa only [Function.comp_apply] using
        (integral_prod _ (hp.integrable_comp_of_integrable hf)).symm
    _ = ∫ s, f s ∂Measure.map (fun p : E × (ι → E) => Function.update p.2 j p.1)
        (μ.prod (Measure.pi (fun _ : ι => μ))) := by
      exact (integral_map hp.measurable.aemeasurable
        (by simpa only [hp.map_eq] using hf.aestronglyMeasurable)).symm
    _ = _ := by rw [hp.map_eq]

end VertexCover.Product


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
