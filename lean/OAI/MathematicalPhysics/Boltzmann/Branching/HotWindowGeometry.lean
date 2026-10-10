import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLabelFreeLimit

namespace OAI

/-! # Restriction and compatibility of the nested hot-density windows -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

def hotWindowSet (A R : ℝ) : Set HotKineticPhase :=
  (Icc (0:ℝ) A ×ˢ Metric.closedBall (0 : JetPrototype.Space) R) ×ˢ univ

theorem hotWindowSet_measurable (A R : ℝ) : MeasurableSet (hotWindowSet A R) :=
  (measurableSet_Icc.prod measurableSet_closedBall).prod MeasurableSet.univ

theorem hotWindowVolume_eq (A R : ℝ) :
    hotWindowVolume A R = volume.restrict (hotWindowSet A R) := by
  rw [hotWindowVolume,Measure.prod_restrict,← Measure.volume_eq_prod,
    Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod]
  rfl

theorem hotWindowSet_mono {A B R S : ℝ} (hA : A ≤ B) (hR : R ≤ S) :
    hotWindowSet A R ⊆ hotWindowSet B S := by
  rintro z ⟨⟨ht,hx⟩,hv⟩
  exact ⟨⟨⟨ht.1,ht.2.trans hA⟩,Metric.closedBall_subset_closedBall hR hx⟩,hv⟩

theorem hotWindowVolume_restrict {A B R S : ℝ} (hA : A ≤ B) (hR : R ≤ S) :
    (hotWindowVolume B S).restrict (hotWindowSet A R) = hotWindowVolume A R := by
  rw [hotWindowVolume_eq,hotWindowVolume_eq]
  exact Measure.restrict_restrict_of_subset (hotWindowSet_mono hA hR)

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.compatible (E : HotLimitExtraction S) {j k : ℕ} (hjk : j ≤ k) :
    E.profile k =ᵐ[hotWindowVolume (j+1) (j+1)] E.profile j := by
  have hle : (j:ℝ)+1 ≤ (k:ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hjk 1
  have hk := (E.weak k).restrict (hotWindowSet_measurable (j+1) (j+1))
  rw [hotWindowVolume_restrict hle hle] at hk
  exact hk.unique (E.weak j)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end OAI
