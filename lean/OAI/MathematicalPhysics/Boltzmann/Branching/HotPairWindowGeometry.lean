import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotTransportBalance

namespace OAI

/-! # Nested spatial windows for the actual hot pair sequence -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

def hotPairWindowSet (A R : ℝ) : Set HotPairPhase :=
  (Icc (0:ℝ) A ×ˢ Metric.closedBall (0 : JetPrototype.Space) R) ×ˢ univ

theorem hotPairWindowSet_measurable (A R : ℝ) : MeasurableSet (hotPairWindowSet A R) :=
  (measurableSet_Icc.prod measurableSet_closedBall).prod MeasurableSet.univ

theorem hotPairWindowVolume_eq (A R : ℝ) :
    hotPairWindowVolume A R = volume.restrict (hotPairWindowSet A R) := by
  rw [hotPairWindowVolume,hotBaseWindowVolume,Measure.prod_restrict,← Measure.volume_eq_prod,
    Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod]
  rfl

theorem hotPairWindowSet_mono {A B R S : ℝ} (hA : A ≤ B) (hR : R ≤ S) :
    hotPairWindowSet A R ⊆ hotPairWindowSet B S := by
  rintro z ⟨⟨ht,hx⟩,hv⟩
  exact ⟨⟨⟨ht.1,ht.2.trans hA⟩,Metric.closedBall_subset_closedBall hR hx⟩,hv⟩

theorem hotPairWindowVolume_restrict {A B R S : ℝ} (hA : A ≤ B) (hR : R ≤ S) :
    (hotPairWindowVolume B S).restrict (hotPairWindowSet A R) = hotPairWindowVolume A R := by
  rw [hotPairWindowVolume_eq,hotPairWindowVolume_eq]
  exact Measure.restrict_restrict_of_subset (hotPairWindowSet_mono hA hR)

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.compatible (E : HotPairExtraction S) {j k : ℕ} (hjk : j ≤ k) :
    E.pairProfile k =ᵐ[hotPairWindowVolume (j+1) (j+1)] E.pairProfile j := by
  have hle : (j:ℝ)+1 ≤ (k:ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hjk 1
  have hk := (E.pairWeak k).restrict (hotPairWindowSet_measurable (j+1) (j+1))
  rw [hotPairWindowVolume_restrict hle hle] at hk
  exact hk.unique (E.pairWeak j)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end OAI
