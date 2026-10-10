import OAI.Analysis.CircleDomains.Probability.MeasureFamilyNullUnions

namespace OAI

/-! A positive-modulus family has a positive-modulus piece in every
countable cover. In particular one may bound the finite measures' masses
before constructing the dual probability plan. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_positive_modulus_piece
    {A Z ι : Type*} [MeasurableSpace Z] [Countable ι]
    (σ : Measure Z) (K : A → FiniteMeasure Z) (S : ι → Set A)
    (hcover : ∀ a, ∃ i, a ∈ S i) (hp : 0 < measureFamilyModulus A Z σ K) :
    ∃ i, 0 < measureFamilyModulus (S i) Z σ (fun a => K a.val) := by
  by_contra hn
  push Not at hn
  have hz : ∀ i, measureFamilyModulus (S i) Z σ (fun a => K a.val) = 0 :=
    fun i => le_antisymm (hn i) bot_le
  exact hp.ne' (measureFamilyModulus_zero_of_countable_cover σ K S hcover hz)

lemma exists_positive_modulus_bounded_mass {A Z : Type*} [MeasurableSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) (hp : 0 < measureFamilyModulus A Z σ K) :
    ∃ n : ℕ, 0 < measureFamilyModulus {a | (K a : Measure Z) univ ≤ n} Z σ
      (fun a => K a.val) := by
  apply exists_positive_modulus_piece σ K (fun n : ℕ => {a | (K a : Measure Z) univ ≤ n}) _ hp
  intro a
  obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt (measure_ne_top (K a : Measure Z) univ)
  exact ⟨n,hn.le⟩

end CircleDomainRigidity

end

end OAI
