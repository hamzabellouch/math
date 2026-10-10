import OAI.Analysis.CircleDomains.Sobolev.RegularCoareaNeighborhood
import OAI.Analysis.CircleDomains.Sobolev.WeightedCoareaUnion

namespace OAI

/-! Weighted coarea on the noncritical part of a C1 planar domain. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma regular_weighted_coarea {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    WeightedScalarCoareaIdentity (D ∩ {z | fderiv ℝ f z ≠ 0}) f q := by
  let R := D ∩ {z | fderiv ℝ f z ≠ 0}
  rcases R.eq_empty_or_nonempty with hempty | hne
  · change WeightedScalarCoareaIdentity R f q
    rw [hempty]
    constructor
    · have he : weightedScalarLevelLength ∅ f q = fun _ : ℝ => 0 := by
        funext t
        simp [weightedScalarLevelLength]
      rw [he]
      exact measurable_const.aemeasurable
    · simp [weightedScalarLevelLength]
  let : Nonempty R := hne.to_subtype
  choose U hU hxU hUR hco using fun x : R =>
    exists_regular_coarea_neighborhood hD hf x.property.1 x.property.2
  have hcover : R ⊆ ⋃ x : R, U x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  have hlin : IsLindelof R := isLindelof_iff_lindelofSpace.mpr inferInstance
  obtain ⟨v, hv⟩ := hlin.indexed_countable_subcover U hU hcover
  let A : ℕ → Set ℂ := disjointed (fun n => U (v n))
  have hAU : ∀ n, A n ⊆ U (v n) := fun n => disjointed_subset _ n
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.disjointed (fun j => (hU (v j)).measurableSet) n
  have hAD : ∀ n, A n ⊆ D := fun n => (hAU n).trans ((hUR (v n)).trans inter_subset_left)
  have hlocal : ∀ n, WeightedScalarCoareaIdentity (A n) f q := fun n =>
    hco (v n) (A n) (hA n) (hAU n) q hq
  have heq : (⋃ n, A n) = R := by
    rw [show A = disjointed (fun n => U (v n)) by rfl, iUnion_disjointed]
    exact (iUnion_subset (fun n => hUR (v n))).antisymm hv
  have h := weighted_coarea_iUnion hD hf.continuousOn A hA (disjoint_disjointed _) hAD q hlocal
  rwa [heq] at h

end CircleDomainRigidity

end

end OAI
