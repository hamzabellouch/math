import OAI.Analysis.CircleDomains.Probability.MeasureFamilyCompactLocalization
import OAI.Analysis.CircleDomains.Probability.MeasureFamilyIncreasing
import OAI.Analysis.CircleDomains.Probability.CompactFiniteMeasureBorel

namespace OAI

/-! If zero is absent from the image, compact localization can also retain
a positive lower mass. The resulting compact family avoids zero. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_nonzero_modulus_localization
    {A Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] (K : A → FiniteMeasure Z)
    (hK : ∀ a, K a ≠ 0) {c : ℝ≥0∞}
    (hc : c < measureFamilyModulus A Z σ K) :
    ∃ T : Set (FiniteMeasure Z), IsCompact T ∧ (0 : FiniteMeasure Z) ∉ T ∧
      c < measureFamilyModulus {a | K a ∈ T} Z σ (fun a => K a.val) := by
  obtain ⟨T,hT,hmod⟩ := exists_compact_modulus_localization σ K hc
  let B : Set A := {a | K a ∈ T}
  let S : ℕ → Set B := fun n => {a | 1/((n:ℝ)+1) ≤ ((K a.val).mass : ℝ)}
  have hm : Monotone S := by
    intro n m hnm a ha
    have hnm' : (n:ℝ)+1 ≤ (m:ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    exact (one_div_le_one_div_of_le (by positivity : 0 < (n:ℝ)+1) hnm').trans ha
  have hu : ∀ a : B, ∃ n, a ∈ S n := by
    intro a
    have hmass : 0 < ((K a.val).mass : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr ((FiniteMeasure.mass_nonzero_iff (K a.val)).mpr (hK a.val)))
    obtain ⟨n,hn⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hmass)).exists
    exact ⟨n,hn.le⟩
  rw [measureFamilyModulus_iUnion σ (fun a : B => K a.val) S hm hu] at hmod
  obtain ⟨N,hN⟩ := lt_iSup_iff.mp hmod
  let T' : Set (FiniteMeasure Z) := T ∩ {v | 1/((N:ℝ)+1) ≤ (v.mass : ℝ)}
  have hT' : IsCompact T' := hT.inter_right
    (isClosed_le continuous_const (NNReal.continuous_coe.comp FiniteMeasure.continuous_mass))
  have hz : (0 : FiniteMeasure Z) ∉ T' := by
    intro h
    have hp : 0 < 1/((N:ℝ)+1) := by positivity
    have hn : 1/((N:ℝ)+1) ≤ 0 := by simpa using h.2
    exact (not_le_of_gt hp) hn
  refine ⟨T',hT',hz,?_⟩
  have heq : range (fun a : S N => K a.val.val) =
      range (fun a : {a | K a ∈ T'} => K a.val) := by
    ext v
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨⟨a.val.val,a.val.property,a.property⟩,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨⟨⟨a.val,a.property.1⟩,a.property.2⟩,rfl⟩
  exact hN.trans_eq (measureFamilyModulus_eq_of_range_eq σ _ _ heq)

end CircleDomainRigidity

end

end OAI
