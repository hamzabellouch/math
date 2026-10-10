import OAI.Analysis.CircleDomains.Probability.MeasureFamilyBoundedSequence
import OAI.Analysis.CircleDomains.Sobolev.ExtendedDensityL2

namespace OAI

/-! Increasing-family continuity of pointwise modulus. Infinite values of
the approximating densities are isolated in one Borel null set and repaired. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma measureFamilyModulus_le_of_increasing_strict_bound
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) [IsSeparable σ]
    (K : A → FiniteMeasure Z) (S : ℕ → Set A) (hmono : Monotone S)
    (hcover : ∀ a, ∃ n, a ∈ S n) {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ n, measureFamilyModulus (S n) Z σ (fun a => K a.val) < ENNReal.ofReal D) :
    measureFamilyModulus A Z σ K ≤ ENNReal.ofReal D := by
  choose h hh ha he using (fun n => exists_admissible_of_modulus_lt σ
    (fun a : S n => K a.val) (hbound n))
  have hr (n : ℕ) := extended_density_L2 σ (h n) (hh n) hD (he n).le
  choose hm hu hnorm hNm hN0 using hr
  let N : Set Z := ⋃ n : ℕ, {z | h n z = ∞}
  have hN : MeasurableSet N := MeasurableSet.iUnion hNm
  have hσN : σ N = 0 := measure_iUnion_null hN0
  let B : Set A := {a | (K a : Measure Z) N ≠ 0}
  have hB : measureFamilyModulus B Z σ (fun a => K a.val) = 0 :=
    measureFamilyModulus_zero_of_charges_null_set σ _ hN hσN (fun a => a.property)
  rw [measureFamilyModulus_remove_null_family σ K B hB]
  have hn (n : ℕ) : ‖(hu n).toLp (fun z => (h n z).toReal)‖ ≤ Real.sqrt D := by
    nlinarith [hnorm n, norm_nonneg ((hu n).toLp (fun z => (h n z).toReal)),
      Real.sqrt_nonneg D,Real.sq_sqrt hD]
  have hb := measureFamilyModulus_le_of_bounded_L2_sequence σ
    (fun a : (Bᶜ : Set A) => K a.val) (fun n z => (h n z).toReal)
    hu hm (fun _ _ => ENNReal.toReal_nonneg) hn ?_
  · simpa only [Real.sq_sqrt hD] using hb
  · intro a
    obtain ⟨n,han⟩ := hcover a.val
    filter_upwards [eventually_ge_atTop n] with k hk
    have hνN : (K a.val : Measure Z) N = 0 := by
      simpa only [B,mem_compl_iff,mem_ofPred_eq,not_not] using a.property
    have hνk : (K a.val : Measure Z) {z | h k z = ∞} = 0 :=
      measure_mono_null (subset_iUnion (fun n => {z | h n z = ∞}) k) hνN
    rw [lintegral_ofReal_toReal_eq_away_infinity _ _ hνk]
    exact ha k ⟨a.val,hmono hk han⟩

lemma measureFamilyModulus_iUnion
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) [IsSeparable σ]
    (K : A → FiniteMeasure Z) (S : ℕ → Set A) (hmono : Monotone S)
    (hcover : ∀ a, ∃ n, a ∈ S n) :
    measureFamilyModulus A Z σ K =
      ⨆ n, measureFamilyModulus (S n) Z σ (fun a => K a.val) := by
  apply le_antisymm
  · by_contra hnot
    have hlt : (⨆ n, measureFamilyModulus (S n) Z σ (fun a => K a.val)) <
        measureFamilyModulus A Z σ K := lt_of_not_ge hnot
    obtain ⟨d,hd,hdm⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
    have hbound (n : ℕ) : measureFamilyModulus (S n) Z σ (fun a => K a.val) <
        ENNReal.ofReal (d : ℝ) := by
      simpa only [ENNReal.ofReal_coe_nnreal] using (le_iSup
        (fun n => measureFamilyModulus (S n) Z σ (fun a => K a.val)) n).trans_lt hd
    have hb := measureFamilyModulus_le_of_increasing_strict_bound σ K S hmono hcover
      d.coe_nonneg hbound
    exact (not_lt_of_ge (by simpa only [ENNReal.ofReal_coe_nnreal] using hb)) hdm
  · apply iSup_le
    intro n
    apply measureFamilyModulus_mono_range
    rintro _ ⟨a,rfl⟩
    exact mem_range_self a.val

end CircleDomainRigidity

end

end OAI
