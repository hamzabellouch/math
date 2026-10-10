import OAI.Dynamics.StandardMap.LimitBalance

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma open_null_of_integral_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [RegularSpace X]
    (μ : Measure X) [μ.Regular] {U : Set X} (hU : IsOpen U)
    (hzero : ∀ g : C_c(X,ℝ), (∀ x,0 ≤ g x) → (∀ x∉U,g x=0) → ∫ x,g x ∂μ=0) : μ U=0 := by
  rw [hU.measure_eq_iSup_isCompact μ]
  apply le_antisymm _ bot_le
  simp only [iSup_le_iff]
  intro K hKU hK
  obtain ⟨⟨f,hfc⟩,hfK,hfU,hfs,hfr⟩ := exists_continuous_one_zero_of_isCompact
    hK hU.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKU)
  let g : C_c(X,ℝ) := ⟨⟨f,hfc⟩,hfs⟩
  have hint := hzero g (fun x => (hfr x).1) (fun x hx => hfU hx)
  have hb := (hfc.integrable_of_hasCompactSupport hfs (μ := μ)).measure_le_integral
    (Eventually.of_forall fun x => (hfr x).1) (fun x hx => (hfK hx).ge)
  change μ K ≤ ENNReal.ofReal (∫ x,g x ∂μ) at hb
  rw [hint,ENNReal.ofReal_zero] at hb
  convert! hb using 1
lemma vague_open_null {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [RegularSpace X]
    (l : Filter ι) [l.NeBot] (μ : ι → Measure X) (ν : Measure X) [ν.Regular]
    (hconv : ∀ g : C_c(X,ℝ), Tendsto (fun i => ∫ x,g x ∂μ i) l (𝓝 (∫ x,g x ∂ν)))
    {U : Set X} (hU : IsOpen U)
    (hzero : ∀ g : C_c(X,ℝ), (∀ x,0 ≤ g x) → (∀ x∉U,g x=0) →
      Tendsto (fun i => ∫ x,g x ∂μ i) l (𝓝 0)) : ν U=0 := by
  apply open_null_of_integral_zero ν hU
  intro g hg hz
  exact tendsto_nhds_unique (hconv g) (hzero g hg hz)
lemma ae_le_zero_of_positive_rational_null {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hn : ∀ q : ℚ,0<q → μ {x | (q:ℝ)<f x}=0) : ∀ᵐ x ∂μ, f x ≤ 0 := by
  have hh : ∀ q : ℚ,0<q → ∀ᵐ x ∂μ,¬(q:ℝ)<f x := fun q hq => ae_iff.mpr (by simpa using hn q hq)
  have h := ae_all_iff.mpr (fun q : ℚ => ae_all_iff.mpr (hh q))
  filter_upwards [h] with x hx
  by_contra hpos
  obtain ⟨q,hq,hqx⟩ := exists_rat_btwn (lt_of_not_ge hpos)
  exact hx q (by exact_mod_cast hq) hqx
end StandardMapEntropy

end OAI
