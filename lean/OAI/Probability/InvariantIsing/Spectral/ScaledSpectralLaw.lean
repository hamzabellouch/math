import OAI.Probability.InvariantIsing.Pressure.LimitingPressure

namespace OAI

/-! Positive temperature scaling preserves the precise spectral hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

def scaledSpectralLaw (ν : ProbabilityMeasure ℝ) (β : ℝ) : ProbabilityMeasure ℝ :=
  ν.map (fun x => β*x)

lemma scaled_spectral_support_bound (ν : ProbabilityMeasure ℝ) (a b β : ℝ)
    (hβ : 0 ≤ β) (hbound : (ν : Measure ℝ).support ⊆ Icc a b) :
    (scaledSpectralLaw ν β : Measure ℝ).support ⊆ Icc (β*a) (β*b) := by
  apply Measure.support_subset_of_isClosed isClosed_Icc
  change ∀ᵐ y ∂((ν : Measure ℝ).map (fun x => β*x)), y∈Icc (β*a) (β*b)
  apply (ae_map_iff (measurable_const.mul measurable_id).aemeasurable measurableSet_Icc).mpr
  filter_upwards [(ν : Measure ℝ).support_mem_ae] with x hx
  exact ⟨mul_le_mul_of_nonneg_left (hbound hx).1 hβ,
    mul_le_mul_of_nonneg_left (hbound hx).2 hβ⟩

lemma scaled_spectral_support_mem (ν : ProbabilityMeasure ℝ) (β x : ℝ)
    (hx : x∈(ν : Measure ℝ).support) :
    β*x∈(scaledSpectralLaw ν β : Measure ℝ).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro S hS hopen
  change ((ν : Measure ℝ).map (fun x => β*x)) S > 0
  have hm : Measurable (fun y : ℝ => β*y) := measurable_const.mul measurable_id
  rw [Measure.map_apply hm hopen.measurableSet]
  exact (Measure.mem_support_iff_forall x).mp hx _
    ((hopen.preimage (continuous_const.mul continuous_id)).mem_nhds hS)

lemma scaled_spectral_compact (ν : ProbabilityMeasure ℝ) (a b β : ℝ)
    (hβ : 0 ≤ β) (hbound : (ν : Measure ℝ).support ⊆ Icc a b) :
    IsCompact (scaledSpectralLaw ν β : Measure ℝ).support :=
  isCompact_Icc.of_isClosed_subset Measure.isClosed_support
    (scaled_spectral_support_bound ν a b β hβ hbound)

lemma scaled_spectral_no_outliers (eig : (N : ℕ) → Fin N → ℝ) (a b β : ℝ)
    (hβ : 0 < β)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i,
      β*a-ε ≤ β*eig N i ∧ β*eig N i ≤ β*b+ε := by
  intro ε hε
  filter_upwards [hno (ε/β) (div_pos hε hβ)] with N hN i
  have hl := mul_le_mul_of_nonneg_left (hN i).1 hβ.le
  have hu := mul_le_mul_of_nonneg_left (hN i).2 hβ.le
  have he : β*(ε/β)=ε := mul_div_cancel₀ ε hβ.ne'
  rw [mul_sub,he] at hl
  rw [mul_add,he] at hu
  exact ⟨hl,hu⟩

lemma scaled_spectral_weak (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ) (β : ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)) :
    Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (fun i => β*eig (k+1) i))
      atTop (𝓝 (scaledSpectralLaw ν β)) := by
  have hh := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ ν hweak
    (show Continuous (fun x : ℝ => β*x) from continuous_const.mul continuous_id)
  apply hh.congr
  intro k
  apply ProbabilityMeasure.toMeasure_injective
  exact empiricalSpectralLaw_map _ _ _ (measurable_const.mul measurable_id)

end InvariantIsing

end

end OAI
