import OAI.NumberTheory.TotientAsymptotic.BandExtraction
import OAI.NumberTheory.TotientAsymptotic.TupleCoefficient
import OAI.NumberTheory.TotientAsymptotic.PPTErrorEnvelope

namespace OAI

/-! The qualitative all-preimage structural condition. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def ExtractedStructureInput : Prop :=
  ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∀ P : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      preimageExceptionCount x (extractedStructureCondition x P) ≤
        (δ P+ε)*tupleNormalization x

lemma preimageExceptionCount_le_totientCount (x : ℝ) (Q : ℕ → Prop) :
    preimageExceptionCount x Q ≤ V x := by
  classical
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hv,n,hn,hphi,_⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hv,n,hn,hphi⟩

lemma ppt_natural_exponential_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun P : ℕ => Real.exp (-c*(P:ℝ))) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos hc))

lemma ppt_natural_gaussian_tendsto :
    Tendsto (fun P : ℕ => Real.exp (-(P:ℝ)^2/4)) atTop (𝓝 0) := by
  have hp : Tendsto (fun P : ℕ => (P:ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hh := Real.tendsto_exp_atBot.comp
    (hp.const_mul_atTop_of_neg (by norm_num : -(1/4:ℝ) < 0))
  convert hh using 1
  ext P
  congr 1
  ring

theorem extractedStructureInput_of_small
    (hupper : ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, V x ≤ C*tupleNormalization x)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ P : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      preimageExceptionCount x (extractedStructureCondition x P) ≤
        ε*tupleNormalization x) : ExtractedStructureInput := by
  obtain ⟨C,hC⟩ := hupper
  apply ppt_iterated_error_envelope
    (fun P x => preimageExceptionCount x (extractedStructureCondition x P))
    tupleNormalization scale_eventually_pos _ hsmall
  refine ⟨C,?_⟩
  filter_upwards [hC] with x hx
  intro P
  exact (preimageExceptionCount_le_totientCount x _).trans hx

/-- Preserve the original quantitative Ford-based conditional route while
the unconditional proof needs only this smaller qualitative conclusion. -/
theorem extractedStructureInput_of_ford (hscale : FordScaleBounds)
    (h10 : FordTheorem10Input) (h16 : FordTheorem16Input) :
    ExtractedStructureInput := by
  obtain ⟨cmin,cmax,_hc,hscale⟩ := hscale
  let K := max 1 |cmax|
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hupper : ∀ᶠ x : ℝ in atTop, V x ≤ K*tupleNormalization x := by
    filter_upwards [hscale,scale_eventually_pos] with x hx hn
    have hh : V x/tupleNormalization x ≤ cmax := hx.2
    exact (div_le_iff₀ hn).mp
      (hh.trans ((le_abs_self cmax).trans (le_max_right _ _)))
  apply extractedStructureInput_of_small ⟨K,hupper⟩
  obtain ⟨C,hC,hcount⟩ := extracted_structure_exception_bound h10 h16
  intro ε hε
  have hlim : Tendsto (fun P : ℕ => C*K*Real.exp (-(P:ℝ)/2500)) atTop (𝓝 0) := by
    have hh : Tendsto (fun P : ℕ => C*K*Real.exp (-(1/2500:ℝ)*(P:ℝ)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (ppt_natural_exponential_tendsto (by norm_num : (0:ℝ) < 1/2500)).const_mul (C*K)
    convert hh using 1
    ext P
    congr 2
    ring
  filter_upwards [hlim.eventually (eventually_lt_nhds hε),eventually_ge_atTop (1:ℕ)]
    with P hsmall hP
  filter_upwards [hcount,hupper,scale_eventually_pos,
    m_tendsto.eventually (eventually_gt_atTop P)] with x hx hu hn hm
  calc
    _ ≤ C*V x*Real.exp (-(P:ℝ)/2500) := hx P (by omega) hm
    _ ≤ C*(K*tupleNormalization x)*Real.exp (-(P:ℝ)/2500) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hC.le) (Real.exp_pos _).le
    _ = (C*K*Real.exp (-(P:ℝ)/2500))*tupleNormalization x := by ring
    _ ≤ ε*tupleNormalization x := mul_le_mul_of_nonneg_right hsmall.le hn.le

end TotientAsymptotic

end

end OAI
