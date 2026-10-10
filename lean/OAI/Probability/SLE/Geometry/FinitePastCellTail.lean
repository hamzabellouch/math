import OAI.Probability.SLE.Geometry.FiniteCellTailKernel
import OAI.Probability.SLE.Geometry.FinitePastEvents

namespace OAI

/-! A positive mass test strictly before a finite radius frontier forces
the corresponding canonical cell mass test at the frontier. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

lemma CanonicalMass.finite_strict_past_le_cell_test
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G) (Q : Measure Ω) (hQP : Q.AbsolutelyContinuous P)
    (T : Ω → WithTop ℝ≥0) (hT : ∀ᵐ ω ∂Q, T ω≠⊤)
    (J : Finset ℝ≥0) (K : Set ℂ) (H : ℝ) :
    Q (finiteStrictPastEvent J (fun t => {ω | H<(C.process t ω (Subtype.val ⁻¹' K)).toReal}) T) ≤
      Q (C.finiteCellMassTest T K (ENNReal.ofReal H)) := by
  apply measure_mono_ae
  filter_upwards [hQP.ae_le C.paths,hT] with ω hp hf hω
  obtain ⟨t,_ht,hval,hbefore⟩ := mem_iUnion₂.mp hω
  have hf' := hf
  lift T ω to ℝ≥0 using hf with s hs
  have hts : t ≤ s := by
    apply WithTop.coe_le_coe.mp
    simpa only [hs] using hbefore.le
  have hmass := hp.monotone hts (Subtype.val ⁻¹' K)
  refine ⟨lt_top_iff_ne_top.mpr (hs ▸ hf'),?_⟩
  have htime : (T ω).untopD 0=s := by rw [← hs,WithTop.untopD_coe]
  rw [htime]
  exact (ENNReal.ofReal_le_ofReal hval.le).trans (ENNReal.ofReal_toReal_le.trans hmass)

end SLEExactGauge.Multipoint

end

end OAI
