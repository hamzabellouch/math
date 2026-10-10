import Mathlib
import OAI.Analysis.Conductivity.Sobolev.AttachedEndMatchedH1

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance smoothCollarTraceCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance smoothCollarTraceCircleIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def smoothCollarTraceFourier (b : ℝ) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) : SpectralL2 TorusModes :=
  (mFourierBasis (d:=Fin 2)).repr
    (ContinuousMap.toLp 2 volume ℂ
      ⟨fun θ => (q (sourceAngularCollar b θ):ℂ),
        Complex.continuous_ofReal.comp (hq.continuous.comp (continuous_sourceAngularCollar b))⟩)

lemma smoothCollarTraceFourier_apply (b : ℝ) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (h : TorusModes) :
    smoothCollarTraceFourier b hq h=mFourierCoeff (fun θ => (q (sourceAngularCollar b θ):ℂ)) h := by
  rw [smoothCollarTraceFourier,mFourierBasis_repr,mFourierCoeff_toLp]
  rfl

def smoothCollarTrace (s : Fin 3 → ℝ) (b : ℝ) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) : spectralTraceGraph (torusRate s) :=
  ((spectralTraceGraph_exists_iff (w:=torusRate s) (fun h => Real.sqrt_nonneg _) (smoothCollarTraceFourier b hq)).mpr
    (by simpa only [smoothCollarTraceFourier_apply] using sourceAngularTrace_summable s b hq)).choose

lemma smoothCollarTrace_fst (s : Fin 3 → ℝ) (b : ℝ) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (h : TorusModes) :
    (smoothCollarTrace s b hq).val 0 h=mFourierCoeff (fun θ => (q (sourceAngularCollar b θ):ℂ)) h := by
  have he := ((spectralTraceGraph_exists_iff (w:=torusRate s) (fun h => Real.sqrt_nonneg _) (smoothCollarTraceFourier b hq)).mpr
    (by simpa only [smoothCollarTraceFourier_apply] using sourceAngularTrace_summable s b hq)).choose_spec
  change (smoothCollarTrace s b hq).val 0=smoothCollarTraceFourier b hq at he
  rw [he,smoothCollarTraceFourier_apply]

lemma smoothCollarTrace_rate_memℓp (s : Fin 3 → ℝ) (b : ℝ) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) :
    Memℓp (fun h => (torusRate s h:ℂ)*(smoothCollarTrace s b hq).val 0 h) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,smoothCollarTrace_fst] using sourceAngularTrace_rate_sq_summable s b hq

theorem smoothCollarTrace_matched_H1 {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {q χ : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    {a b η : ℝ} (ha : a≠0) (hη : 0<η) (hl : -(1:ℝ)/100≤b-η) (hr : b+η≤1/100)
    (hχs : tsupport χ⊆sourceClosedCollarBand (b-η) (b+η)) :
    let f := smoothCollarTrace s b hq
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=cutMatchedValue (fun y => a*(sourceCollarTime y-b)) χ
        (fun y => (attachedEndPoissonField s f a b 0 y).re-q y) (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=cutMatchedGradient (fun y => a*(sourceCollarTime y-b)) χ
        (fun y => (attachedEndPoissonField s f a b 0 y).re-q y)
        (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y-fderiv ℝ q y)
        i (WithLp.ofLp x)) := by
  exact smooth_attachedEnd_matched_H1 hs _ hq hχ hc hχb ha hη hl hr hχs
    (smoothCollarTrace_fst s b hq)
    ⟨_,smoothCollarTrace_rate_memℓp s b hq⟩ (fun _ => rfl)

end ScalarConductivity

end

end OAI
