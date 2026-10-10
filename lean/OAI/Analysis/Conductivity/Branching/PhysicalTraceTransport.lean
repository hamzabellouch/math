import Mathlib
import OAI.Analysis.Conductivity.Sobolev.ChildH1Pullback
import OAI.Analysis.Conductivity.Variational.PhysicalTraceMean

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
local instance physicalTraceTransportMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalTraceTransportProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma physicalRealTrace_child (k : Fin 2) (u : H1) :
    physicalRealTraceCLM k.succ u=physicalRealTraceCLM 0 (childH1Pullback k u) := by
  have hc : IsClosed {u : H1 | physicalRealTraceCLM k.succ u=
      physicalRealTraceCLM 0 (childH1Pullback k u)} :=
    isClosed_eq (physicalRealTraceCLM k.succ).continuous
      ((physicalRealTraceCLM 0).continuous.comp (childH1Pullback k).continuous)
  apply (closure_minimal (s:={u : H1 | u.val∈smoothJets}) ?_ hc) (smoothH1_dense u)
  rintro v ⟨f,hf,_,he⟩
  have hv : v=smoothH1 f hf := Subtype.ext he
  change physicalRealTraceCLM k.succ v=physicalRealTraceCLM 0 (childH1Pullback k v)
  rw [hv,childH1Pullback_smooth]
  apply Lp.ext
  filter_upwards [physicalRealTrace_smooth_ae k.succ hf,
    physicalRealTrace_smooth_ae 0 (hf.comp (sourceChildEuclidean_contDiff (actualChildSign k)))] with θ h1 h0
  exact h1.trans h0.symm

def sourceMeanCLM (i : Fin 3) : H1 →L[ℝ] ℝ :=
  (Complex.reCLM.comp ((lp.evalCLM ℂ (fun _ : TorusModes => ℂ) 2 0).restrictScalars ℝ)).comp
    (physicalOuterTraceCLM i)

lemma sourceMean_eq_integral (i : Fin 3) (u : H1) :
    sourceMeanCLM i u=∫ θ,physicalRealTraceCLM i u θ := (physicalRealTrace_mean i u).symm

lemma sourceMean_child (k : Fin 2) (u : H1) :
    sourceMeanCLM k.succ u=sourceMeanCLM 0 (childH1Pullback k u) := by
  rw [sourceMean_eq_integral,sourceMean_eq_integral,physicalRealTrace_child]

lemma basisFlux_mean (j : Fin 2) (u : H1) :
    constantTerminalFluxCLM (centralBasisSlopes j) u=
      angularArea*(sourceMeanCLM j.succ u-sourceMeanCLM 0 u) := by
  rw [constantTerminalFlux_realTrace]
  simp only [←sourceMean_eq_integral]
  rw [Fin.sum_univ_three]
  fin_cases j
  · change angularArea*((-1)*sourceMeanCLM 0 u+1*sourceMeanCLM 1 u+0*sourceMeanCLM 2 u)=angularArea*(sourceMeanCLM 1 u-sourceMeanCLM 0 u)
    ring
  · change angularArea*((-1)*sourceMeanCLM 0 u+0*sourceMeanCLM 1 u+1*sourceMeanCLM 2 u)=angularArea*(sourceMeanCLM 2 u-sourceMeanCLM 0 u)
    ring

lemma physicalRealTrace_bound (i : Fin 3) (u : H1) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue u x)≤M) :
    ∀ᵐ θ : UnitAddTorus (Fin 2),abs (physicalRealTraceCLM i u θ)≤M := by
  have hh := physicalRealTrace_upper_bound i u hM (hb.mono (fun _ h => (abs_le.mp h).2))
  have hn : ∀ᵐ x∂ballMeasure,weakValue (-u) x≤M := by
    filter_upwards [hb,weakValue_neg u] with x hx hn
    rw [hn,Pi.neg_apply]
    linarith [(abs_le.mp hx).1]
  have hh' := physicalRealTrace_upper_bound i (-u) hM hn
  rw [map_neg] at hh'
  filter_upwards [hh,hh',Lp.coeFn_neg (physicalRealTraceCLM i u)] with θ h0 h1 hn
  rw [hn,Pi.neg_apply] at h1
  exact abs_le.mpr ⟨by linarith,h0⟩

lemma sourceMean_bound (i : Fin 3) (u : H1) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x∂ballMeasure,abs (weakValue u x)≤M) : abs (sourceMeanCLM i u)≤M := by
  rw [sourceMean_eq_integral]
  have hh : ∀ᵐ θ,‖physicalRealTraceCLM i u θ‖≤M := by
    simpa only [Real.norm_eq_abs] using physicalRealTrace_bound i u hM hb
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using norm_integral_le_of_norm_le_const hh

end ScalarConductivity

end

end OAI
