import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.WeakFourierDerivative

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology SchwartzMap FourierTransform ComplexConjugate ContDiff
noncomputable section
namespace Coulomb
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma l1_l2_fourier_ae (u:Lp ℂ 2 (volume:Measure E)) (hu:Integrable (u:E → ℂ)) :
    (𝓕 u : Lp ℂ 2 (volume:Measure E)) =ᵐ[volume] 𝓕 (u:E → ℂ) := by
  have hf : Continuous (𝓕 (u:E → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hu
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 u : Lp ℂ 2 (volume:Measure E))).locallyIntegrable (by norm_num))
    hf.locallyIntegrable
  intro φ hφ hc
  let χ:E → ℂ := fun x => (φ x:ℂ)
  have hχ:ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp hφ
  have hcχ:HasCompactSupport χ := hc.comp_left (g:=fun r:ℝ => (r:ℂ)) (by simp)
  let Φ:𝓢(E,ℂ) := hcχ.toSchwartzMap hχ
  have h := congrArg (fun T:𝓢'(E,ℂ) => T Φ) (Lp.fourier_toTemperedDistribution_eq u)
  simp only [TemperedDistribution.fourier_apply,Lp.toTemperedDistribution_apply,smul_eq_mul] at h
  have hi := VectorFourier.integral_fourierIntegral_smul_eq_flip (L:=innerₗ E) (μ:=volume) (ν:=volume)
    Real.continuous_fourierChar continuous_inner Φ.integrable hu
  calc
    _ = ∫ x,Φ x * (𝓕 u : Lp ℂ 2 (volume:Measure E)) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Φ,χ,HasCompactSupport.toSchwartzMap_toFun,Complex.real_smul]
    _ = ∫ x,(𝓕 Φ) x * u x := h.symm
    _ = ∫ x,Φ x * 𝓕 (u:E → ℂ) x := by
      rw [SchwartzMap.fourier_coe]
      simpa using! hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Φ,χ,HasCompactSupport.toSchwartzMap_toFun,Complex.real_smul]
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ComplexConjugate
noncomputable section
namespace Coulomb
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma cutL2_integrable (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞)
    (u:Lp ℂ 2 (volume:Measure E)) : Integrable (cutL2 s hs u : E → ℂ) := by
  have h := L2.integrable_inner (𝕜:=ℂ) (indicatorConstLp 2 hs hμ (1:ℂ)) u
  apply h.congr
  filter_upwards [indicatorConstLp_coeFn (p:=2) (hs:=hs) (hμs:=hμ) (c:=(1:ℂ)),cutL2_ae s hs u] with x h1 h2
  rw [h1,h2]
  by_cases hx:x∈s <;> simp [hx]

def fourierPlane (s:Set E) (ξ:E) : E → ℂ :=
  s.indicator (fun x => conj (Real.fourierChar (-inner ℝ x ξ):ℂ))
lemma fourierPlane_memLp (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞) (ξ:E) :
    MemLp (fourierPlane s ξ) 2 volume := by
  apply (memLp_indicator_const 2 hs (1:ℂ) (Or.inr hμ)).mono
  · apply AEStronglyMeasurable.indicator _ hs
    exact (Complex.continuous_conj.comp (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg))).aestronglyMeasurable
  · filter_upwards [] with x
    by_cases hx:x∈s <;> simp [fourierPlane,hx,Circle.norm_coe]
def fourierPlaneL2 (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞) (ξ:E) :
    Lp ℂ 2 (volume:Measure E) := (fourierPlane_memLp s hs hμ ξ).toLp (fourierPlane s ξ)
lemma fourierPlaneL2_ae (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞) (ξ:E) :
    fourierPlaneL2 s hs hμ ξ =ᵐ[volume] fourierPlane s ξ := MemLp.coeFn_toLp _
lemma fourierPlaneL2_norm (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞) (ξ:E) :
    ‖fourierPlaneL2 s hs hμ ξ‖ ≤ ‖indicatorConstLp 2 hs hμ (1:ℂ)‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [fourierPlaneL2_ae s hs hμ ξ,
    indicatorConstLp_coeFn (p:=2) (hs:=hs) (hμs:=hμ) (c:=(1:ℂ))] with x h1 h2
  rw [h1,h2]
  by_cases hx:x∈s <;> simp [fourierPlane,hx,Circle.norm_coe]
lemma fourier_cut_inner (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞)
    (u:Lp ℂ 2 (volume:Measure E)) (ξ:E) :
    𝓕 (cutL2 s hs u:E → ℂ) ξ=inner ℂ (fourierPlaneL2 s hs hμ ξ) u := by
  rw [Real.fourier_eq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fourierPlaneL2_ae s hs hμ ξ,cutL2_ae s hs u] with x h1 h2
  rw [h1,h2]
  by_cases hx:x∈s <;> simp [fourierPlane,hx,Circle.smul_def,mul_comm]
lemma fourier_cut_weak_tendsto (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞)
    (u:ℕ → Lp ℂ 2 (volume:Measure E)) (v:Lp ℂ 2 (volume:Measure E))
    (hw:∀ w,Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v))) (ξ:E) :
    Tendsto (fun n => 𝓕 (cutL2 s hs (u n):E → ℂ) ξ) atTop
      (𝓝 (𝓕 (cutL2 s hs v:E → ℂ) ξ)) := by
  simp_rw [fourier_cut_inner s hs hμ]
  exact hw _
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ComplexConjugate
noncomputable section
namespace Coulomb
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma fourier_cut_norm_bound (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞)
    (u:Lp ℂ 2 (volume:Measure E)) (ξ:E) :
    ‖𝓕 (cutL2 s hs u:E → ℂ) ξ‖ ≤ ‖indicatorConstLp 2 hs hμ (1:ℂ)‖*‖u‖ := by
  rw [fourier_cut_inner s hs hμ]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (fourierPlaneL2_norm s hs hμ ξ) (norm_nonneg u))

lemma fourier_double_cut_tendsto (s t:Set E) (hs:MeasurableSet s) (ht:MeasurableSet t)
    (hμ:volume s≠∞) (hν:volume t≠∞)
    (u:ℕ → Lp ℂ 2 (volume:Measure E)) (v:Lp ℂ 2 (volume:Measure E))
    (C:ℝ) (hb:∀ n,‖u n‖≤C)
    (hw:∀ w,Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v))) :
    Tendsto (fun n => cutL2 t ht (𝓕 (cutL2 s hs (u n)))) atTop
      (𝓝 (cutL2 t ht (𝓕 (cutL2 s hs v)))) := by
  let A:ℝ := ‖indicatorConstLp 2 hs hμ (1:ℂ)‖
  let B:ℝ := A*(C+‖v‖)
  have hC:0≤C := (norm_nonneg (u 0)).trans (hb 0)
  have hA:0≤A := norm_nonneg _
  have hB:0≤B := mul_nonneg hA (add_nonneg hC (norm_nonneg v))
  let f:ℕ → E → ℂ := fun n ξ => 𝓕 (cutL2 s hs (u n):E → ℂ) ξ - 𝓕 (cutL2 s hs v:E → ℂ) ξ
  have hf (n:ℕ) : Continuous (f n) :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (cutL2_integrable s hs hμ (u n))).sub
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (cutL2_integrable s hs hμ v))
  have hfb (n:ℕ) (ξ:E) : ‖f n ξ‖≤B := by
    calc
      _≤‖𝓕 (cutL2 s hs (u n):E → ℂ) ξ‖+‖𝓕 (cutL2 s hs v:E → ℂ) ξ‖ := norm_sub_le _ _
      _≤A*‖u n‖+A*‖v‖ := add_le_add (fourier_cut_norm_bound s hs hμ _ _) (fourier_cut_norm_bound s hs hμ _ _)
      _≤A*C+A*‖v‖ := add_le_add (mul_le_mul_of_nonneg_left (hb n) hA) (le_refl _)
      _=B := by dsimp [B]; ring
  let : IsFiniteMeasure (volume.restrict t : Measure E) := ⟨by simpa using hν.lt_top⟩
  have hlim : Tendsto (fun n => ∫ ξ in t,‖f n ξ‖^2) atTop (𝓝 (0:ℝ)) := by
    have H := tendsto_integral_of_dominated_convergence (μ:=volume.restrict t)
      (F:=fun n ξ => ‖f n ξ‖^2) (f:=fun _ => (0:ℝ)) (fun _ => B^2)
      (fun n => ((hf n).norm.pow 2).aestronglyMeasurable) (integrable_const _)
      (fun n => Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hfb n ξ) _))
      (Filter.Eventually.of_forall (fun ξ => by
        have h := (fourier_cut_weak_tendsto s hs hμ u v hw ξ).sub_const
          (𝓕 (cutL2 s hs v:E → ℂ) ξ)
        simpa [f] using h.norm.pow 2))
    simpa using H
  have he (n:ℕ) :
      ‖cutL2 t ht (𝓕 (cutL2 s hs (u n)))-cutL2 t ht (𝓕 (cutL2 s hs v))‖^2
        =∫ ξ in t,‖f n ξ‖^2 := by
    rw [←cutL2_sub,cutL2_norm_sq]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (𝓕 (cutL2 s hs (u n))) (𝓕 (cutL2 s hs v))),
      ae_restrict_of_ae (l1_l2_fourier_ae _ (cutL2_integrable s hs hμ (u n))),
      ae_restrict_of_ae (l1_l2_fourier_ae _ (cutL2_integrable s hs hμ v))] with ξ h1 h2 h3
    simp only [h1,Pi.sub_apply,h2,h3,f]
  have hl := hlim.congr' (Filter.Eventually.of_forall fun n => (he n).symm)
  have hn := (Real.continuous_sqrt.tendsto (0:ℝ)).comp hl
  simp only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn
end Coulomb
end

end

end OAI
