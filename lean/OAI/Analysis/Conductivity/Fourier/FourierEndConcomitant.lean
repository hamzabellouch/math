import Mathlib
import OAI.Analysis.Conductivity.Fourier.AffineFourierField
import OAI.Analysis.Conductivity.Flux.TorusCrossFluxDecay

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatFourier_value_derivative_decay {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B gap : ℝ} (ha : ∀ h,|a h|≤B) (hg : 0≤gap)
    (hr : ∀ h,a h≠0 → gap≤torusRate s h) :
    ∃ C D : ℝ,0≤C ∧ 0≤D ∧ ∀ x : Coord3,1≤x 0 →
      ‖flatFourier s a phase x‖≤C*exp (-gap*(x 0-1)) ∧
      ‖fderiv ℝ (flatFourier s a phase) x (flatAxis 0)‖≤D*exp (-gap*(x 0-1)) := by
  obtain ⟨C,hC,hb⟩ := flatFourier_exponential_bound (phase:=phase) hs ha hg hr 0
  obtain ⟨D,hD,hd⟩ := flatFourier_exponential_bound (phase:=phase) hs ha hg hr 1
  refine ⟨C,D,hC,hD,fun x hx => ⟨?_,?_⟩⟩
  · simpa only [norm_iteratedFDeriv_zero] using hb x hx
  · have hh := (fderiv ℝ (flatFourier s a phase) x).le_opNorm (flatAxis 0)
    have hn : ‖flatAxis (0:Fin 3)‖=1 := by simp [flatAxis,Pi.norm_single]
    rw [hn,mul_one,←norm_iteratedFDeriv_one] at hh
    exact hh.trans (hd x hx)

theorem affine_fourier_cross_flux_zero {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a b pa pb : (Fin 2→ℤ)→ℝ} {Ba Bb ga gb t : ℝ}
    (ha : ∀ h,|a h|≤Ba) (hb : ∀ h,|b h|≤Bb) (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h) (hrb : ∀ h,b h≠0 → gb≤torusRate s h)
    (α β : ℝ) (ht : 0<t) :
    torusCellIntegral (2*Real.pi)
      (fun x => flatCrossFlux s (affineFourierField s a pa α β) (flatFourier s b pb) x 0) t=0 := by
  obtain ⟨C,D,hC,hD,hbd⟩ := flatFourier_value_derivative_decay (phase:=pa) hs ha hga.le hra
  obtain ⟨E,F,hE,hF,hbf⟩ := flatFourier_value_derivative_decay (phase:=pb) hs hb hgb.le hrb
  apply flatCrossFlux_zero_of_bounds
    (affineFourierField_smooth hs ha α β) (flatFourier_smooth hs hb)
    (affineFourierField_periodic s a pa α β) (flatFourier_angularPeriodic s b pb)
    (fun _ hx => affineFourierField_harmonic hs ha α β hx)
    (fun _ hx => flatFourier_harmonic hs hb hx)
    (A:=|α|) (B:=|β|+C) (C:=|α|+D) (D:=E) (E:=F)
    (abs_nonneg _) (add_nonneg (abs_nonneg _) hC) (add_nonneg (abs_nonneg _) hD)
    hE hF hgb ht
  intro x hx
  have hxp : 0<x 0 := lt_of_lt_of_le zero_lt_one hx
  have he : exp (-ga*(x 0-1))≤1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hga.le) (sub_nonneg.mpr hx))
  have h1 := (hbd x hx).1.trans (by simpa using mul_le_mul_of_nonneg_left he hC)
  have h2 := (hbd x hx).2.trans (by simpa using mul_le_mul_of_nonneg_left he hD)
  refine ⟨?_,?_,(hbf x hx).1,(hbf x hx).2⟩
  · change ‖α*x 0+β+flatFourier s a pa x‖≤_
    calc
      _ ≤ (‖α*x 0‖+‖β‖)+‖flatFourier s a pa x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ |α| *x 0+|β|+C := by
        simpa [norm_mul,Real.norm_eq_abs,abs_of_pos hxp] using add_le_add_left h1 (‖α*x 0‖+‖β‖)
      _ = _ := by ring
  · rw [affineFourierField_fderiv hs ha α β hxp]
    have heq : (α • (ContinuousLinearMap.proj 0 : Coord3→L[ℝ]ℝ)+fderiv ℝ (flatFourier s a pa) x) (flatAxis 0)=
        α+fderiv ℝ (flatFourier s a pa) x (flatAxis 0) := by simp [flatAxis]
    rw [heq]
    exact (norm_add_le _ _).trans (by simpa only [Real.norm_eq_abs] using add_le_add (le_refl |α|) h2)

end ScalarConductivity

end
end

end OAI
