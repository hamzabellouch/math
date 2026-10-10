import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarLocalExistence
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarInitialBound

namespace OAI

/-! Wronskian duality turns a forward bound for all scalar solutions into a
reverse bound. The comparison basis is constructed, not assumed. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralScalarWronskian_eq (a b : ℝ) (hab : a≤ b) (V : ℝ → ℂ)
    (D U : ℝ → ℂ × ℂ) (hD : ContinuousOn D (Icc a b)) (hU : ContinuousOn U (Icc a b))
    (hDD : ∀ t ∈ Ioo a b, HasDerivAt D (spectralScalarField (V t) (D t)) t)
    (hUD : ∀ t ∈ Ioo a b, HasDerivAt U (spectralScalarField (V t) (U t)) t) :
    spectralScalarWronskian (D b) (U b)=spectralScalarWronskian (D a) (U a) := by
  have hc : ContinuousOn (fun t => spectralScalarWronskian (D t) (U t)) (Icc a b) :=
    (hD.fst.mul hU.snd).sub (hD.snd.mul hU.fst)
  have hd (t : ℝ) (ht : t ∈ Ioo a b) := spectralScalarWronskian_hasDerivAt D U (V t) t
    (hDD t ht) (hUD t ht)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hd
    (intervalIntegrable_const (c := (0 : ℂ)))
  simpa only [intervalIntegral.integral_zero,sub_eq_zero] using he.symm

theorem spectralScalarWronskian_coordinate_norm (k : ℝ) (hk : 0<k) (u : ℂ × ℂ) :
    spectralShellNorm k u=
      ‖spectralScalarWronskian u (0,(k : ℂ))‖+
      ‖spectralScalarWronskian ((k⁻¹ : ℂ),0) u‖ := by
  simp only [spectralShellNorm,spectralScalarWronskian,mul_zero,zero_mul,sub_zero,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk,norm_inv]
  ring

theorem spectralScalar_reverse_transfer (a b ka kb C : ℝ) (hab : a≤ b)
    (hka : 0<ka) (hkb : 0<kb) (V : ℝ → ℂ) (hV : ContinuousOn V (Icc a b))
    (hforward : ∀ u : ℝ → ℂ × ℂ, ContinuousOn u (Icc a b) →
      (∀ t ∈ Ioo a b, HasDerivAt u (spectralScalarField (V t) (u t)) t) →
      spectralShellNorm kb (u b)≤ C*spectralShellNorm ka (u a))
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc a b))
    (hqD : ∀ t ∈ Ioo a b, HasDerivAt q (spectralScalarField (V t) (q t)) t) :
    spectralShellNorm ka (q a)≤(2*C)*spectralShellNorm kb (q b) := by
  obtain ⟨D,hD,hDa,hDD⟩ := spectralScalar_local_exists a b hab V hV ((ka⁻¹ : ℂ),0)
  obtain ⟨U,hU,hUa,hUD⟩ := spectralScalar_local_exists a b hab V hV (0,(ka : ℂ))
  have hDD' (t : ℝ) (ht : t ∈ Ioo a b) := hDD t ⟨ht.1.le,ht.2.le⟩
  have hUD' (t : ℝ) (ht : t ∈ Ioo a b) := hUD t ⟨ht.1.le,ht.2.le⟩
  have hDnorm : spectralShellNorm ka (D a)=1 := by
    rw [hDa]
    simp only [spectralShellNorm,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hka,
      norm_zero,mul_zero,add_zero,mul_inv_cancel₀ hka.ne']
  have hUnorm : spectralShellNorm ka (U a)=1 := by
    rw [hUa]
    simp only [spectralShellNorm,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hka,
      norm_zero,mul_zero,zero_add,inv_mul_cancel₀ hka.ne']
  have hDb : spectralShellNorm kb (D b)≤ C := by simpa only [hDnorm,mul_one] using hforward D hD.continuousOn hDD'
  have hUb : spectralShellNorm kb (U b)≤ C := by simpa only [hUnorm,mul_one] using hforward U hU.continuousOn hUD'
  have hWqU := spectralScalarWronskian_eq a b hab V q U hq hU.continuousOn hqD hUD'
  have hWDq := spectralScalarWronskian_eq a b hab V D q hD.continuousOn hq hDD' hqD
  have hNq : 0≤ spectralShellNorm kb (q b) := spectralShellNorm_nonneg kb hkb.le _
  calc
    _ = ‖spectralScalarWronskian (q a) (U a)‖+‖spectralScalarWronskian (D a) (q a)‖ := by
      rw [hUa,hDa]
      exact spectralScalarWronskian_coordinate_norm ka hka (q a)
    _ = ‖spectralScalarWronskian (q b) (U b)‖+‖spectralScalarWronskian (D b) (q b)‖ := by rw [hWqU,hWDq]
    _ ≤ spectralShellNorm kb (q b)*spectralShellNorm kb (U b)+
        spectralShellNorm kb (D b)*spectralShellNorm kb (q b) :=
      add_le_add (spectralScalarWronskian_shell_bound kb hkb _ _)
        (spectralScalarWronskian_shell_bound kb hkb _ _)
    _ ≤ spectralShellNorm kb (q b)*C+C*spectralShellNorm kb (q b) :=
      add_le_add (mul_le_mul_of_nonneg_left hUb hNq) (mul_le_mul_of_nonneg_right hDb hNq)
    _ = _ := by ring

end DefocusingNLS

end OAI
