import OAI.NumberTheory.DirichletL.Reflection.SurvivingEnergy

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

lemma reciprocal_annulus_normalization (r Qn Qb kn kb : ℝ)
    (hr : 0<r) (hn : 0<Qn) (hb : 0<Qb) (hkn : 0<kn) (hkb : 0<kb) :
    1/(r*Real.sqrt Qn*Qb) = Real.sqrt kn*kb/(r*Real.sqrt (kn*Qn)*(kb*Qb)) := by
  rw [Real.sqrt_mul hkn.le]
  have hs : Real.sqrt kn≠0 := (Real.sqrt_pos.mpr hkn).ne'
  field_simp

theorem physical_scalar_extracted (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r Qn Qb kn kb R A : ℝ)
    (hr : 0<r) (hn : 0<Qn) (hb : 0<Qb) (hkn : 0<kn) (hkb : 0<kb) :
    A/(r*Real.sqrt Qn*Qb)*smallScalar R =
      (A*Real.sqrt kn*kb)*extractedOutsideScalar F jF e r
        (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))
        (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)) R := by
  have hp (v : Fin 3) : (Ideal.absNorm (frozenExtracted F jF e v):ℝ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v)
  unfold extractedOutsideScalar
  rw [mul_div_cancel₀ _ (hp 1),mul_div_cancel₀ _ (hp 2)]
  have h := reciprocal_annulus_normalization r Qn Qb kn kb hr hn hb hkn hkb
  calc
    _ = A*(1/(r*Real.sqrt Qn*Qb))*smallScalar R := by ring
    _ = _ := by rw [h]; ring

theorem annular_kernel_threshold (Z T tau C r QK QP Qn Qb kn kb D1 D2 : ℝ)
    (hT : 0<T) (htau : 0<tau) (hC : 0<C) (hr : 0<r)
    (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkn : 0<kn) (hkb : 0<kb) (h1 : 0<D1) (h2 : 0<D2) :
    Real.logb Z (kn*Qn/D1)+3*Real.logb Z (kb*Qb/D2)+3*Real.logb Z r-
      Real.logb Z (kernelCenter (T/(27*tau^2*C^2)*r^3) QK QP Qn Qb) =
    Real.logb Z (27*tau^2*C^2*QK^2*QP^2*kn*kb^3/(T*D1*D2^3)) := by
  have hR : 0<kernelCenter (T/(27*tau^2*C^2)*r^3) QK QP Qn Qb := by
    unfold kernelCenter
    positivity
  have hv : 0<kn*Qn/D1 := by positivity
  have hl : 0<kb*Qb/D2 := by positivity
  have heq : (kn*Qn/D1)*(kb*Qb/D2)^3*r^3 /
      kernelCenter (T/(27*tau^2*C^2)*r^3) QK QP Qn Qb =
      27*tau^2*C^2*QK^2*QP^2*kn*kb^3/(T*D1*D2^3) := by
    unfold kernelCenter
    field_simp
  rw [← heq,Real.logb_div (by positivity) hR.ne',
    Real.logb_mul (by positivity) (pow_ne_zero _ hr.ne'),
    Real.logb_mul hv.ne' (pow_ne_zero _ hl.ne'),Real.logb_pow,Real.logb_pow]
  norm_num

end
end SevenEighths.InverseReflectedPhase

end OAI
