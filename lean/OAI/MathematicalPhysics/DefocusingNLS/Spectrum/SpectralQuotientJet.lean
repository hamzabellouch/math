import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalJet
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! The exact exterior jet after dividing an outgoing column by the background profile. -/

namespace DefocusingNLS

noncomputable def spectralQuotientJet (ν : ℂ) (Y Q : ℝ → ℂ × ℂ) (r : ℝ) : ℂ × ℂ :=
  let y := Y (Real.log r)
  let q := Q (Real.log r)
  let A := Complex.exp (ν*(Real.log r : ℂ))
  (A*(y.1*q.1⁻¹),A/(r : ℂ)*((ν*y.1+y.2)*q.1⁻¹-y.1*q.2*(q.1⁻¹)^2))

theorem spectralQuotientJet_hasDerivAt (ν : ℂ) (Y Q : ℝ → ℂ × ℂ)
    (r : ℝ) (hr : 0 < r) (hq0 : (Q (Real.log r)).1 ≠ 0)
    (hY : HasDerivAt (fun t => (Y t).1) (Y (Real.log r)).2 (Real.log r))
    (hQ : HasDerivAt (fun t => (Q t).1) (Q (Real.log r)).2 (Real.log r)) :
    HasDerivAt (fun s => (spectralQuotientJet ν Y Q s).1)
      (spectralQuotientJet ν Y Q r).2 r := by
  let A := Complex.exp (ν*(Real.log r : ℂ))
  let y := Y (Real.log r)
  let q := Q (Real.log r)
  have hlog := Real.hasDerivAt_log hr.ne'
  have hA := (hlog.ofReal_comp.const_mul ν).cexp
  have hy : HasDerivAt (fun s => (Y (Real.log s)).1) (y.2/(r : ℂ)) r := by
    simpa only [Function.comp_def,Complex.real_smul,div_eq_mul_inv,Complex.ofReal_inv,mul_comm]
      using hY.scomp r hlog
  have hq : HasDerivAt (fun s => (Q (Real.log s)).1) (q.2/(r : ℂ)) r := by
    simpa only [Function.comp_def,Complex.real_smul,div_eq_mul_inv,Complex.ofReal_inv,mul_comm]
      using hQ.scomp r hlog
  have hd := hA.mul (hy.mul (hq.inv hq0))
  apply hd.congr_deriv
  change A*(ν*(r⁻¹ : ℝ))*(y.1*q.1⁻¹)+
    A*((y.2/(r : ℂ))*q.1⁻¹+y.1*(-(q.2/(r : ℂ))/q.1^2))=
      A/(r : ℂ)*((ν*y.1+y.2)*q.1⁻¹-y.1*q.2*(q.1⁻¹)^2)
  push_cast
  field_simp
  ring

theorem spectralQuotientJet_bounds (ν : ℂ) (Y Q : ℝ → ℂ × ℂ)
    (M K D r : ℝ) (hr : 0 < r)
    (hY : ‖Y (Real.log r)‖ ≤ M) (hQ : ‖((Q (Real.log r)).1)⁻¹‖ ≤ K)
    (hQ' : ‖(Q (Real.log r)).2‖ ≤ D) :
    ‖(spectralQuotientJet ν Y Q r).1‖ ≤ r^ν.re*(M*K) ∧
      ‖(spectralQuotientJet ν Y Q r).2‖ ≤
        r^(ν.re-1)*(((‖ν‖+1)*M)*K+M*D*K^2) := by
  have hnorm : ‖Complex.exp (ν*(Real.log r : ℂ))‖=r^ν.re := by
    rw [Complex.norm_exp,Real.rpow_def_of_pos hr]
    congr 1
    simp [Complex.mul_re,mul_comm]
  have hy := (norm_fst_le (Y (Real.log r))).trans hY
  have hyd := (norm_snd_le (Y (Real.log r))).trans hY
  have hM : 0 ≤ M := (norm_nonneg _).trans hY
  have hK : 0 ≤ K := (norm_nonneg _).trans hQ
  have hD : 0 ≤ D := (norm_nonneg _).trans hQ'
  constructor
  · change ‖Complex.exp (ν*(Real.log r : ℂ))*
      ((Y (Real.log r)).1*((Q (Real.log r)).1)⁻¹)‖ ≤ _
    rw [norm_mul,norm_mul,hnorm]
    gcongr
  · change ‖Complex.exp (ν*(Real.log r : ℂ))/(r : ℂ)*
      ((ν*(Y (Real.log r)).1+(Y (Real.log r)).2)*((Q (Real.log r)).1)⁻¹-
       (Y (Real.log r)).1*(Q (Real.log r)).2*(((Q (Real.log r)).1)⁻¹)^2)‖ ≤ _
    rw [norm_mul,norm_div,hnorm,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      Real.rpow_sub hr,Real.rpow_one]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ ‖(ν*(Y (Real.log r)).1+(Y (Real.log r)).2)*((Q (Real.log r)).1)⁻¹‖+
          ‖(Y (Real.log r)).1*(Q (Real.log r)).2*(((Q (Real.log r)).1)⁻¹)^2‖ := norm_sub_le _ _
      _ = ‖ν*(Y (Real.log r)).1+(Y (Real.log r)).2‖*‖((Q (Real.log r)).1)⁻¹‖+
          ‖(Y (Real.log r)).1‖*‖(Q (Real.log r)).2‖*‖((Q (Real.log r)).1)⁻¹‖^2 := by
        simp only [norm_mul,norm_pow]
      _ ≤ (‖ν‖*‖(Y (Real.log r)).1‖+‖(Y (Real.log r)).2‖)*
          ‖((Q (Real.log r)).1)⁻¹‖+
          ‖(Y (Real.log r)).1‖*‖(Q (Real.log r)).2‖*‖((Q (Real.log r)).1)⁻¹‖^2 := by
        gcongr
        exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ (‖ν‖*M+M)*K+M*D*K^2 := by gcongr
      _ = _ := by ring

end DefocusingNLS

end OAI
