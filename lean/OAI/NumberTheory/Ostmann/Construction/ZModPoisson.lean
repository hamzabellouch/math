import OAI.NumberTheory.Ostmann.Construction.CRTCancellation
import OAI.NumberTheory.Ostmann.Construction.GeneralPeriodicPoisson

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Construction

theorem finEquiv_eq_natCast (Q : ℕ) [NeZero Q] (r : Fin Q) :
    ZMod.finEquiv Q r=((r:ℕ):ZMod Q) := by
  cases Q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ Q =>
    apply Fin.ext
    change r.val=r.val%(Q+1)
    exact (Nat.mod_eq_of_lt r.isLt).symm

theorem fourier_fin_eq_stdAddChar (Q : ℕ) [NeZero Q] (r : Fin Q) (s : ℤ) :
    fourier s (((r:ℝ)/Q:ℝ):UnitAddCircle) =
      ZMod.stdAddChar ((s:ZMod Q)*ZMod.finEquiv Q r) := by
  rw [finEquiv_eq_natCast]
  have hc : (s:ZMod Q)*((r:ℕ):ZMod Q)=((s*(r:ℕ):ℤ):ZMod Q) := by push_cast; rfl
  rw [hc,ZMod.stdAddChar_coe,fourier_coe_apply]
  push_cast
  congr 1
  ring

theorem finite_fourier_eq_dft (Q : ℕ) [NeZero Q] (F : ZMod Q → ℂ) (s : ℤ) :
    (∑ r : Fin Q,F (ZMod.finEquiv Q r)*fourier s (((r:ℝ)/Q:ℝ):UnitAddCircle)) =
      ZMod.dft F (-s:ZMod Q) := by
  simp_rw [fourier_fin_eq_stdAddChar]
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul,mul_neg,neg_neg]
  calc
    _ = ∑ z : ZMod Q,F z*ZMod.stdAddChar ((s:ZMod Q)*z) :=
      (ZMod.finEquiv Q).toEquiv.sum_comp _
    _ = _ := by apply Finset.sum_congr rfl; intro z hz; rw [mul_comm z,mul_comm]

theorem zmod_scaled_poisson (Q : ℕ) [NeZero Q] (ψ : SchwartzMap ℝ ℂ)
    (F : ZMod Q → ℂ) {X : ℝ} (hX : 0<X) :
    (∑' n : ℤ,F (n:ZMod Q)*ψ ((n:ℝ)/X)) =
      (X/(Q:ℝ):ℂ)*(∑' s : ℤ,ZMod.dft F (s:ZMod Q)*𝓕 ψ (-(s:ℝ)*X/Q)) := by
  have h := scaled_periodic_poisson_full Q ψ (fun r => F (ZMod.finEquiv Q r)) hX
  have ht (n : ℤ) : periodicResidueTest Q (fun r => F (ZMod.finEquiv Q r)) n=F (n:ZMod Q) := by
    simp only [periodicResidueTest,finEquiv_residue]
  simp_rw [ht,finite_fourier_eq_dft] at h
  rw [h]
  congr 1
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro s
  simp only [Equiv.neg_apply,neg_neg,Int.cast_neg]

end Ostmann.Construction

end

end OAI
