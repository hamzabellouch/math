import Mathlib.Analysis.Calculus.Taylor
import OAI.MathematicalPhysics.Transonic.Exterior.BarrierCoeff

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorPolynomial
open Filter Set Polynomial PowerSeries
open scoped Topology ContDiff
lemma taylor_jet_littleO (n : ℕ) (f : ℝ → ℝ) (hf : ContDiffAt ℝ n f 0) :
    (fun x => f x-(PowerSeries.trunc (n+1) (SonicJet.jet f)).eval x)
      =o[𝓝 (0 : ℝ)] (fun x => x^n) := by
  obtain ⟨s,hs,hfs⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hs
  have hfb : ContDiffOn ℝ n f (Metric.ball 0 r) := hfs.mono hrs
  have h0 : (0 : ℝ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have ht := taylor_isLittleO (convex_ball (0 : ℝ) r) h0 hfb
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds _ hr)] at ht
  have heval (x : ℝ) : taylorWithinEval f n (Metric.ball 0 r) 0 x=
      (PowerSeries.trunc (n+1) (SonicJet.jet f)).eval x := by
    rw [taylor_within_apply]
    change (∑ k ∈ Finset.range (n+1), ((k.factorial : ℝ)⁻¹*(x-0)^k) •
      iteratedDerivWithin k f (Metric.ball 0 r) 0)=
        (PowerSeries.trunc (n+1) (SonicJet.jet f)).eval₂ (RingHom.id ℝ) x
    rw [PowerSeries.eval₂_trunc_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball h0,SonicJet.coeff_jet]
    simp only [RingHom.id_apply,sub_zero,smul_eq_mul,div_eq_mul_inv]
    ring
  simpa only [heval,sub_zero] using ht

/-- The nonresonant positive 74th source coefficient supplies the entry above
P73. This is not an assumed Taylor-tail sign. -/
lemma enters_above_trunc73 (f : ℝ → ℝ) (hf : ContDiffAt ℝ 74 f 0)
    (hp : 0<PowerSeries.coeff 74 (SonicJet.jet f)) :
    ∀ᶠ x in 𝓝 (0:ℝ), 0<x → (PowerSeries.trunc 74 (SonicJet.jet f)).eval x<f x := by
  let a := PowerSeries.coeff 74 (SonicJet.jet f)
  have ha : 0<a := hp
  have ht := (taylor_jet_littleO 74 f hf).bound (show (0:ℝ)<a/2 by positivity)
  filter_upwards [ht] with x hx
  intro hxp
  have hpoly : (PowerSeries.trunc 75 (SonicJet.jet f)).eval x=
      (PowerSeries.trunc 74 (SonicJet.jet f)).eval x+a*x^74 := by
    rw [show 75=Nat.succ 74 by rfl,PowerSeries.trunc_succ,Polynomial.eval_add,
      Polynomial.eval_monomial]
  have hrest : |f x-(PowerSeries.trunc 75 (SonicJet.jet f)).eval x|≤a/2*x^74 := by
    simpa only [Real.norm_eq_abs,abs_pow,abs_of_pos hxp] using hx
  rw [hpoly,abs_le] at hrest
  have hpow : 0<x^74 := pow_pos hxp _
  nlinarith [hrest.1,mul_pos ha hpow]
end SepticProfile.ExteriorPolynomial

end
end

end OAI
