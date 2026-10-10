import OAI.MathematicalPhysics.Transonic.Exterior.BarrierCoeff
import OAI.MathematicalPhysics.Transonic.Exterior.BarrierTrace

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorPolynomial
open FixedInterval PowerSeries Polynomial

lemma reflectedTrunc_enclosed {Q : ℤ} (b : ℕ → Box) (mono : ℕ → Box)
    (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1) (d : ℝ)
    (hz : b 0=zero) (htail : ∀ n, 74≤n → b n=zero)
    (hsign : ∀ n, 1≤n → n≤73 → b n=signBox n (mono n))
    (hm : ∀ n, 1≤n → n≤73 → Holds Q (mono n)
      (PowerSeries.coeff n (ExteriorJet.scaledReflected u)*d^n)) :
    ∀ n, Holds Q (b n) (PowerSeries.coeff n (reflectedTrunc u d : PowerSeries ℝ)) := by
  intro n
  rw [Polynomial.coeff_coe]
  by_cases hn0 : n=0
  · subst n;rw [hz,reflectedTrunc_zero u hu0 d];exact holds_zero Q
  by_cases hn : n<74
  · rw [coeff_reflectedTrunc,ite_eq_left hn,hsign n (by omega) (by omega)]
    exact holds_signBox (hm n (by omega) (by omega)) n
  · rw [coeff_reflectedTrunc,ite_eq_right hn,htail n (by omega)];exact holds_zero Q

lemma residual_enclosed {Q : ℤ} (hQ : 0<Q) (a : ExteriorJet.BarrierWeights)
    (h sigma kappa c : ℝ) (ha : ExteriorJet.BarrierWeightsHold Q a h sigma kappa c)
    (tr : BarrierTrace.Trace) (hv : BarrierTrace.ValidPowers Q 8 73 tr)
    (w : ℝ[X]) (hw : w.natDegree≤73)
    (hu : ∀ n, Holds Q (tr.u n) (PowerSeries.coeff n (w : PowerSeries ℝ)))
    (hr : ∀ i, i<220 → tr.r i=ExteriorJet.barrierResidualBox Q a tr (i+72)) :
    ∀ i, i<220 → Holds Q (tr.r i) (-(residual h sigma kappa c w).coeff (i+74)) := by
  have hh := BarrierTrace.powers_enclosed hQ 8 73 (by norm_num) tr hv (w : PowerSeries ℝ) hu
    (fun n hn => by rw [Polynomial.coeff_coe];exact coeff_eq_zero_of_natDegree_lt (by omega))
  intro i hi
  rw [hr i hi]
  have he := ExteriorJet.barrierResidual_enclosed hQ a h sigma kappa c ha tr
    (w : PowerSeries ℝ) (i+72) hu hh.1 hh.2.1 hh.2.2
  rw [←coe_residual,Polynomial.coeff_coe] at he
  simpa only [Nat.add_assoc,show 72+2=74 by norm_num] using he

lemma lower_enclosed {Q : ℤ} (a b : ℕ → Box) (w : ℝ[X])
    (hw0 : w.coeff 0=0)
    (ha : ∀ n, Holds Q (a n) (PowerSeries.coeff n (w : PowerSeries ℝ)))
    (hb0 : b 0=ExteriorJet.oneBox Q)
    (hbn : ∀ n, n≠0 → b n=neg (a n)) :
    ∀ n, Holds Q (b n) ((1-w).coeff n) := by
  intro n
  rw [Polynomial.coeff_sub,Polynomial.coeff_one]
  by_cases hn : n=0
  · subst n;rw [ite_eq_left rfl,hw0,sub_zero,hb0];exact ExteriorJet.holds_oneBox Q
  · rw [ite_eq_right hn,zero_sub,hbn n hn]
    exact holds_neg (by simpa using ha n)

lemma lowerPoly_eval_scale (u : PowerSeries ℝ) (d x : ℝ) :
    (lowerPoly u d).eval x=(PowerSeries.trunc 74 u).eval (d/256*x) := by
  have hr : rescale (-d) (ExteriorJet.scaledReflected u)=1-rescale (d/256) u := by
    simp only [ExteriorJet.scaledReflected,ExteriorJet.reflected,map_sub,map_one,
      PowerSeries.rescale_rescale]
    congr 2
    ring_nf
  rw [lowerPoly,reflectedTrunc,hr,PowerSeries.trunc_sub,PowerSeries.trunc_one]
  norm_num only [show (74:ℕ)≠0 by decide,ite_false,sub_sub_cancel]
  change Polynomial.eval₂ (RingHom.id ℝ) x _=Polynomial.eval₂ (RingHom.id ℝ) (d/256*x) _
  rw [PowerSeries.eval₂_trunc_eq_sum_range,PowerSeries.eval₂_trunc_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [RingHom.id_apply,PowerSeries.coeff_rescale,mul_pow]
  ring

lemma eval_residual_lower (h sigma kappa c : ℝ) (w : ℝ[X]) (x : ℝ) :
    -(residual (-h) sigma kappa c w).eval x=
      (1+h*x)*(1-sigma*(1+h*x)^2)*(1-((1-w).eval x)^2)*
        deriv (fun t => (1-w).eval t) x-
      h*(1-c*((1-w).eval x)^2)*
        (kappa*(1+h*x)*(1-((1-w).eval x)^2)+3*((1+h*x)-(1-w).eval x)) := by
  have hd : deriv (fun t => (1-w).eval t) x=-(w.derivative.eval x) := by
    rw [Polynomial.deriv]
    simp
  rw [hd,eval_residual]
  simp only [Polynomial.deriv,Polynomial.eval_sub,Polynomial.eval_one]
  ring

end SepticProfile.ExteriorPolynomial

end
end

end OAI
