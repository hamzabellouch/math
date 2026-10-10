import OAI.MathematicalPhysics.Transonic.Exterior.Certificate
import OAI.MathematicalPhysics.Transonic.Exterior.FastRange

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorPolynomial
open FixedInterval ExteriorJet PowerSeries Polynomial Set

lemma lower_eval_horner (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1) (d x : ℝ) :
    (lowerPoly u d).eval x=1+x*hornerValue (fun j => (lowerPoly u d).coeff j) x 1 73 := by
  have hdeg : (lowerPoly u d).natDegree<74 := by
    have hh := reflectedTrunc_natDegree u d
    unfold lowerPoly
    compute_degree!
    omega
  have hz : (lowerPoly u d).coeff 0=1 := by
    simp only [lowerPoly,Polynomial.coeff_sub,Polynomial.coeff_one,ite_true,
      reflectedTrunc_zero u hu0 d,sub_zero]
  rw [Polynomial.eval_eq_sum_range' hdeg,show 74=73+1 by norm_num,
    Finset.sum_range_succ',hornerValue_sum,Finset.mul_sum,hz]
  simp only [pow_zero,mul_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_succ,Nat.add_comm 1 j]
  ring

structure AdmissibleWindow (sigma kappa d : ℝ) (u : PowerSeries ℝ) : Prop where
  dpos : 0<d
  subsonic : sigma*(1+d/256)^2<1
  range : ∀ x∈Ioc (0:ℝ) 1, 1<(lowerPoly u d).eval x ∧ (lowerPoly u d).eval x<6/5
  strict : ∀ x∈Ioc (0:ℝ) 1,
    0 < -(residual (-d/256) sigma kappa (3/5) (reflectedTrunc u d)).eval x
  exit : 0<(lowerPoly u d).eval 1-(1+d/256)+
    (3/7*(1-kappa))*(1+d/256)*(1-((lowerPoly u d).eval 1)^2)

end SepticProfile.ExteriorPolynomial
namespace SepticProfile.ExteriorCertificates
open FixedInterval ExteriorJet PowerSeries Polynomial Set ExteriorPolynomial

lemma window_sound {Q : ℤ} (hQ : 0<Q) (jt : NormalizedTrace.Trace) (sig kap : Box)
    (W : WindowData) (hv : WindowValid Q jt sig kap W)
    (sigma kappa d : ℝ) (u : PowerSeries ℝ)
    (hsig : Holds Q sig sigma) (hkap : Holds Q kap kappa)
    (hu0 : PowerSeries.coeff 0 u=1) (he : Formal.residual sigma kappa (3/5) u=0)
    (hd : 0<d) (hroot : Holds Q W.root d)
    (hm : ∀ j, 1≤j → j≤73 → Holds Q (W.mono j) (PowerSeries.coeff j (scaledReflected u)*d^j)) :
    AdmissibleWindow sigma kappa d u := by
  let w := reflectedTrunc u d
  let P := lowerPoly u d
  have hw0 : w.coeff 0=0 := reflectedTrunc_zero u hu0 d
  have hw : ∀ j, Holds Q (W.trace.u j) (PowerSeries.coeff j (w : PowerSeries ℝ)) :=
    reflectedTrunc_enclosed W.trace.u W.mono u hu0 d hv.signed_zero hv.signed_tail hv.signed_eq hm
  have hp : ∀ j, Holds Q (W.poly j) (P.coeff j) :=
    lower_enclosed W.trace.u W.poly w hw0 hw hv.poly_zero hv.poly_eq
  have ha : BarrierWeightsHold Q W.weights (-d/256) sigma kappa (3/5) := by
    rw [hv.weights_eq];exact exteriorWeights_hold hQ hsig hkap hroot
  have hr : ∀ i, i<220 → Holds Q (W.trace.r i)
      (-(residual (-d/256) sigma kappa (3/5) w).coeff (i+74)) :=
    residual_enclosed hQ W.weights (-d/256) sigma kappa (3/5) ha W.trace hv.powers w
      (reflectedTrunc_natDegree u d) hw hv.residual_eq
  have hpend : Holds Q W.pend (P.eval 1) := by
    rw [hv.pend_eq]
    have hh := holds_horner hQ W.poly (fun j => P.coeff j) (oneBox Q) 1 (holds_oneBox Q) 0 74
      (fun j _ _ => hp j)
    rw [hornerValue_sum] at hh
    have hdeg : P.natDegree<74 := by
      have hh := reflectedTrunc_natDegree u d
      dsimp [P,lowerPoly]
      compute_degree!
      omega
    simpa only [Nat.zero_add,← Polynomial.eval_eq_sum_range' hdeg] using hh
  have hzend : Holds Q W.zend (1+d/256) := by
    rw [hv.zend_eq]
    convert holds_add (holds_oneBox Q) (holds_scale (a:=1) (b:=256) (by norm_num) hroot) using 1; norm_num; ring
  have hbeta : Holds Q W.betaquot (3/7*(1-kappa)) := by
    rw [hv.betaquot_eq]
    exact holds_scale (by norm_num) (holds_sub (holds_oneBox Q) hkap)
  have hc : Holds Q W.crit (P.eval 1-(1+d/256)+(3/7*(1-kappa))*(1+d/256)*(1-(P.eval 1)^2)) := by
    rw [hv.crit_eq]
    simpa only [pow_two] using holds_add (holds_sub hpend hzend)
      (holds_mul hQ (holds_mul hQ hbeta hzend) (holds_sub (holds_oneBox Q) (holds_mul hQ hpend hpend)))
  have hs : Holds Q W.subsonic (1-sigma*(1+d/256)^2) := by
    rw [hv.subsonic_eq]
    simpa only [pow_two] using holds_sub (holds_oneBox Q) (holds_mul hQ hsig (holds_mul hQ hzend hzend))
  refine ⟨hd,?_,?_,?_,enclosed_pos hQ hc hv.crit_pos⟩
  · linarith [enclosed_pos hQ hs hv.subsonic_pos]
  · intro x hx
    obtain ⟨cell,rb,pb,hcell,hrb,hpb,hrpos,hppos,hpup⟩ := hv.panels x ⟨hx.1.le,hx.2⟩
    have hpe := holds_horner hQ W.poly (fun j => P.coeff j) cell x hcell 1 73
      (fun j _ _ => hp j)
    rw [← hpb] at hpe
    have hpp := enclosed_pos hQ hpe hppos
    have hQC : (0:ℝ)<Q := by exact_mod_cast hQ
    have hpu : hornerValue (fun j => P.coeff j) x 1 73<1/5 := by
      have hb := (bounds hpe).2
      have hup : 5*((pb.center:ℝ)+pb.radius)<Q := by exact_mod_cast hpup
      nlinarith
    rw [lower_eval_horner u hu0 d x]
    change 1<1+x*hornerValue (fun j => P.coeff j) x 1 73 ∧
      1+x*hornerValue (fun j => P.coeff j) x 1 73<6/5
    constructor
    · linarith [mul_pos hx.1 hpp]
    · have hh := mul_le_mul_of_nonneg_right hx.2 hpp.le
      nlinarith
  · intro x hx
    obtain ⟨cell,rb,pb,hcell,hrb,hpb,hrpos,hppos,hpup⟩ := hv.panels x ⟨hx.1.le,hx.2⟩
    have hre := holds_horner hQ W.trace.r
      (fun i => -(residual (-d/256) sigma kappa (3/5) w).coeff (i+74)) cell x hcell 0 220
      (fun j hj hj' => hr j (by omega))
    rw [← hrb] at hre
    rw [residual_neg_eval sigma kappa d u hu0 he x]
    exact mul_pos (pow_pos hx.1 _) (enclosed_pos hQ hre hrpos)

end SepticProfile.ExteriorCertificates

end
end

end OAI
