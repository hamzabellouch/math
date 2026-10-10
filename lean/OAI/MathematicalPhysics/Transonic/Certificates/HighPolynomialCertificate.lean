import OAI.MathematicalPhysics.Transonic.Certificates.HighPlusCertificate
import OAI.MathematicalPhysics.Transonic.Certificates.HighMinusCertificate
import OAI.MathematicalPhysics.Transonic.Shooting.SonicContinuationLink

namespace OAI

section

namespace SepticProfile.HighPolynomialCertificate
open Polynomial FixedInterval

lemma jet_enclosed (f : PowerSeries ℝ) (hf0 : PowerSeries.coeff 0 f=1)
    (hf1 : PowerSeries.coeff 1 f= -(-500*(FixedHighJet.a:ℝ))/500)
    (he : EulerFormal.residual FixedHighJet.sigma FixedHighJet.kappa (3/5) (1/500) f=0) :
    ∀ n≤220, Holds FixedHighJet.Q (FixedHighJet.w n) (PowerSeries.coeff n (f-1)) := by
  have h0 : PowerSeries.coeff 0 (f-1)=0 := by simp only [map_sub,PowerSeries.coeff_one,hf0,ite_true,sub_self]
  have h1 : PowerSeries.coeff 1 (f-1)=(FixedHighJet.a:ℝ) := by
    rw [map_sub,PowerSeries.coeff_one,ite_eq_right (by norm_num : (1:ℕ)≠0),sub_zero,hf1]
    ring
  apply FixedHighJet.coefficients_enclosed (f-1) h0 h1
  have hh : (1+(f-1):PowerSeries ℝ)=f := by abel
  rw [hh]
  simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using he

lemma plus_range (f : PowerSeries ℝ) (hf0 : PowerSeries.coeff 0 f=1)
    (hf1 : PowerSeries.coeff 1 f= -(-500*(FixedHighJet.a:ℝ))/500)
    (he : EulerFormal.residual FixedHighJet.sigma FixedHighJet.kappa (3/5) (1/500) f=0)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (5/6)) :
    1-t/50≤(EulerPolynomial.barrier f (1/1000)).eval t ∧
      (EulerPolynomial.barrier f (1/1000)).eval t≤1-t/500 := by
  have hbox := HighPlusBarrierTransfer.barrier_coefficients_enclosed f hf0 (jet_enclosed f hf0 hf1 he)
  apply HighPlusRange.velocity_range (EulerPolynomial.barrier f (1/1000))
    (EulerPolynomial.degree_barrier f (1/1000)) ?_ hbox ht.1 ht.2
  norm_num only [EulerPolynomial.coeff_barrier,hf0,show (0:ℕ)<221 by omega,
    show (0:ℕ)≠140 by omega,ite_true,ite_false,add_zero]

lemma plus_residual (f : PowerSeries ℝ) (hf0 : PowerSeries.coeff 0 f=1)
    (hf1 : PowerSeries.coeff 1 f= -(-500*(FixedHighJet.a:ℝ))/500)
    (he : EulerFormal.residual FixedHighJet.sigma FixedHighJet.kappa (3/5) (1/500) f=0)
    (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) (5/6)) :
    0<EulerFormal.profileResidual FixedHighJet.sigma FixedHighJet.kappa (3/5) (1/500)
      (fun x => (EulerPolynomial.barrier f (1/1000)).eval x) t := by
  let p := EulerPolynomial.barrier f (1/1000)
  let r := EulerPolynomial.residual FixedHighJet.sigma FixedHighJet.kappa (3/5) (1/500) p
  have hp : p.natDegree≤220 := EulerPolynomial.degree_barrier f (1/1000)
  have hr : r.natDegree≤881 := EulerPolynomial.degree_residual _ _ _ _ _ hp
  have hbox := HighPlusBarrierTransfer.barrier_coefficients_enclosed f hf0 (jet_enclosed f hf0 hf1 he)
  have hres (k : ℕ) (hk : 140≤k) (hk' : k≤881) :
      Holds FixedHighPlusBarrier.Q (FixedHighPlusBarrier.r k) (r.coeff k) := by
    have hcoef (n : ℕ) : Holds FixedHighPlusBarrier.Q (FixedHighPlusBarrier.u n)
        (PowerSeries.coeff n (p:PowerSeries ℝ)) := by
      rw [Polynomial.coeff_coe]
      dsimp only [p]
      exact hbox n
    have hh := FixedHighPlusBarrier.residual_coefficients_enclosed (p:PowerSeries ℝ) hcoef
      (fun n hn => by rw [Polynomial.coeff_coe];exact coeff_eq_zero_of_natDegree_lt (hp.trans_lt hn)) k hk hk'
    rw [show FixedHighPlusBarrier.sigma=FixedHighJet.sigma from rfl,
      show FixedHighPlusBarrier.kappa=FixedHighJet.kappa from rfl] at hh
    rw [show ((3/5 : ℚ) : ℝ) = 3/5 by norm_num,
      show ((1/500 : ℚ) : ℝ) = 1/500 by norm_num] at hh
    rw [← EulerPolynomial.coe_residual,Polynomial.coeff_coe] at hh
    dsimp only [r, p] at hh ⊢
    exact hh
  have hpositive := FixedHighPlusPositive.finite_positive
    (fun i => r.coeff (i+140)) (fun i hi => by
      rw [HighPlusBarrierTransfer.data_r i hi]
      exact hres (i+140) (by omega) (by omega)) ht.1.le ht.2
  have hzero : ∀ n<140, r.coeff n=0 := by
    dsimp only [r, p]
    exact EulerPolynomial.residual_lowzero _ _ _ _ f (1/1000) hf0 he
  change 0<EulerFormal.profileResidual FixedHighJet.sigma FixedHighJet.kappa (3/5) (1/500) (fun x => p.eval x) t
  rw [← EulerPolynomial.eval_residual]
  change 0<r.eval t
  rw [EulerPolynomial.eval_factor r hr hzero t]
  exact mul_pos (pow_pos ht.1 140) hpositive
lemma minus_range (f : PowerSeries ℝ) (hf0 : PowerSeries.coeff 0 f=1)
    (hf1 : PowerSeries.coeff 1 f= -(-500*(FixedHighJet.a:ℝ))/500)
    (he : EulerFormal.residual FixedHighJet.sigma FixedHighJet.kappa (3/5) (1/500) f=0)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (5/6)) :
    1-t/50≤(EulerPolynomial.barrier f (-(1/1000))).eval t ∧
      (EulerPolynomial.barrier f (-(1/1000))).eval t≤1-t/500 := by
  have hbox := HighMinusBarrierTransfer.barrier_coefficients_enclosed f hf0 (jet_enclosed f hf0 hf1 he)
  apply HighMinusRange.velocity_range (EulerPolynomial.barrier f (-(1/1000)))
    (EulerPolynomial.degree_barrier f (-(1/1000))) ?_ hbox ht.1 ht.2
  norm_num only [EulerPolynomial.coeff_barrier,hf0,show (0:ℕ)<221 by omega,
    show (0:ℕ)≠140 by omega,ite_true,ite_false,add_zero]

lemma minus_residual (f : PowerSeries ℝ) (hf0 : PowerSeries.coeff 0 f=1)
    (hf1 : PowerSeries.coeff 1 f= -(-500*(FixedHighJet.a:ℝ))/500)
    (he : EulerFormal.residual FixedHighJet.sigma FixedHighJet.kappa (3/5) (1/500) f=0)
    (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) (5/6)) :
    EulerFormal.profileResidual FixedHighJet.sigma FixedHighJet.kappa (3/5) (1/500)
      (fun x => (EulerPolynomial.barrier f (-(1/1000))).eval x) t<0 := by
  let p := EulerPolynomial.barrier f (-(1/1000))
  let r := EulerPolynomial.residual FixedHighJet.sigma FixedHighJet.kappa (3/5) (1/500) p
  have hp : p.natDegree≤220 := EulerPolynomial.degree_barrier f (-(1/1000))
  have hr : r.natDegree≤881 := EulerPolynomial.degree_residual _ _ _ _ _ hp
  have hbox := HighMinusBarrierTransfer.barrier_coefficients_enclosed f hf0 (jet_enclosed f hf0 hf1 he)
  have hres (k : ℕ) (hk : 140≤k) (hk' : k≤881) :
      Holds FixedHighMinusBarrier.Q (FixedHighMinusBarrier.r k) (r.coeff k) := by
    have hcoef (n : ℕ) : Holds FixedHighMinusBarrier.Q (FixedHighMinusBarrier.u n)
        (PowerSeries.coeff n (p:PowerSeries ℝ)) := by
      rw [Polynomial.coeff_coe]
      dsimp only [p]
      exact hbox n
    have hh := FixedHighMinusBarrier.residual_coefficients_enclosed (p:PowerSeries ℝ) hcoef
      (fun n hn => by rw [Polynomial.coeff_coe];exact coeff_eq_zero_of_natDegree_lt (hp.trans_lt hn)) k hk hk'
    rw [show FixedHighMinusBarrier.sigma=FixedHighJet.sigma from rfl,
      show FixedHighMinusBarrier.kappa=FixedHighJet.kappa from rfl] at hh
    rw [show ((3/5 : ℚ) : ℝ) = 3/5 by norm_num,
      show ((1/500 : ℚ) : ℝ) = 1/500 by norm_num] at hh
    rw [← EulerPolynomial.coe_residual,Polynomial.coeff_coe] at hh
    dsimp only [r, p] at hh ⊢
    exact hh
  have hpositive := FixedHighMinusPositive.finite_positive
    (fun i => -r.coeff (i+140)) (fun i hi => by
      rw [HighMinusBarrierTransfer.data_r i hi]
      exact holds_neg (hres (i+140) (by omega) (by omega))) ht.1.le ht.2
  have hzero : ∀ n<140, r.coeff n=0 := by
    dsimp only [r, p]
    exact EulerPolynomial.residual_lowzero _ _ _ _ f (-(1/1000)) hf0 he
  change EulerFormal.profileResidual FixedHighJet.sigma FixedHighJet.kappa (3/5) (1/500) (fun x => p.eval x) t<0
  rw [← EulerPolynomial.eval_residual]
  change r.eval t<0
  rw [EulerPolynomial.eval_factor r hr hzero t]
  have hsum : 0< -(∑ i ∈ Finset.range 742, r.coeff (i+140)*t^i) := by
    simpa only [neg_mul,Finset.sum_neg_distrib] using hpositive
  exact mul_neg_of_pos_of_neg (pow_pos ht.1 140) (neg_pos.mp hsum)
theorem certificate : SonicContinuation.PolynomialCertificate FixedHighJet.sigma FixedHighJet.kappa
    (-500*(FixedHighJet.a:ℝ)) where
  lower_range := by
    intro f hf0 hf1 he t ht
    simpa only [neg_div] using minus_range f hf0 hf1 he t ht
  upper_range := plus_range
  lower_residual := by
    intro f hf0 hf1 he t ht
    simpa only [neg_div] using minus_residual f hf0 hf1 he t ht
  upper_residual := plus_residual
end SepticProfile.HighPolynomialCertificate


end

end OAI
