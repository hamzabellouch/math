import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedDirichlet

namespace OAI

/-! The ramified conductor cutoff for every global-unit class in the
literal denominator decomposition. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_unit_lambda (u : Eisensteinˣ) (k : ℕ) (a : Eisenstein) :
    cubicThetaEisensteinWeight ((u:Eisenstein)*lambdaE^k) a=
      if primary a then cubicSymbol a (u:Eisenstein)*(cubicSymbol a lambdaE)^k else 0 := by
  by_cases ha : primary a
  · have hunit : IsCoprime (u:Eisenstein) a := ⟨(u⁻¹:Eisensteinˣ),0,by simp⟩
    have hc := hunit.mul_left ((primary_coprime_lambda ha).symm.pow_left (m:=k))
    rw [cubicThetaEisensteinWeight,ite_eq_left ⟨ha,hc⟩,ite_eq_left ha,
      cubicSymbol_mul_upper ha,cubicSymbol_pow_upper ha]
  · rw [cubicThetaEisensteinWeight,ite_eq_right (fun h => ha h.1),ite_eq_right ha]

lemma cubicThetaEisensteinWeight_unit_lambda_periodic (u : Eisensteinˣ)
    (k : ℕ) (a b : Eisenstein) :
    cubicThetaEisensteinWeight ((u:Eisenstein)*lambdaE^k) (a+9*b)=
      cubicThetaEisensteinWeight ((u:Eisenstein)*lambdaE^k) a := by
  have hp : primary (a+9*b) ↔ primary a := by
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨t-3*b,by linear_combination ht⟩
    · rintro ⟨t,ht⟩
      exact ⟨t+3*b,by linear_combination ht⟩
  rw [cubicThetaEisensteinWeight_unit_lambda,cubicThetaEisensteinWeight_unit_lambda]
  by_cases ha : primary a
  · have hn : (9:Eisenstein) ∣ a+9*b-a := ⟨b,by ring⟩
    rw [ite_eq_left (hp.mpr ha),ite_eq_left ha,
      cubicSymbol_unit_periodic (hp.mpr ha) ha u.isUnit hn,
      cubicSymbol_lambda_periodic (hp.mpr ha) ha hn]
  · rw [ite_eq_right (fun h => ha (hp.mp h)),ite_eq_right ha]

lemma cubicThetaEisensteinWeight_full_ramified_periodic (e : Eisensteinˣ)
    {u : Eisenstein} (hu : primary u) (k : ℕ) (a b : Eisenstein) :
    cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^k*u) (a+9*u*b)=
      cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^k*u) a := by
  rw [mul_comm ((e:Eisenstein)*lambdaE^k) u,cubicThetaEisensteinWeight_factor hu,
    cubicThetaEisensteinWeight_factor hu]
  have hc : cubicSymbol u (a+9*u*b)=cubicSymbol u a := by
    apply cubicSymbol_congr
    exact residue_eq_of_dvd_sub ⟨9*b,by ring⟩
  rw [hc,show a+9*u*b=a+9*(u*b) by ring,
    cubicThetaEisensteinWeight_unit_lambda_periodic]

theorem cubicThetaEisensteinGaussCoefficient_full_ramified_support (e : Eisensteinˣ)
    {u : Eisenstein} (hu : primary u) (n : ℕ) (h : Eisenstein)
    (hG : cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)*u) h≠0) :
    lambdaE^n ∣ h := by
  let c : Eisenstein := (e:Eisenstein)*lambdaE^(n+2)*u
  have hc : c≠0 := mul_ne_zero (mul_ne_zero e.ne_zero
    (pow_ne_zero _ lambdaE_prime.ne_zero)) (primary_ne_zero hu)
  have hq : (3:Eisenstein)*c≠0 := mul_ne_zero (by norm_num) hc
  let : Finite (Residues (3*c)) := finite_residues hq
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  have h3 : (3:Eisenstein)∣c := by
    refine ⟨-(e:Eisenstein)*lambdaE^n*u,?_⟩
    dsimp only [c]
    rw [pow_add,lambdaE_sq]
    ring
  have hf (x b : Residues (3*c)) :
      cubicThetaEisensteinResidueWeight c (x+Ideal.Quotient.mk (modulus (3*c)) (9*u)*b)=
      cubicThetaEisensteinResidueWeight c x := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul,← map_add,cubicThetaEisensteinResidueWeight_mk h3,
      cubicThetaEisensteinResidueWeight_mk h3]
    exact cubicThetaEisensteinWeight_full_ramified_periodic e hu (n+2) a b
  have hd : 3*c ∣ (9*u)*h := by
    apply residueFourier_reduction_support hq (cubicThetaEisensteinResidueWeight c) h hf
    change cubicThetaEisensteinGaussCoefficient c h≠0 at hG
    rw [cubicThetaEisensteinGaussCoefficient_fourier hc] at hG
    simpa only [cubicThetaEisensteinResidueWeight,tsum_fintype] using hG
  have he : 3*c=(9*u)*(-(e:Eisenstein)*lambdaE^n) := by
    dsimp only [c]
    rw [pow_add,lambdaE_sq]
    ring
  rw [he,mul_dvd_mul_iff_left (mul_ne_zero (by norm_num) (primary_ne_zero hu))] at hd
  exact (dvd_mul_left (lambdaE^n) (-(e:Eisenstein))).trans hd

theorem cubicThetaRamifiedTerm_high (s : ℂ) (h : Eisenstein)
    (e : Eisensteinˣ) (n : ℕ) (u : CubicThetaPrimaryPart) (hn : ¬lambdaE^n ∣ h) :
    cubicThetaRamifiedTerm s h (e,n,u)=0 := by
  have hz : cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)*u.val) h=0 := by
    by_contra he
    exact hn (cubicThetaEisensteinGaussCoefficient_full_ramified_support e u.property n h he)
  change cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)*u.val) h*
    (norm ((e:Eisenstein)*lambdaE^(n+2)*u.val):ℂ)^(-s)=0
  rw [hz,zero_mul]

end CubicFirstMoment

end

end OAI
