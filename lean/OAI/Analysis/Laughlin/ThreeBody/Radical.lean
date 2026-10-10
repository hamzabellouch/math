import OAI.Analysis.Laughlin.FourBody.RadicalCancellation
import OAI.Analysis.Laughlin.ThreeBody.PolynomialCoefficient

namespace OAI

namespace Laughlin.Spin

noncomputable def threeBodyRadical (z T p : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ)^((z : ℤ)-p) *
    ((p.factorial : ℝ)*((T-p).factorial : ℝ) /
      ((3 : ℝ)^T * (z.factorial : ℝ)*((T-z).factorial : ℝ))))

theorem threeBodyRadical_factorial (z T p : ℕ) :
    threeBodyRadical z T p =
      (Real.sqrt (1/3))^T * (Real.sqrt 2)^z / (Real.sqrt 2)^p *
      sqrtFactorial p * sqrtFactorial (T-p) / (sqrtFactorial z*sqrtFactorial (T-z)) := by
  let a := (Real.sqrt (1/3))^T * (Real.sqrt 2)^z / (Real.sqrt 2)^p *
      sqrtFactorial p * sqrtFactorial (T-p) / (sqrtFactorial z*sqrtFactorial (T-z))
  have ha : 0 ≤ a := by dsimp [a]; unfold sqrtFactorial; positivity
  have hs : a^2 = (2 : ℝ)^((z : ℤ)-p) *
    ((p.factorial : ℝ)*((T-p).factorial : ℝ) /
      ((3 : ℝ)^T * (z.factorial : ℝ)*((T-z).factorial : ℝ))) := by
    dsimp [a]
    simp only [div_pow,mul_pow,sqrtFactorial]
    have hr (c : ℝ) (hc : 0 ≤ c) (n : ℕ) : (Real.sqrt c ^ n)^2 = c^n := by
      rw [← pow_mul,mul_comm n 2,pow_mul,Real.sq_sqrt hc]
    rw [hr _ (by norm_num),hr _ (by norm_num),hr _ (by norm_num)]
    simp only [Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [zpow_natCast,div_pow,one_pow]
    ring
  change Real.sqrt _ = a
  rw [← hs,Real.sqrt_sq ha]

theorem source_threeBody_radical_coefficient (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    couplingPolynomialCoefficient (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p =
      (Certificate.U 2 z T p : ℝ) * threeBodyRadical z T p := by
  rw [threeBody_polynomialCoefficient_factorial z T p hz hp,threeBodyRadical_factorial]
  ring

theorem threeBody_alpha_radical_cancel (z T t p j : ℕ) (hT : p+j=T) :
    alphaRadical t p j * threeBodyRadical z T p = threeBodyRadical z T t := by
  have hj : T-p=j := by omega
  have he : ((p : ℤ)-t)+((z : ℤ)-p)=(z : ℤ)-t := by omega
  have hs : (alphaRadical t p j * threeBodyRadical z T p)^2 = (threeBodyRadical z T t)^2 := by
    simp only [alphaRadical,threeBodyRadical,mul_pow]
    repeat rw [Real.sq_sqrt (by positivity)]
    rw [hT,hj]
    calc
      _ = ((2 : ℝ)^((p : ℤ)-t)*(2 : ℝ)^((z : ℤ)-p)) *
        ((t.factorial : ℝ)*(T-t).factorial/(3^T*z.factorial*(T-z).factorial)) := by field_simp
      _ = _ := by rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),he]
  have hl : 0 ≤ alphaRadical t p j * threeBodyRadical z T p := by
    unfold alphaRadical threeBodyRadical; positivity
  have hr : 0 ≤ threeBodyRadical z T t := Real.sqrt_nonneg _
  nlinarith only [hs,hl,hr]

theorem threeBodyRadical_sq_choose (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    (threeBodyRadical z T p)^2 =
      (2 : ℝ)^z * (T.choose z : ℝ) / ((3 : ℝ)^T * (2 : ℝ)^p * (T.choose p : ℝ)) := by
  have hc (k : ℕ) (hk : k ≤ T) : (T.choose k : ℝ) * (k.factorial : ℝ) * ((T-k).factorial : ℝ) = T.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hcp : (T.choose p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.choose_pos hp))
  unfold threeBodyRadical
  rw [Real.sq_sqrt (by positivity),zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zpow_natCast]
  apply (eq_div_iff (by positivity : (3 : ℝ)^T*2^p*(T.choose p : ℝ) ≠ 0)).mpr
  have hzfac := hc z hz
  have hpfac := hc p hp
  field_simp
  nlinarith only [hzfac,hpfac]

end Laughlin.Spin

end OAI
