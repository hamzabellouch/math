import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLocalEuler
import OAI.NumberTheory.CubicGram.CommonFactors
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticAuxiliary

namespace OAI

/-! Arithmetic bounds for the actual dual coefficients. Clearing the
ramified denominator identifies every common level prime among the two
supported factors; the free factor is coprime to the level. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_numerator_of_frequency (n : MetaplecticDualArgument)
    {j : ℤ} (hj : -1 ≤ j) (ζ : Eisensteinˣ) (h h' w : Eisenstein)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3) :
    n.val = lambdaE^(j+1).toNat*ζ.val*h*w*h'^3 := by
  apply Subtype.ext
  have hz : ((j+1).toNat:ℤ) = j+1 := Int.toNat_of_nonneg (by omega)
  have hn : (n.val:ℂ) = metaplecticFrequency n*traceLambda := by
    rw [metaplecticFrequency,div_mul_cancel₀ _ traceLambda_ne_zero]
  rw [hn,he]
  push_cast
  rw [lambdaE_coe,←zpow_natCast traceLambda (j+1).toNat, hz]
  rw [zpow_add₀ traceLambda_ne_zero,zpow_one]
  ring

lemma metaplecticCommonNorm_le_supported {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) (k : ℕ) (ζ : Eisensteinˣ)
    {h h' w : Eisenstein} (hh : primary h) (hh' : primary h') (hwr : IsCoprime w r)
    (he : n.val = lambdaE^k*ζ.val*h*w*h'^3) :
    metaplecticCommonNorm r n ≤ norm h*norm h' := by
  let S := (primaryPrimeFactors r).filter (fun p => p ∣ n.val)
  have hsub : S ⊆ primaryPrimeFactors r := Finset.filter_subset _ _
  have hp (p : Eisenstein) (hpm : p ∈ S) : p ∣ h*h' := by
    obtain ⟨hpr,hpn⟩ := Finset.mem_filter.mp hpm
    have hspec := primaryPrimeFactor_spec hr hpr
    have hprime := hspec.1.2
    rw [he] at hpn
    rcases hprime.dvd_mul.mp hpn with hpn | hp'
    · rcases hprime.dvd_mul.mp hpn with hpn | hpw
      · rcases hprime.dvd_mul.mp hpn with hpn | hph
        · rcases hprime.dvd_mul.mp hpn with hpl | hpζ
          · exact False.elim (hprime.not_isUnit
              ((primary_coprime_lambda hr).isUnit_of_dvd' hspec.2
                (hprime.dvd_of_dvd_pow hpl)))
          · exact False.elim (hprime.not_isUnit (isUnit_of_dvd_unit hpζ ζ.isUnit))
        · exact dvd_mul_of_dvd_left hph h'
      · exact False.elim (hprime.not_isUnit (hwr.isUnit_of_dvd' hpw hspec.2))
    · exact dvd_mul_of_dvd_right (hprime.dvd_of_dvd_pow hp') h
  have hdiv := (primary_subsets_prod_dvd hr hsub (h*h')).mpr hp
  have heq : metaplecticCommonNorm r n = norm (∏ p ∈ S, p) := by
    rw [norm_finset_prod]
    rfl
  rw [heq,←norm_mul_eq]
  exact norm_le_of_dvd (mul_ne_zero (primary_ne_zero hh) (primary_ne_zero hh')) hdiv

/-- The published coefficient support gives this bound with no angular
restriction. It will be summed using the actual lattice norm series. -/
lemma metaplectic_actual_coefficient_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} {C : ℝ} (hC : 0 ≤ C)
    {r : Eisenstein} (hr : primary r) (n : MetaplecticDualArgument)
    {j : ℤ} (hj : -1 ≤ j) (ζ : Eisensteinˣ) {h h' w : Eisenstein}
    (hh : primary h) (hh' : primary h') (hwr : IsCoprime w r)
    (he : metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3)
    (ha : ‖a r n‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')) :
    ‖a r n*metaplecticLocalCoefficient r n‖ ≤
      C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')*(norm h*norm h') := by
  rw [norm_mul]
  apply mul_le_mul ha
    ((norm_metaplecticLocalCoefficient_le hr n).trans
      (metaplecticCommonNorm_le_supported hr n (j+1).toNat ζ hh hh' hwr
        (metaplectic_numerator_of_frequency n hj ζ h h' w he)))
    (_root_.norm_nonneg _) (by positivity)

private lemma metaplectic_norm_pow (a : Eisenstein) (k : ℕ) : norm (a^k) = norm a^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,norm_mul_eq,ih,pow_succ]

private lemma metaplectic_lambda_norm : norm lambdaE = 3 := by
  have hs : norm lambdaE^2 = 9 := by
    rw [←metaplectic_norm_pow,lambdaE_sq]
    change Complex.normSq (-3 : ℂ) = 9
    norm_num
  nlinarith [norm_nonneg lambdaE]

lemma metaplectic_frequency_norm (n : MetaplecticDualArgument) (k : ℕ)
    (ζ : Eisensteinˣ) (h h' w : Eisenstein)
    (he : n.val = lambdaE^k*ζ.val*h*w*h'^3) :
    Complex.normSq (metaplecticFrequency n) =
      (3:ℝ)^((k:ℝ)-1)*norm h*norm w*norm h'^3 := by
  have hLambda : Complex.normSq traceLambda = 3 := by
    rw [←lambdaE_coe]
    exact metaplectic_lambda_norm
  rw [metaplecticFrequency,Complex.normSq_div,hLambda]
  change norm n.val/3 = _
  rw [he,norm_mul_eq,norm_mul_eq,norm_mul_eq,norm_mul_eq,
    metaplectic_norm_pow,metaplectic_norm_pow,metaplectic_lambda_norm,
    norm_of_isUnit ζ.isUnit,mul_one]
  rw [Real.rpow_sub (by norm_num : (0:ℝ)<3),Real.rpow_natCast,Real.rpow_one]
  ring

lemma metaplectic_squarefree_supported_divisor {r h : Eisenstein}
    (hh : Squarefree h) (hs : ∃ k : ℕ, h ∣ r^k) : h ∣ r := by
  obtain ⟨k,hk⟩ := hs
  by_cases hk0 : k = 0
  · subst k
    simpa only [pow_zero] using hk.trans (one_dvd r)
  · exact (hh.dvd_pow_iff_dvd hk0).mp hk

lemma metaplectic_supported_divisor_mem {r h w : Eisenstein}
    (hr : primary r) (hh : primary h) (hs : Squarefree (h*w))
    (hdiv : ∃ k : ℕ, h ∣ r^k) : h ∈ metaplecticPrimaryDivisors r := by
  have hhdiv : h ∣ r := metaplectic_squarefree_supported_divisor (hs.squarefree_of_dvd (dvd_mul_right h w)) hdiv
  exact Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr
    ⟨hh,norm_le_of_dvd (primary_ne_zero hr) hhdiv⟩,hhdiv⟩

lemma metaplectic_units_finite : Finite (Eisensteinˣ) := by
  let f : Eisensteinˣ → {u : Eisenstein // u ∈ nonzeroNormBall 1} := fun u =>
    ⟨u,mem_nonzeroNormBall.mpr ⟨by rw [norm_of_isUnit u.isUnit],u.ne_zero⟩⟩
  have hf : Function.Injective f := by
    intro u v h
    apply Units.ext
    exact congrArg Subtype.val h
  exact Finite.of_injective f hf

end CubicFirstMoment

end

end OAI
