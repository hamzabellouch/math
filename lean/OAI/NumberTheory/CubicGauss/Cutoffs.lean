import Mathlib
import OAI.NumberTheory.CubicGauss.CubicFourier
import OAI.NumberTheory.CubicGram.SieveImprovement

namespace OAI

/-! Primary squarefree balls and unique square-cube decompositions. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma squarefree_mul_of_coprime {a b : Eisenstein} (ha : Squarefree a)
    (hb : Squarefree b) (hab : IsCoprime a b) : Squarefree (a*b) :=
  squarefree_mul_iff.mpr ⟨isRelPrime_iff_isCoprime.mpr hab, ha, hb⟩

lemma cubicSymbol_cube {n : Eisenstein} (hn : primary n) (m : Eisenstein) :
    cubicSymbol n m ^ 3 = if IsCoprime n m then 1 else 0 := by
  classical
  by_cases h : IsCoprime n m
  · rw [ite_eq_left h, pow_succ, cubicSymbol_sq_eq_star hn]
    rw [Complex.star_def, Complex.conj_mul', norm_cubicSymbol_of_isCoprime hn h]
    norm_num
  · rw [ite_eq_right h, cubicSymbol_eq_zero_of_not_isCoprime hn h, zero_pow (by omega : 3 ≠ 0)]

theorem cubicSymbol_cube_decomposition {n : Eisenstein} (hn : primary n)
    (s t c : Eisenstein) :
    cubicSymbol n (s*t^2*c^3) = cubicSymbol n s * star (cubicSymbol n t) *
      (if IsCoprime n c then 1 else 0) := by
  rw [cubicSymbol_mul_upper hn, cubicSymbol_mul_upper hn, cubicSymbol_pow_upper hn,
    cubicSymbol_pow_upper hn, cubicSymbol_sq_eq_star hn, cubicSymbol_cube hn]

open HeckeTheta

lemma norm_lambdaE : norm lambdaE = 3 := by
  change Complex.normSq (lambdaE : ℂ) = 3
  rw [lambdaE_coe_lambda]
  simp [HeckeTheta.lambda, Complex.normSq_apply]

lemma normNat_lambdaE : normNat lambdaE = 3 := by
  exact_mod_cast (show ((normNat lambdaE : ℕ) : ℝ) = 3 by rw [normNat_cast, norm_lambdaE])

lemma lambdaE_prime : Prime lambdaE := by
  apply irreducible_iff_prime.mp
  refine ⟨?_, ?_⟩
  · intro hu
    have := norm_of_isUnit hu
    rw [norm_lambdaE] at this
    norm_num at this
  · intro a b hab
    have hn : normNat a * normNat b = 3 := by
      rw [← normNat_mul, ← hab, normNat_lambdaE]
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp (show normNat a ∣ 3 from ⟨normNat b, hn.symm⟩) with ha | ha
    · left
      apply norm_one_isUnit
      rw [← normNat_cast, ha]
      norm_num
    · right
      have hb : normNat b = 1 := by rw [ha] at hn; omega
      apply norm_one_isUnit
      rw [← normNat_cast, hb]
      norm_num

theorem full_cube_decomposition_unit {n : Eisenstein} (hn : n ≠ 0) :
    ∃ (u : Eisensteinˣ) (i : ℕ) (s t c : Eisenstein), i < 3 ∧
      primary s ∧ primary t ∧ Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧
      c ≠ 0 ∧ n = u * lambdaE^i * s*t^2*c^3 := by
  obtain ⟨k,a,hlam,ha⟩ := WfDvdMonoid.max_power_factor hn lambdaE_prime.irreducible
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha; exact hn ha
  have hlama : IsCoprime lambdaE a := lambdaE_prime.coprime_iff_not_dvd.mpr hlam
  have h3a : IsCoprime a 3 := by
    have : IsCoprime a (lambdaE^2) := hlama.symm.pow_right
    rw [lambdaE_sq] at this
    simpa only [neg_neg] using this.neg_right
  have hres := residue_isUnit_of_isCoprime h3a.symm
  let a' := primaryNormalize a
  have hp : primary a' := primaryNormalize_primary hres
  obtain ⟨s,t,c,hs,ht,hc,hss,htt,hst,hprod⟩ := primary_cube_decomposition hp
  obtain ⟨u,hu⟩ := (primaryNormalize_associated a).symm
  refine ⟨u,k%3,s,t,lambdaE^(k/3)*c,Nat.mod_lt _ (by omega),hs,ht,hss,htt,hst,
    mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) (primary_ne_zero hc),?_⟩
  change primaryNormalize a = s*t^2*c^3 at hprod
  rw [ha, ← hu, hprod]
  have hk : lambdaE^k = lambdaE^(k%3)*(lambdaE^(k/3))^3 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hk]
  ring

end CubicFirstMoment
end

end OAI
