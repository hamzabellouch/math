import OAI.NumberTheory.CubicMoment.Estimates.SupportedIdealCount
import OAI.NumberTheory.CubicMoment.Estimates.SupportedIdealParts

namespace OAI

/-! The finite Euler factor for a varying small modulus costs only an
arbitrary positive power of its norm. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

 theorem supported_euler_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : EisensteinIdealExponent,
      (∏ p ∈ ν.support, (1-(normNat (idealPrimeRepresentative p):ℝ)^(-ε))⁻¹) ≤
        C*idealExponentNorm ν^ε := by
  let R : ℝ := (2:ℝ)^(1/ε)
  let T : Finset EisensteinIdealPrime :=
    (fullIdealBall R).biUnion (fun ν => ν.support)
  let A : ℝ := (1-(2:ℝ)^(-ε))⁻¹
  have ht : (2:ℝ)^(-ε) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hA : 1 ≤ A := by
    dsimp [A]
    rw [← one_div]
    apply (le_div_iff₀ (by linarith : 0 < 1-(2:ℝ)^(-ε))).mpr
    rw [one_mul]
    linarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-ε)]
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  have hRe : R^ε = 2 := by
    dsimp [R]
    rw [← Real.rpow_mul (by norm_num),one_div_mul_cancel hε.ne',Real.rpow_one]
  have hT (p : EisensteinIdealPrime) :
      (normNat (idealPrimeRepresentative p):ℝ) ≤ R → p ∈ T := by
    intro hp
    apply Finset.mem_biUnion.mpr
    refine ⟨Finsupp.single p 1,?_,by simp⟩
    apply mem_fullIdealBall.mpr
    simpa only [idealExponentNorm_single,pow_one] using hp
  refine ⟨A^T.card,pow_pos (zero_lt_one.trans_le hA) _,?_⟩
  intro ν
  have hpoint : ∀ p ∈ ν.support,
      (1-(normNat (idealPrimeRepresentative p):ℝ)^(-ε))⁻¹ ≤
        (if p ∈ T then A else 1)*(normNat (idealPrimeRepresentative p):ℝ)^(ε*ν p) := by
    intro p hp
    let q : ℝ := normNat (idealPrimeRepresentative p)
    have hq : (2:ℝ) ≤ q := by
      dsimp [q]
      exact_mod_cast idealPrimeRepresentative_normNat_ge_two p
    have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
    have hqt : q^(-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
    have hexp : ε ≤ ε*ν p := by
      have hn : (1:ℝ) ≤ ν p := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp))
      nlinarith
    have hpow : 1 ≤ q^(ε*ν p) := Real.one_le_rpow (by linarith) (by positivity)
    by_cases hpT : p ∈ T
    · simp only [ite_eq_left hpT]
      have hlocal : (1-q^(-ε))⁻¹ ≤ A := by
        apply (inv_le_inv₀ (by linarith) (by linarith)).mpr
        have hmono := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<2) hq (by linarith : -ε ≤ 0)
        linarith
      exact hlocal.trans (le_mul_of_one_le_right (zero_le_one.trans hA) hpow)
    · simp only [ite_eq_right hpT,one_mul]
      have hRp : R ≤ q := le_of_lt (lt_of_not_ge (fun h => hpT (hT p h)))
      have htwo : (2:ℝ) ≤ q^ε := by
        rw [← hRe]
        exact Real.rpow_le_rpow hR.le hRp hε.le
      have hhalf : q^(-ε) ≤ 1/2 := by
        rw [Real.rpow_neg hqp.le]
        simpa only [one_div] using
          (inv_le_inv₀ (Real.rpow_pos_of_pos hqp ε) (by norm_num : (0:ℝ) < 2)).mpr htwo
      have hlocal : (1-q^(-ε))⁻¹ ≤ 2 := by
        rw [← one_div]
        apply (div_le_iff₀ (by linarith : 0 < 1-q^(-ε))).mpr
        linarith
      exact hlocal.trans (htwo.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp))
  have hprod := Finset.prod_le_prod₀ (s := ν.support)
    (fun p _ => inv_nonneg.mpr (by
      have hp : (1:ℝ) < normNat (idealPrimeRepresentative p) := by
        have := idealPrimeRepresentative_normNat_ge_two p
        exact_mod_cast (by omega : 1 < normNat (idealPrimeRepresentative p))
      exact sub_nonneg.mpr (le_of_lt (Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith))))) hpoint
  rw [Finset.prod_mul_distrib] at hprod
  have hsmall : (∏ p ∈ ν.support, if p ∈ T then A else 1) ≤ A^T.card := by
    rw [Finset.prod_ite_mem,Finset.prod_const]
    exact pow_le_pow_right₀ hA (Finset.card_le_card Finset.inter_subset_right)
  have hnorm : (∏ p ∈ ν.support,
      (normNat (idealPrimeRepresentative p):ℝ)^(ε*ν p)) = idealExponentNorm ν^ε := by
    calc
      _ = ∏ p ∈ ν.support, ((normNat (idealPrimeRepresentative p):ℝ)^ν p)^ε := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
        congr 1
        ring
      _ = (∏ p ∈ ν.support, ((normNat (idealPrimeRepresentative p):ℝ)^ν p))^ε :=
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity) ε
      _ = _ := by rw [idealExponentNorm_eq_prod]
  rw [hnorm] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (idealExponentNorm_pos ν).le _))

/-- Uniform subpower counting of the actual supported parts. -/
theorem supportedParts_card_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Eisenstein) (S : Finset EisensteinIdealExponent) (J : ℝ),
      v ≠ 0 → 1 ≤ J → (∀ ν ∈ S, idealExponentNorm ν ≤ J) →
      ((supportedParts v S).card:ℝ) ≤ C*(J*norm v)^ε := by
  obtain ⟨C,hC,hEuler⟩ := supported_euler_small_power hε
  refine ⟨C,hC,?_⟩
  intro v S J hv hJ hS
  have hT (ρ : EisensteinIdealExponent) (hρ : ρ ∈ supportedParts v S) :
      ρ.support ⊆ (idealExponentOf v).support ∧ idealExponentNorm ρ ≤ J := by
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hρ
    refine ⟨?_,(supportedIdealPart_norm_le v ν).trans (hS ν hν)⟩
    intro p hp
    by_contra hpin
    have hzero : supportedIdealPart v ν p = 0 := by
      have hz := Finsupp.notMem_support_iff.mp hpin
      simp [supportedIdealPart,hz]
    exact (Finsupp.mem_support_iff.mp hp) hzero
  have hsum := ideal_supported_rankin_sum hε (idealExponentOf v).support
    (supportedParts v S) hT
  have he := hEuler (idealExponentOf v)
  rw [idealExponentOf_norm hv] at he
  calc
    _ = ∑ _ρ ∈ supportedParts v S, (1:ℝ) := by simp
    _ ≤ ∑ ρ ∈ supportedParts v S, J^ε*idealExponentNorm ρ^(-ε) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [Real.rpow_neg (idealExponentNorm_pos ρ).le,← div_eq_mul_inv]
      apply (le_div_iff₀ (Real.rpow_pos_of_pos (idealExponentNorm_pos ρ) ε)).mpr
      rw [one_mul]
      exact Real.rpow_le_rpow (idealExponentNorm_pos ρ).le (hT ρ hρ).2 hε.le
    _ = J^ε*∑ ρ ∈ supportedParts v S, idealExponentNorm ρ^(-ε) := (Finset.mul_sum _ _ _).symm
    _ ≤ J^ε*(C*norm v^ε) := mul_le_mul_of_nonneg_left (hsum.trans he) (by positivity)
    _ = C*(J*norm v)^ε := by rw [Real.mul_rpow (by linarith) (norm_nonneg v)]; ring

end CubicFirstMoment

end

end OAI
