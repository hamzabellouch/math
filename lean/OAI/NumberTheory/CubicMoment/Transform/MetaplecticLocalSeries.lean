import OAI.NumberTheory.CubicMoment.Transform.MetaplecticVoronoi
import OAI.NumberTheory.CubicGram.LatticeCounts

namespace OAI

/-! The local absolute series in the level Voronoi formula. The two
terms at each cube exponent are exactly the squarefree exponent 0 or 1.
Their product over the level costs only an arbitrary norm power. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def metaplecticLocalRatio (p σ : ℝ) : ℝ := p^(-5/2-3*σ)

def metaplecticLocalTerms (p σ : ℝ) (k : ℕ) : ℝ :=
  (if k = 0 then 1 else p*metaplecticLocalRatio p σ^k)+
    p^(-σ)*metaplecticLocalRatio p σ^k

def metaplecticLocalEuler (p σ : ℝ) : ℝ :=
  1+p^(-σ)+(p+p^(-σ))*metaplecticLocalRatio p σ/(1-metaplecticLocalRatio p σ)

lemma metaplecticLocalRatio_bounds {p σ : ℝ} (hp : 2 ≤ p) (hσ : 0 < σ) :
    0 ≤ metaplecticLocalRatio p σ ∧ metaplecticLocalRatio p σ ≤ 1/4 ∧
      p*metaplecticLocalRatio p σ ≤ 1/2 := by
  have hp0 : 0 < p := by linarith
  have hq : metaplecticLocalRatio p σ ≤ p^(-(2:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  have hpq : p*metaplecticLocalRatio p σ ≤ p^(-(1:ℝ)) := by
    calc
      _ = p^(1+(-5/2-3*σ)) := by
        rw [Real.rpow_add hp0,Real.rpow_one]
        rfl
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  refine ⟨Real.rpow_nonneg hp0.le _,?_,?_⟩
  · calc
      _ ≤ p^(-(2:ℝ)) := hq
      _ ≤ (2:ℝ)^(-(2:ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by norm_num)
      _ = 1/4 := by norm_num [Real.rpow_neg,Real.rpow_natCast]
  · calc
      _ ≤ p^(-(1:ℝ)) := hpq
      _ ≤ (2:ℝ)^(-(1:ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by norm_num)
      _ = 1/2 := by norm_num

theorem metaplecticLocalTerms_hasSum {p σ : ℝ} (hp : 2 ≤ p) (hσ : 0 < σ) :
    HasSum (metaplecticLocalTerms p σ) (metaplecticLocalEuler p σ) := by
  obtain ⟨hq0,hq,_⟩ := metaplecticLocalRatio_bounds hp hσ
  have hq1 : metaplecticLocalRatio p σ < 1 := by linarith
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left
    ((p+p^(-σ))*metaplecticLocalRatio p σ)
  have ht : HasSum (fun k : ℕ => metaplecticLocalTerms p σ (k+1))
      ((p+p^(-σ))*metaplecticLocalRatio p σ/(1-metaplecticLocalRatio p σ)) := by
    convert hg using 1
    · funext k
      simp only [metaplecticLocalTerms,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
        ite_false,pow_succ]
      ring
    · ring
  have hs := HasSum.zero_add (f := metaplecticLocalTerms p σ) ht
  simpa only [metaplecticLocalTerms,pow_zero,ite_true,mul_one,metaplecticLocalEuler] using hs

lemma metaplecticLocalEuler_nonneg {p σ : ℝ} (hp : 2 ≤ p) (hσ : 0 < σ) :
    0 ≤ metaplecticLocalEuler p σ := by
  obtain ⟨hq0,hq,_⟩ := metaplecticLocalRatio_bounds hp hσ
  unfold metaplecticLocalEuler
  have hp0 : 0 ≤ p := by linarith
  have hden : 0 ≤ 1-metaplecticLocalRatio p σ := by linarith
  positivity

lemma metaplecticLocalEuler_le_three {p σ : ℝ} (hp : 2 ≤ p) (hσ : 0 < σ) :
    metaplecticLocalEuler p σ ≤ 3 := by
  obtain ⟨hq0,hq,hpq⟩ := metaplecticLocalRatio_bounds hp hσ
  have hx0 : 0 ≤ p^(-σ) := Real.rpow_nonneg (by linarith) _
  have hx : p^(-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hden : 0 < 1-metaplecticLocalRatio p σ := by linarith
  have hf : (p+p^(-σ))*metaplecticLocalRatio p σ/(1-metaplecticLocalRatio p σ) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    have hxq := mul_le_mul_of_nonneg_right hx hq0
    nlinarith
  unfold metaplecticLocalEuler
  linarith

private lemma primaryPrime_norm_two {p : Eisenstein} (hp : primaryPrime p) : 2 ≤ norm p := by
  have hz := normNat_ne_zero hp.2.ne_zero
  have ho : normNat p ≠ 1 := by
    intro h
    apply hp.2.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [← normNat_cast,h]
    norm_num
  rw [← normNat_cast]
  exact_mod_cast (show 2 ≤ normNat p by omega)

theorem metaplectic_local_product_small_power {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      (∏ p ∈ primaryPrimeFactors r, metaplecticLocalEuler (norm p) σ) ≤ C*norm r^ε := by
  obtain ⟨C,hC,hbound⟩ := primeDivisorWeight_small_power (ε/2) (by positivity)
  refine ⟨C^2,by positivity,?_⟩
  intro r hr hsr
  have hprod : (∏ p ∈ primaryPrimeFactors r, metaplecticLocalEuler (norm p) σ) ≤
      (4:ℝ)^(primaryPrimeFactors r).card := by
    calc
      _ ≤ ∏ _p ∈ primaryPrimeFactors r, (4:ℝ) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          exact metaplecticLocalEuler_nonneg
            (primaryPrime_norm_two (primaryPrimeFactor_spec hr hp).1) hσ
        · intro p hp
          exact (metaplecticLocalEuler_le_three
            (primaryPrime_norm_two (primaryPrimeFactor_spec hr hp).1) hσ).trans
              (by norm_num)
      _ = _ := Finset.prod_const _
  calc
    _ ≤ (4:ℝ)^(primaryPrimeFactors r).card := hprod
    _ = ((2:ℝ)^(primaryPrimeFactors r).card)^2 := by
      calc
        _ = ((2:ℝ)^2)^(primaryPrimeFactors r).card := by norm_num
        _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    _ ≤ (C*norm r^(ε/2))^2 := pow_le_pow_left₀ (by positivity) (hbound r hr hsr) _
    _ = C^2*norm r^ε := by
      have he : (norm r^(ε/2))^2 = norm r^ε := by
        rw [←Real.rpow_mul_natCast (norm_nonneg r)]
        congr 1
        ring
      rw [mul_pow,he]

end CubicFirstMoment

end

end OAI
