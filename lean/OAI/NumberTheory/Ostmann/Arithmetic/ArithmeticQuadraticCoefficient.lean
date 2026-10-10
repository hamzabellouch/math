import OAI.NumberTheory.Ostmann.QuadraticCenter.FullQuadraticCoefficient
import OAI.NumberTheory.Ostmann.QuadraticSieve.WeightedJacobiMoment

namespace OAI

/-! # Dependence of the original coefficient on finite arithmetic residues -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def quadraticInverseResidue (M : ℕ) (U : Finset ℕ) : ZMod U.toList.prod :=
  -(M : ZMod U.toList.prod)⁻¹

noncomputable def quadraticSymbolCoefficient (M : ℕ) (U : Finset ℕ) : ℂ :=
  ((1 / 16 : ℝ) ^ U.card : ℂ) * (realJacobi U.toList.prod M : ℂ)

noncomputable def quadraticDivisorSymbol (M : ℕ) (V : Finset ℕ) : ℂ :=
  (realJacobi V.toList.prod M : ℂ)

noncomputable def arithmeticQuadraticCoefficient (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (P M h₀ : ℕ) (θ : ℝ) (s : ℕ) : ℂ :=
  fullQuadraticCoefficient Q hQ D (quadraticInverseResidue M)
    (fun _ => (h₀ : ℝ) + θ) Φ R P (quadraticSymbolCoefficient M) (quadraticDivisorSymbol M) s

theorem quadraticSymbolCoefficient_norm_le (M : ℕ) (U : Finset ℕ) :
    ‖quadraticSymbolCoefficient M U‖ ≤ (1 / 16 : ℝ) ^ U.card := by
  have hn : ‖((1 / 16 : ℝ) : ℂ)‖ = (1 / 16 : ℝ) := by norm_num
  rw [quadraticSymbolCoefficient, norm_mul, norm_pow, hn,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (by positivity) (realJacobi_abs_le _ _)

theorem quadraticDivisorSymbol_norm_le (M : ℕ) (V : Finset ℕ) :
    ‖quadraticDivisorSymbol M V‖ ≤ 1 := by
  simpa only [quadraticDivisorSymbol, Complex.norm_real, Real.norm_eq_abs] using
    realJacobi_abs_le V.toList.prod M

theorem realJacobi_mod_multiple (L d M : ℕ) (hd : d ∣ L) (hM : Odd M) :
    realJacobi d M = realJacobi d (M % (4 * L)) := by
  have hr : Odd (M % (4 * L)) := hM.mod_even (Even.mul_right (by decide) L)
  unfold realJacobi
  rw [jacobiSym.mod_right' d hM, jacobiSym.mod_right' d hr,
    Nat.mod_mod_of_dvd M (Nat.mul_dvd_mul_left 4 hd)]

theorem quadraticInverseResidue_mod_multiple (L M : ℕ) (U : Finset ℕ)
    (hU : U.toList.prod ∣ L) :
    quadraticInverseResidue M U = quadraticInverseResidue (M % (4 * L)) U := by
  have hd : U.toList.prod ∣ 4 * L := dvd_mul_of_dvd_right hU 4
  have he : ((M % (4 * L) : ℕ) : ZMod U.toList.prod) = (M : ZMod U.toList.prod) := by
    rw [ZMod.natCast_eq_natCast_iff']
    exact Nat.mod_mod_of_dvd M hd
  simp only [quadraticInverseResidue, he]

theorem primeDivisorPositive_congr_point (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a b : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (U : Finset ℕ) (s : ℕ)
    (ha : a U = b U) :
    primeDivisorPositive Q hQ D a θ Φ R v U s =
      primeDivisorPositive Q hQ D b θ Φ R v U s := by
  unfold primeDivisorPositive
  split_ifs
  · rw [ha]
  · rfl

theorem fullQuadraticCoefficient_congr_on (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a b : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (P : ℕ) (c c' ξ ξ' : Finset ℕ → ℂ) (s : ℕ)
    (ha : ∀ U ∈ Q.powerset, a U = b U)
    (hc : ∀ U ∈ Q.powerset, c U = c' U)
    (hξ : ∀ V ∈ Q.powerset, ξ V = ξ' V) :
    fullQuadraticCoefficient Q hQ D a θ Φ R P c ξ s =
      fullQuadraticCoefficient Q hQ D b θ Φ R P c' ξ' s := by
  unfold fullQuadraticCoefficient divisorWeightedCoefficient
  apply Finset.sum_congr rfl
  intro V hV
  rw [hξ V hV]
  apply congrArg (fun z : ℂ => (ξ' V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro U hU
  rw [hc U hU]
  apply congrArg (fun z : ℂ => c' U * z)
  unfold primeDivisorMultiples
  rw [primeDivisorPositive_congr_point Q hQ D (divisorQuadraticScalar a V)
    (divisorQuadraticScalar b V) θ Φ R V.toList.prod U
    (s * P ^ 2) (divisorQuadraticScalar_congr_point a b V U (ha U hU))]

theorem arithmeticQuadraticCoefficient_mod (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (P M h₀ : ℕ) (θ : ℝ) (s : ℕ) (hM : Odd M) :
    arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ s =
      arithmeticQuadraticCoefficient Q hQ D Φ R P (M % (4 * Q.toList.prod)) h₀ θ s := by
  apply fullQuadraticCoefficient_congr_on
  · intro U hU
    exact quadraticInverseResidue_mod_multiple Q.toList.prod M U
      (primeSet_prod_dvd_of_subset Q U (Finset.mem_powerset.mp hU))
  · intro U hU
    unfold quadraticSymbolCoefficient
    rw [realJacobi_mod_multiple Q.toList.prod U.toList.prod M
      (primeSet_prod_dvd_of_subset Q U (Finset.mem_powerset.mp hU)) hM]
  · intro V hV
    unfold quadraticDivisorSymbol
    rw [realJacobi_mod_multiple Q.toList.prod V.toList.prod M
      (primeSet_prod_dvd_of_subset Q V (Finset.mem_powerset.mp hV)) hM]

end Ostmann

end OAI
