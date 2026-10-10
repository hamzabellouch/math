import OAI.NumberTheory.CubicMoment.Estimates.CubePoisson
import OAI.NumberTheory.CubicMoment.Estimates.CubeAsymptotic
import OAI.NumberTheory.CubicMoment.Estimates.CubeRoughness
import OAI.NumberTheory.CubicMoment.Estimates.CubeRiesz

namespace OAI

/-! The actual cube part of a Gram entry, with the multiplicity three
and the coprimality error retained. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gramDualTerm_cube {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) (j : Eisenstein) :
    gramDualTerm b a W A (j^3) =
      if IsCoprime a j ∧ IsCoprime b j then
        radialDualProfile W (A*(norm j)^3/(27*norm (b*a))) else 0 := by
  have h := cube_gramDualTerm ha hb primary_one
    (isCoprime_one_right : IsCoprime a 1) (isCoprime_one_right : IsCoprime b 1) W hA j
  change mixedCubic b a (1^2)*gramDualTerm b a W (A/(norm 1)^2) (1^2*j^3) = _ at h
  simpa only [one_pow,one_mul,norm_one_eq,div_one,mixedCubic_one hb ha] using h

lemma cube_gram_series {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A q : ℝ} (hA : 0 ≤ A) (hq : 0 < q) (he : q^3 = A/(27*norm (b*a))) :
    (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
        gramDualTerm b a W A h else 0) =
      (1/3:ℂ)*(∑' j : Eisenstein, if j = 0 then 0 else
        (if IsCoprime a j ∧ IsCoprime b j then
          radialDualProfile W (q^3*(norm j)^3) else 0)) := by
  have hj (j : Eisenstein) : gramDualTerm b a W A (j^3) =
      if IsCoprime a j ∧ IsCoprime b j then
        radialDualProfile W (q^3*(norm j)^3) else 0 := by
    rw [gramDualTerm_cube ha hb W hA, he]
    congr 2
    ring
  have hs : Summable (fun j : Eisenstein => if j = 0 then (0:ℂ) else
      gramDualTerm b a W A (j^3)) := by
    apply (summable_radial_cube_lattice W hW hW' (pow_pos hq 3)).norm.of_norm_bounded
    intro j
    rw [hj]
    by_cases hz : j = 0
    · rw [ite_eq_left hz,norm_zero]
      positivity
    · rw [ite_eq_right hz]
      by_cases hc : IsCoprime a j ∧ IsCoprime b j
      · simp only [ite_eq_left hc,le_refl]
      · rw [ite_eq_right hc,norm_zero]
        positivity
  have h := tsum_nonzero_cubes (gramDualTerm b a W A) hs
  simp_rw [hj] at h
  linear_combination -(1/3:ℂ)*h

/-- A fixed radial weight has a uniform principal-frequency expansion.
The two errors are the bounded lattice error and the explicit rough-prime
exclusion error. The lattice scale is linked to the actual Poisson scale. -/
theorem cube_gram_asymptotic (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (a b : Eisenstein),
      primary a → Squarefree a → primary b → Squarefree b →
      ∀ A q : ℝ, 0 ≤ A → 0 < q → q ≤ 1 → q^3 = A/(27*norm (b*a)) →
      ‖(∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
          gramDualTerm b a W A h else 0) -
        (1/(3*q):ℝ) • cubeProfileIntegral W‖ ≤
        (C+K/q*∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p)/3 := by
  obtain ⟨C,hC,hmain⟩ := radial_cube_lattice_asymptotic W hW hW'
  obtain ⟨K,hK,hrough⟩ := radial_cube_coprimality_error W hW hW'
  refine ⟨C,K,hC,hK,?_⟩
  intro a b ha hsa hb hsb A q hA hq hq1 he
  let J := ∑' j : Eisenstein, if j = 0 then (0:ℂ) else
    radialDualProfile W (q^3*(norm j)^3)
  let Jc := ∑' j : Eisenstein, if j = 0 then (0:ℂ) else
    (if IsCoprime a j ∧ IsCoprime b j then
      radialDualProfile W (q^3*(norm j)^3) else 0)
  have hm : ‖J-(q⁻¹:ℝ) • cubeProfileIntegral W‖ ≤ C := hmain q hq hq1
  have hr : ‖J-Jc‖ ≤ K/q*∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p :=
    hrough q hq a b ha hsa hb hsb
  have hd : ‖Jc-(q⁻¹:ℝ) • cubeProfileIntegral W‖ ≤
      C+K/q*∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p := by
    calc
      _ = ‖(J-(q⁻¹:ℝ) • cubeProfileIntegral W)-(J-Jc)‖ := by congr 1; ring
      _ ≤ ‖J-(q⁻¹:ℝ) • cubeProfileIntegral W‖+‖J-Jc‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hm hr
  rw [cube_gram_series ha hb W hW hW' hA hq he]
  change ‖(1/3:ℂ)*Jc-(1/(3*q):ℝ) • cubeProfileIntegral W‖ ≤ _
  have heq : (1/3:ℂ)*Jc-(1/(3*q):ℝ) • cubeProfileIntegral W =
      (1/3:ℝ) • (Jc-(q⁻¹:ℝ) • cubeProfileIntegral W) := by
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_mul,
      Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_inv]
    ring
  rw [heq,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3)]
  exact (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 1/3)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
