import OAI.NumberTheory.CubicMoment.Estimates.IdealDualDyads
import OAI.NumberTheory.CubicMoment.Estimates.HeckeMajorant

namespace OAI

/-! Transfer of a common bound for normalized dual polynomials to the
retained Hecke integrals. Root numbers and conductors only enter through
unit-modulus row factors. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma gammaQuotient_half_strip : GammaQuotientStripBound (1/2) := by
  refine ⟨1,0,by norm_num,?_⟩
  intro σ hσ u
  have hσe : σ = 1/2 := le_antisymm hσ.2 hσ.1
  subst σ
  have he : gammaFEQuotient ((1/2:ℝ)+(u:ℂ)*Complex.I) = heckeGammaRatio 0 u := by
    unfold gammaFEQuotient heckeGammaRatio
    norm_num only [zero_add,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    congr 2; ring
  rw [he,norm_heckeGammaRatio (by norm_num)]
  simp

def normalizedDualPolynomial {ν : Type*} (S : Finset ν) (χ : ν → ℂ)
    (N : ν → ℝ) (J u : ℝ) : ℂ :=
  ∑ v ∈ S, (χ v*((J/N v)^(1/2:ℝ):ℝ))*mellinPhase u (N v)

lemma finiteHeckeDual_integrand_normalized {ν : Type*} (S : Finset ν)
    (χ : ν → ℂ) (N : ν → ℝ) (hN : ∀ v ∈ S, 0 < N v)
    (ε : ℂ) {A Z J : ℝ} (hA : 0 < A) (hZ : 0 < Z) (hJ : 0 < J)
    (G : ℂ → ℂ) (t τ : ℝ) :
    G ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      finiteHeckeDual S χ N ε A ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
    ((Real.sqrt Z:ℂ)*(J^(-(1/2:ℝ)):ℝ))*
      (G ((1/2:ℂ)+(τ:ℂ)*Complex.I)*heckeSymmetryFactor ε (A^2) Z 0 t τ*
        normalizedDualPolynomial S χ N J (τ-t)) := by
  rw [finite_hecke_dual_symmetry_integrand S χ N ε hA hZ G t τ,
    finite_dual_dyad_rescale S χ N hJ hN (τ-t)]
  unfold normalizedDualPolynomial
  ring

lemma integrable_normalized_dual_kernel {ν : Type*} (S : Finset ν)
    (χ : ν → ℂ) (N : ν → ℝ) (hN : ∀ v ∈ S, 1 ≤ N v)
    (ε : ℂ) {A Z J : ℝ} (hA : 0 < A) (hZ : 1 ≤ Z) (hJ : 0 < J)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (t : ℝ) :
    Integrable (fun τ : ℝ => mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      heckeSymmetryFactor ε (A^2) Z 0 t τ*normalizedDualPolynomial S χ N J (τ-t)) := by
  let κ : ℂ := (Real.sqrt Z:ℂ)*(J^(-(1/2:ℝ)):ℝ)
  have hκ : κ ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le hZ)).ne')
    (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hJ _).ne')
  have hi := finite_hecke_dual_mellin_integrable S χ N hN ε hA hZ
    (σ := (1/2:ℝ)) (b := (1/2:ℝ)) ⟨le_rfl,le_rfl⟩ gammaQuotient_half_strip W hW hpos hsm t
  apply (hi.const_mul κ⁻¹).congr
  apply Filter.Eventually.of_forall
  intro τ
  have he := finiteHeckeDual_integrand_normalized S χ N
    (fun v hv => zero_lt_one.trans_le (hN v hv)) ε hA (zero_lt_one.trans_le hZ) hJ
    (mellin W) t τ
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at *
  rw [he,← mul_assoc,inv_mul_cancel₀ hκ,one_mul]

lemma norm_normalization_sq {Z J : ℝ} (hZ : 0 < Z) (hJ : 0 < J) :
    ‖(Real.sqrt Z:ℂ)*(J^(-(1/2:ℝ)):ℝ)‖^2 = Z/J := by
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (Real.rpow_nonneg hJ.le _),
    mul_pow,Real.sq_sqrt hZ.le]
  have hp : (J^(-(1/2:ℝ)))^2 = J⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hJ.le]
    norm_num
    exact Real.rpow_neg_one J
  rw [hp,div_eq_mul_inv]

/-- Any common bound on the normalized dual polynomial square-sum gives
exactly the factor Z/J in the retained integral square-sum. The constant
is independent of the characters, conductors, root numbers and height. -/
theorem retained_dual_moment_transfer {ν : Type*}
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Fintype ι], ∀ (S : Finset ν) (χ : ι → ν → ℂ) (N : ν → ℝ),
      (∀ v ∈ S, 1 ≤ N v) → ∀ (ε : ι → ℂ) (A : ι → ℝ),
      (∀ i, ‖ε i‖ = 1) → (∀ i, 0 < A i) → ∀ (Z J t B : ℝ),
      1 ≤ Z → 0 < J → 0 ≤ B →
      (∀ τ : ℝ, (∑ i, ‖normalizedDualPolynomial S (χ i) N J (τ-t)‖^2) ≤ B) →
      (∑ i, ‖((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          finiteHeckeDual S (χ i) N (ε i) (A i)
            ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)‖^2) ≤ C*(Z/J)*B := by
  obtain ⟨K,hK,hbound⟩ := mellin_polynomial_majorant W hW hpos hsm (1/2) 0
  let c : ℂ := ((1/(2*Real.pi):ℝ):ℂ)
  let w : ℝ → ℝ := mellinEdgeMajorant K
  refine ⟨‖c‖^2*(∫ τ : ℝ, w τ)^2,by positivity,?_⟩
  intro ι inst S χ N hN ε A hε hA Z J t B hZ hJ hB hP
  let G (i : ι) (τ : ℝ) := mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
    heckeSymmetryFactor (ε i) ((A i)^2) Z 0 t τ*
      normalizedDualPolynomial S (χ i) N J (τ-t)
  have hi : ∀ i, Integrable (G i) := fun i =>
    integrable_normalized_dual_kernel S (χ i) N hN (ε i) (hA i) hZ hJ W hW hpos hsm t
  have hmass : (∑ i, ‖∫ τ : ℝ, G i τ‖^2) ≤ (∫ τ : ℝ, w τ)^2*B := by
    apply hecke_common_majorant_square_sum ε (fun i => (A i)^2) Z 0 t
      (fun i τ => normalizedDualPolynomial S (χ i) N J (τ-t))
      (fun _ τ => mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)) w hB hε (by norm_num) hi
      (mellinEdgeMajorant_integrable K) (fun τ => by dsimp [w,mellinEdgeMajorant]; positivity)
    · intro i τ
      simpa only [pow_zero,mul_one,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
        using hbound 0 τ
    · exact hP
  have he (i : ι) :
      ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ,
        mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          finiteHeckeDual S (χ i) N (ε i) (A i)
            ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)) =
      (c*((Real.sqrt Z:ℂ)*(J^(-(1/2:ℝ)):ℝ)))*(∫ τ : ℝ, G i τ) := by
    simp_rw [finiteHeckeDual_integrand_normalized S (χ i) N
      (fun v hv => zero_lt_one.trans_le (hN v hv)) (ε i) (hA i) (zero_lt_one.trans_le hZ) hJ]
    rw [integral_const_mul]
    dsimp [c,G]
    ring
  have henorm (i : ι) :
      ‖((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          finiteHeckeDual S (χ i) N (ε i) (A i)
            ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)‖^2 =
      (‖c‖^2*(Z/J))*‖∫ τ : ℝ, G i τ‖^2 := by
    rw [he,norm_mul,mul_pow]
    congr 1
    rw [norm_mul,mul_pow,norm_normalization_sq (zero_lt_one.trans_le hZ) hJ]
  simp_rw [henorm]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (‖c‖^2*(Z/J))*((∫ τ : ℝ, w τ)^2*B) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
