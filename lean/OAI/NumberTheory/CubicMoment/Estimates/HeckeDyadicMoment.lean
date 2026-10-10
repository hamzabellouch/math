import OAI.NumberTheory.CubicMoment.Estimates.HeckeDualMoment

namespace OAI

/-! Exact finite dyadic splitting of the retained dual integral and the
resulting character-average bound. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def finiteDualIntegral {ν : Type*} (W : ℝ → ℂ) (S : Finset ν) (χ : ν → ℂ)
    (N : ν → ℝ) (ε : ℂ) (A Z t : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
    mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      finiteHeckeDual S χ N ε A ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)

lemma finiteIdealDualIntegral_dyad_partition (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    (S : Finset EisensteinIdealExponent) (χ : EisensteinIdealExponent → ℂ)
    (ε : ℂ) {A Z : ℝ} (hA : 0 < A) (hZ : 1 ≤ Z) (t : ℝ) :
    finiteDualIntegral W S χ idealExponentNorm ε A Z t =
      ∑ j ∈ idealDyadIndices S, finiteDualIntegral W (idealDyad S j) χ idealExponentNorm ε A Z t := by
  let F (T : Finset EisensteinIdealExponent) (τ : ℝ) :=
    mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      finiteHeckeDual T χ idealExponentNorm ε A ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)
  have hf (τ : ℝ) : F S τ = ∑ j ∈ idealDyadIndices S, F (idealDyad S j) τ := by
    dsimp [F,finiteHeckeDual]
    rw [finite_idealDirichlet_dyad_partition]
    simp only [Finset.mul_sum]
  have hi (j : ℕ) : Integrable (F (idealDyad S j)) := by
    simpa only [F,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      finite_hecke_dual_mellin_integrable (idealDyad S j) χ idealExponentNorm
      (fun ν _ => idealExponentNorm_ge_one ν) ε hA hZ
      (σ := (1/2:ℝ)) (b := (1/2:ℝ)) ⟨le_rfl,le_rfl⟩ gammaQuotient_half_strip W hW hpos hsm t
  unfold finiteDualIntegral
  rw [← Finset.mul_sum]
  congr 1
  change (∫ τ : ℝ, F S τ) = ∑ j ∈ idealDyadIndices S, ∫ τ : ℝ, F (idealDyad S j) τ
  rw [show F S = fun τ => ∑ j ∈ idealDyadIndices S, F (idealDyad S j) τ from funext hf]
  exact integral_finsetSum _ (fun j _ => hi j)

/-- A bound for each actual normalized ideal dyad transfers to the
whole retained integral with only its finite number of dyads lost. -/
theorem retained_ideal_dyadic_moment_transfer
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Fintype ι], ∀ (S : Finset EisensteinIdealExponent)
      (χ : ι → EisensteinIdealExponent → ℂ) (ε : ι → ℂ) (A : ι → ℝ),
      (∀ i, ‖ε i‖ = 1) → (∀ i, 0 < A i) → ∀ (Z t : ℝ) (B : ℕ → ℝ),
      1 ≤ Z → (∀ j ∈ idealDyadIndices S, 0 ≤ B j) →
      (∀ j ∈ idealDyadIndices S, ∀ τ : ℝ,
        (∑ i, ‖normalizedDualPolynomial (idealDyad S j) (χ i) idealExponentNorm
          ((2:ℝ)^j) (τ-t)‖^2) ≤ B j) →
      (∑ i, ‖finiteDualIntegral W S (χ i) idealExponentNorm (ε i) (A i) Z t‖^2) ≤
        (idealDyadIndices S).card * C *
          ∑ j ∈ idealDyadIndices S, (Z/(2:ℝ)^j)*B j := by
  obtain ⟨C,hC,hbound⟩ := retained_dual_moment_transfer
    (ν := EisensteinIdealExponent) W hW hpos hsm
  refine ⟨C,hC,?_⟩
  intro ι inst S χ ε A hε hA Z t B hZ hB hP
  let F (i : ι) (j : ℕ) := finiteDualIntegral W (idealDyad S j) (χ i) idealExponentNorm (ε i) (A i) Z t
  have hsplit (i : ι) : finiteDualIntegral W S (χ i) idealExponentNorm (ε i) (A i) Z t =
      ∑ j ∈ idealDyadIndices S, F i j :=
    finiteIdealDualIntegral_dyad_partition W hW hpos hsm S (χ i) (ε i) (hA i) hZ t
  simp_rw [hsplit]
  have hcauchy := complex_mass_sum_sq_le (idealDyadIndices S) (Finset.univ : Finset ι) F
  apply hcauchy.trans
  calc
    _ ≤ (idealDyadIndices S).card * ∑ j ∈ idealDyadIndices S, C*(Z/(2:ℝ)^j)*B j := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro j hj
      exact hbound (idealDyad S j) χ idealExponentNorm (fun ν _ => idealExponentNorm_ge_one ν)
        ε A hε hA Z ((2:ℝ)^j) t (B j) hZ (by positivity) (hB j hj) (hP j hj)
    _ = _ := by rw [Finset.mul_sum]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

end CubicFirstMoment

end

end OAI
