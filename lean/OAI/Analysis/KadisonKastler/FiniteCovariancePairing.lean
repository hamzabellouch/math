import OAI.Analysis.KadisonKastler.FiniteSignFourthMoment
import OAI.Analysis.KadisonKastler.ClippedPairingBound
import OAI.Analysis.KadisonKastler.DensePairingBound

namespace OAI

/-! # Testing balanced finite families by bounded algebra elements -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem normalized_sign_second_moment_le_one (τ : FaithfulTracialState A)
    (a : ι → A) (ha : ∀ i, traceTwoNorm τ (a i) ≤ 1) :
    (𝔼 ε : ι → Bool, traceTwoNorm τ (normalizedFiniteSignSum a ε) ^ 2) ≤ 1 := by
  rw [expect_normalizedFiniteSignSum_twoNorm_sq]
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _ : ι, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum fun i _ => by
        nlinarith [traceTwoNorm_nonneg τ (a i), ha i]
    _ = 1 := by simp [Fintype.card_ne_zero]

/-- A balanced family has a bounded fourth moment after sign randomization.
Clipping then controls its common pairing by unit-ball tests. -/
theorem pairing_le_of_finite_covariances (τ : FaithfulTracialState A)
    (J : A →ₗ[ℂ] H) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (V : H →L[ℂ] H) (a b : ι → A) {z : ℂ} {K : ℝ}
    (hK : ∀ x y : A, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖inner ℂ (V (J x)) (J y)‖ ≤ K)
    (ha : ∀ i, traceTwoNorm τ (a i) ≤ 1)
    (hb : ∀ i, traceTwoNorm τ (b i) ≤ 1)
    (hQa : traceTwoNorm τ (finiteSignRightCovariance a) ≤ 2)
    (hLa : traceTwoNorm τ (finiteSignLeftCovariance a) ≤ 2)
    (hQb : traceTwoNorm τ (finiteSignRightCovariance b) ≤ 2)
    (hLb : traceTwoNorm τ (finiteSignLeftCovariance b) ≤ 2)
    (hz : ∀ i, inner ℂ (V (J (a i))) (J (b i)) = z) :
    ‖z‖ ≤ 192 * K + ‖V‖ / 2 := by
  have hmean : (𝔼 ε : ι → Bool,
      inner ℂ (V (J (normalizedFiniteSignSum a ε)))
        (J (normalizedFiniteSignSum b ε))) = z := by
    rw [expect_normalizedFiniteSignSum_pairing]
    simp [hz, Fintype.card_ne_zero]
  have h := averaged_pairing_le_one_ninety_two τ J hJ V
    (normalizedFiniteSignSum a) (normalizedFiniteSignSum b) hK
    (normalized_sign_second_moment_le_one τ a ha)
    (normalized_sign_second_moment_le_one τ b hb)
    (expect_normalizedFiniteSignSum_fourth_le_twelve τ a hQa hLa)
    (expect_normalizedFiniteSignSum_fourth_le_twelve τ b hQb hLb)
  rwa [hmean] at h

/-- Once finite families with the stated covariance bounds have been
constructed for each pair of tracial unit vectors, the bounded-ball test
constant is `384`. The family construction is kept as a separate task. -/
theorem opNorm_le_of_finite_covariance_families (τ : FaithfulTracialState A)
    (J : A →ₗ[ℂ] H) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hJdense : DenseRange J) (V : H →L[ℂ] H) {K : ℝ}
    (hK : ∀ x y : A, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖inner ℂ (V (J x)) (J y)‖ ≤ K)
    (hfamilies : ∀ a b : A, traceTwoNorm τ a ≤ 1 → traceTwoNorm τ b ≤ 1 →
      ∃ n : ℕ, 0 < n ∧ ∃ f g : Fin n → A,
        (∀ i, traceTwoNorm τ (f i) ≤ 1) ∧
        (∀ i, traceTwoNorm τ (g i) ≤ 1) ∧
        traceTwoNorm τ (finiteSignRightCovariance f) ≤ 2 ∧
        traceTwoNorm τ (finiteSignLeftCovariance f) ≤ 2 ∧
        traceTwoNorm τ (finiteSignRightCovariance g) ≤ 2 ∧
        traceTwoNorm τ (finiteSignLeftCovariance g) ≤ 2 ∧
        (∀ i, inner ℂ (V (J (f i))) (J (g i)) = inner ℂ (V (J a)) (J b))) :
    ‖V‖ ≤ 384 * K := by
  have hK0 : 0 ≤ K := by
    simpa using hK 0 0 (by simp) (by simp)
  have hV : ‖V‖ ≤ 192 * K + ‖V‖ / 2 := by
    apply opNorm_le_of_dense_unit_pairing J hJdense V (by positivity)
    intro a b ha hb
    rw [hJ] at ha hb
    obtain ⟨n, hn, f, g, hf, hg, hQf, hLf, hQg, hLg, hfg⟩ := hfamilies a b ha hb
    let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact pairing_le_of_finite_covariances τ J hJ V f g hK hf hg hQf hLf hQg hLg hfg
  linarith

end

end KadisonKastler

end OAI
