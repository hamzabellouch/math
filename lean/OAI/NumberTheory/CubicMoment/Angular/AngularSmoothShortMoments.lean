import OAI.NumberTheory.CubicMoment.Angular.AngularSmoothShortFamily
import OAI.NumberTheory.CubicMoment.Estimates.DominantFactorLengths

namespace OAI

/-! The exceptional-moment machinery applied to constructed smooth factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_all_short_smooth_cubic_moment (ℓ : ℤ) {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (F Y : ℝ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
        (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
        (W : ι → ℝ → ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
      (∀ i, X i ≤ Y^(1-δ)) → Y/C ≤ ∏ i, X i → (∏ i, X i) ≤ C*Y →
      (∀ a ∈ P, gramDyad Y a) →
      (∑ a ∈ P, ‖∏ i, primaryAngularShortSmoothSum ℓ (A i) a 1 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨ε,hε,T,hbound⟩ := all_short_cubic_moment (ι := ι) hδ hC
  refine ⟨ε,hε,T,?_⟩
  intro F Y X A q η W t P hY hA hX hq hW hcut hshort hlo hhi hP
  let K := angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW
  have h := hbound K 0 Y P hY hshort hlo hhi hP
  simpa only [K,angularShortFamily_cubicValue ℓ F X A q η W t hA hX hq hW hcut] using h

theorem angular_all_short_smooth_mixed_moment (ℓ : ℤ) (hHuxley : HuxleyAdditiveLargeSieve)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (F Y : ℝ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
        (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
        (W : ι → ℝ → ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
      (∀ i, X i ≤ Y^(1-δ)) → Y/C ≤ ∏ i, X i → (∏ i, X i) ≤ C*Y →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3:ℝ) ∧ norm p.2 ≤ Y^(1/3:ℝ)) →
      (∑ p ∈ P, ‖∏ i, primaryAngularShortSmoothSum ℓ (A i) p.1 p.2 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨ε,hε,T,hbound⟩ := all_short_mixed_moment (ι := ι) hHuxley hδ hC
  refine ⟨ε,hε,T,?_⟩
  intro F Y X A q η W t P hY hA hX hq hW hcut hshort hlo hhi hP
  let K := angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW
  have h := hbound K 0 Y P hY hshort hlo hhi hP
  simpa only [K,angularShortFamily_mixedValue ℓ F X A q η W t hA hX hq hW hcut] using h

theorem angular_dominant_smooth_cubic_moment_reduction (ℓ : ℤ) {C δ ε : ℝ}
    (hC : 0 < C) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
      (P : Finset Eisenstein) (i : ι),
      (∀ k, ShortArithmeticFactor F (A k)) → (∀ k, 1 ≤ X k) →
      (∀ k, q k ≠ 0) → (∀ k x, ‖W k x‖ ≤ 1) → (∀ k x, 2 < x → W k x = 0) →
      1 ≤ Y → (∀ a ∈ P, primary a) → (∏ k, X k) ≤ C*Y → Y^(1-δ) ≤ X i →
      (∑ a ∈ P, ‖∏ k, primaryAngularShortSmoothSum ℓ (A k) a 1 (q k) (η k) (W k) (X k/2) (t k)‖^2) ≤
        (M*Y^(δ+ε))^2*(∑ a ∈ P, ‖primaryAngularShortSmoothSum ℓ (A i) a 1 (q i) (η i) (W i) (X i/2) (t i)‖^2) := by
  obtain ⟨M,hM,hbound⟩ := dominant_cubic_moment_reduction (ι := ι) hC hδ hε
  refine ⟨M,hM,?_⟩
  intro F Y X A q η W t P i hA hX hq hW hcut hY hP htotal hlong
  let K := angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW
  have h := hbound K 0 Y i P hY hP htotal hlong
  simpa only [K,angularShortFamily_cubicValue ℓ F X A q η W t hA hX hq hW hcut] using h

theorem angular_dominant_smooth_mixed_moment_reduction (ℓ : ℤ) {C δ ε : ℝ}
    (hC : 0 < C) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
      (P : Finset (Eisenstein × Eisenstein)) (i : ι),
      (∀ k, ShortArithmeticFactor F (A k)) → (∀ k, 1 ≤ X k) →
      (∀ k, q k ≠ 0) → (∀ k x, ‖W k x‖ ≤ 1) → (∀ k x, 2 < x → W k x = 0) →
      1 ≤ Y → (∀ p ∈ P, primary p.1 ∧ primary p.2) → (∏ k, X k) ≤ C*Y → Y^(1-δ) ≤ X i →
      (∑ p ∈ P, ‖∏ k, primaryAngularShortSmoothSum ℓ (A k) p.1 p.2 (q k) (η k) (W k) (X k/2) (t k)‖^2) ≤
        (M*Y^(δ+ε))^2*(∑ p ∈ P, ‖primaryAngularShortSmoothSum ℓ (A i) p.1 p.2 (q i) (η i) (W i) (X i/2) (t i)‖^2) := by
  obtain ⟨M,hM,hbound⟩ := dominant_mixed_moment_reduction (ι := ι) hC hδ hε
  refine ⟨M,hM,?_⟩
  intro F Y X A q η W t P i hA hX hq hW hcut hY hP htotal hlong
  let K := angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW
  have h := hbound K 0 Y i P hY hP htotal hlong
  simpa only [K,angularShortFamily_mixedValue ℓ F X A q η W t hA hX hq hW hcut] using h

end CubicFirstMoment

end

end OAI
