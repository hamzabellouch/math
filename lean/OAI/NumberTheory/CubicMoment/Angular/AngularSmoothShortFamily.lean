import OAI.NumberTheory.CubicMoment.Angular.AngularBalancedFullSmoothFactor
import OAI.NumberTheory.CubicMoment.Estimates.SmoothShortFamily
import OAI.NumberTheory.CubicMoment.Estimates.AllShortMoments

namespace OAI

/-! Constructing the actual smooth short-factor family used in the exceptional
moments. Finite characters, norm phases and smooth dyads are explicit. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def smoothAngularShortTwist (ℓ : ℤ) {q : Eisenstein} (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (X t : ℝ) (n : Eisenstein) : ℂ :=
  theta ℓ n*smoothShortTwist η W X t n

lemma smoothAngularShortTwist_norm (ℓ : ℤ) {q : Eisenstein} (hq : q ≠ 0)
    (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (hW : ∀ x, ‖W x‖ ≤ 1)
    (X t : ℝ) {n : Eisenstein} (hn : n ≠ 0) :
    ‖smoothAngularShortTwist ℓ η W X t n‖ ≤ 1 := by
  rw [smoothAngularShortTwist,norm_theta_mul hn]
  exact smoothShortTwist_norm hq η W hW X t n

def angularShortFamilyOfSmoothWeights {ι : Type*} (ℓ : ℤ) (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hq : ∀ i, q i ≠ 0) (hW : ∀ i x, ‖W i x‖ ≤ 1) : ShortFactorFamily ι where
  cutoff := fun _ => F
  length := fun _ => X
  coefficient := fun _ => A
  twist := fun _ i => smoothAngularShortTwist ℓ (η i) (W i) (X i) (t i)
  factor_spec := fun _ => hA
  length_ge_one := fun _ => hX
  twist_bound := fun _ i _ hn => smoothAngularShortTwist_norm ℓ (hq i) (η i) (W i)
    (hW i) (X i) (t i) (primary_ne_zero (mem_primaryElementBall.mp hn).1)

lemma angularShortFamily_mixedValue {ι : Type*} (ℓ : ℤ) (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hq : ∀ i, q i ≠ 0) (hW : ∀ i x, ‖W i x‖ ≤ 1)
    (hcut : ∀ i x, 2 < x → W i x = 0) (j : ℕ) (i : ι) (p : Eisenstein × Eisenstein) :
    (angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW).mixedValue j i p =
      primaryAngularShortSmoothSum ℓ (A i) p.1 p.2 (q i) (η i) (W i) (X i/2) (t i) := by
  rw [primaryAngularShortSmoothSum_eq_polynomial ℓ (A i) p.1 p.2 (q i) (η i) (W i)
    (by linarith [hX i] : 0 < X i/2) (hcut i)]
  have hx : 2*(X i/2) = X i := by ring
  rw [hx]
  unfold ShortFactorFamily.mixedValue
  change primaryIdealPolynomial (X i) (A i) (fun n =>
    smoothAngularShortTwist ℓ (η i) (W i) (X i) (t i) n*mixedCubic p.1 p.2 n) = _
  congr 1
  funext n
  unfold smoothAngularShortTwist smoothShortTwist
  ring

lemma angularShortFamily_cubicValue {ι : Type*} (ℓ : ℤ) (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hq : ∀ i, q i ≠ 0) (hW : ∀ i x, ‖W i x‖ ≤ 1)
    (hcut : ∀ i x, 2 < x → W i x = 0) (j : ℕ) (i : ι) (a : Eisenstein) :
    (angularShortFamilyOfSmoothWeights ℓ F X A q η W t hA hX hq hW).cubicValue j i a =
      primaryAngularShortSmoothSum ℓ (A i) a 1 (q i) (η i) (W i) (X i/2) (t i) := by
  rw [← angularShortFamily_mixedValue ℓ F X A q η W t hA hX hq hW hcut j i (a,1)]
  unfold ShortFactorFamily.cubicValue ShortFactorFamily.mixedValue
  congr 1
  funext n
  simp only [mixedCubic,cubicSymbol_one_lower,star_one,mul_one]

end CubicFirstMoment

end

end OAI
