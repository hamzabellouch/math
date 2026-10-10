import OAI.NumberTheory.CubicMoment.Estimates.BalancedFullSmoothFactor
import OAI.NumberTheory.CubicMoment.Estimates.AllShortMoments

namespace OAI

/-! Constructing the actual smooth short-factor family used in the exceptional
moments. Finite characters, norm phases and smooth dyads are explicit. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def smoothShortTwist {q : Eisenstein} (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (X t : ℝ) (n : Eisenstein) : ℂ :=
  η (Ideal.Quotient.mk (modulus q) n)*mellinPhase t (norm n)*W (norm n/(X/2))

lemma smoothShortTwist_norm {q : Eisenstein} (hq : q ≠ 0)
    (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (hW : ∀ x, ‖W x‖ ≤ 1)
    (X t : ℝ) (n : Eisenstein) : ‖smoothShortTwist η W X t n‖ ≤ 1 := by
  rw [smoothShortTwist,norm_mul,norm_mul,mellinPhase_norm,mul_one]
  exact (mul_le_mul (residueChar_norm_le_one hq η _) (hW _)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

def shortFamilyOfSmoothWeights {ι : Type*} (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hq : ∀ i, q i ≠ 0) (hW : ∀ i x, ‖W i x‖ ≤ 1) : ShortFactorFamily ι where
  cutoff := fun _ => F
  length := fun _ => X
  coefficient := fun _ => A
  twist := fun _ i => smoothShortTwist (η i) (W i) (X i) (t i)
  factor_spec := fun _ => hA
  length_ge_one := fun _ => hX
  twist_bound := fun _ i n _ => smoothShortTwist_norm (hq i) (η i) (W i) (hW i) (X i) (t i) n

lemma smoothShortFamily_mixedValue {ι : Type*} (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hq : ∀ i, q i ≠ 0) (hW : ∀ i x, ‖W i x‖ ≤ 1)
    (hcut : ∀ i x, 2 < x → W i x = 0) (j : ℕ) (i : ι) (p : Eisenstein × Eisenstein) :
    (shortFamilyOfSmoothWeights F X A q η W t hA hX hq hW).mixedValue j i p =
      primaryShortSmoothSum (A i) p.1 p.2 (q i) (η i) (W i) (X i/2) (t i) := by
  rw [primaryShortSmoothSum_eq_polynomial (A i) p.1 p.2 (q i) (η i) (W i)
    (by linarith [hX i] : 0 < X i/2) (hcut i)]
  have hx : 2*(X i/2) = X i := by ring
  rw [hx]
  unfold ShortFactorFamily.mixedValue
  change primaryIdealPolynomial (X i) (A i) (fun n =>
    smoothShortTwist (η i) (W i) (X i) (t i) n*mixedCubic p.1 p.2 n) = _
  congr 1
  funext n
  unfold smoothShortTwist
  ring

lemma smoothShortFamily_cubicValue {ι : Type*} (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hq : ∀ i, q i ≠ 0) (hW : ∀ i x, ‖W i x‖ ≤ 1)
    (hcut : ∀ i x, 2 < x → W i x = 0) (j : ℕ) (i : ι) (a : Eisenstein) :
    (shortFamilyOfSmoothWeights F X A q η W t hA hX hq hW).cubicValue j i a =
      primaryShortSmoothSum (A i) a 1 (q i) (η i) (W i) (X i/2) (t i) := by
  rw [← smoothShortFamily_mixedValue F X A q η W t hA hX hq hW hcut j i (a,1)]
  unfold ShortFactorFamily.cubicValue ShortFactorFamily.mixedValue
  congr 1
  funext n
  simp only [mixedCubic,cubicSymbol_one_lower,star_one,mul_one]

end CubicFirstMoment

end

end OAI
