import OAI.NumberTheory.CubicMoment.Estimates.FiniteMellinProduct
import OAI.NumberTheory.CubicMoment.Angular.AngularSmoothShortFamily
import OAI.NumberTheory.CubicMoment.Estimates.ShortTupleMellin

namespace OAI

/-! Mellin separation for the actual smooth short-inverse factors. The
integrand is a product of the original primary sums, with a common shift. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryAngularShortSmoothSum_eq_subtype (ℓ : ℤ) (A : EisensteinArithmeticFunction)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ)
    {X : ℝ} (hX : 0 < X) (hW : ∀ x : ℝ, 2 < x → W x = 0) (t : ℝ) :
    primaryAngularShortSmoothSum ℓ A a b q η W (X/2) t =
      ∑ n : primaryElementBall X,
        ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
          (mixedCubic a b n*η (Ideal.Quotient.mk (modulus q) n)*theta ℓ n*mellinPhase t (norm n))*
            W (norm n/(X/2)) := by
  rw [primaryAngularShortSmoothSum_eq_polynomial ℓ A a b q η W (by linarith : 0 < X/2) hW,
    show 2*(X/2) = X by ring,primaryIdealPolynomial_eq_elements]
  symm
  change (∑ n ∈ (primaryElementBall X).attach, _) = _
  rw [Finset.sum_attach (f := fun n : Eisenstein =>
    ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
      (mixedCubic a b n*η (Ideal.Quotient.mk (modulus q) n)*theta ℓ n*mellinPhase t (norm n))*
        W (norm n/(X/2)))]
  apply Finset.sum_congr rfl
  intro n _
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryAngularShortTupleSum (ℓ : ℤ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (W : ι → ℝ → ℂ) (t : ι → ℝ) (V : ℝ → ℂ) (Z : ℝ) : ℂ :=
  ∑ n : (i : ι) → primaryElementBall (X i),
    (∏ i, ((MvPowerSeries.coeff (idealExponentOf (n i)) (A i):ℝ):ℂ)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*theta ℓ (n i)*
        mellinPhase (t i) (norm (n i)))*W i (norm (n i)/(X i/2)))*
      V ((∏ i, norm (n i))/Z)

theorem primaryAngularShortTupleSum_mellin (ℓ : ℤ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hW : ∀ i x, 2 < x → W i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z) :
    primaryAngularShortTupleSum ℓ X A a b q η W t V Z =
      ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin V ((τ:ℂ)*Complex.I)*(Z:ℂ)^((τ:ℂ)*Complex.I)*
          ∏ i, primaryAngularShortSmoothSum ℓ (A i) a b (q i) (η i) (W i) (X i/2) (t i-τ) := by
  unfold primaryAngularShortTupleSum
  rw [smooth_mellin_product
    (fun i (n : primaryElementBall (X i)) =>
      ((MvPowerSeries.coeff (idealExponentOf n) (A i):ℝ):ℂ)*
        (mixedCubic a b n*η i (Ideal.Quotient.mk (modulus (q i)) n)*theta ℓ n*
          mellinPhase (t i) (norm n))*W i (norm n/(X i/2)))
    (fun i (n : primaryElementBall (X i)) => norm n)
    (fun i n => norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp n.property).1))
    V hV hpos hsm 0 hZ]
  simp only [Complex.ofReal_zero,zero_add]
  congr 1
  apply integral_congr_ae
  filter_upwards with τ
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [primaryAngularShortSmoothSum_eq_subtype ℓ (A i) a b (q i) (η i) (W i) (hX i) (hW i)]
  apply Finset.sum_congr rfl
  intro n _
  have hn : 0 < norm (n:Eisenstein) :=
    norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp n.property).1)
  rw [← mellinPhase_mul_neg_cpow hn]
  ring

end CubicFirstMoment

end

end OAI
