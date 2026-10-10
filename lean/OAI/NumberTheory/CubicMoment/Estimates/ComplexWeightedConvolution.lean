import OAI.NumberTheory.CubicMoment.Estimates.PrimaryProductCoefficients
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerConvolution
import OAI.NumberTheory.CubicMoment.Estimates.ArithmeticTwist
import OAI.NumberTheory.CubicMoment.Estimates.ShortConvolutionMoments

namespace OAI

/-! Complex coefficient collection retains the distinct norm and residue
twists of each original prime factor during short inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryComplexProductPolynomial (A : ι → MvPowerSeries EisensteinIdealPrime ℂ)
    (χ : Eisenstein → ℂ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ b ∈ primaryElementBall (2*Y),
    MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i)*χ b*V (norm b/Y)

lemma complex_coeff_product_eq_convolution (A : ι → MvPowerSeries EisensteinIdealPrime ℂ)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i) =
      orderedConvolution (fun _ : ι => primaryElementBall F)
        (fun i n => MvPowerSeries.coeff (idealExponentOf n) (A i)) b := by
  rw [coeff_product_primary_fiber A hb hbF]
  rfl

/-- The global smooth cutoff permits collection on one finite primary
ball, although the unrestricted product support is much larger. -/
theorem primaryComplexProductPolynomial_eq_tuple (A : ι → MvPowerSeries EisensteinIdealPrime ℂ)
    (χ : Eisenstein → ℂ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryComplexProductPolynomial A χ V Y =
      ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        (∏ i, MvPowerSeries.coeff (idealExponentOf (n i)) (A i))*
          χ (∏ i, n i)*V ((∏ i, norm (n i))/Y) := by
  let S : ι → Finset Eisenstein := fun _ => primaryElementBall (2*Y)
  let w : ι → Eisenstein → ℂ := fun i n =>
    MvPowerSeries.coeff (idealExponentOf n) (A i)
  have hc (b : Eisenstein) (hb : b ∈ primaryElementBall (2*Y)) :
      MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i) = orderedConvolution S w b :=
    complex_coeff_product_eq_convolution A (mem_primaryElementBall.mp hb).1 (mem_primaryElementBall.mp hb).2
  unfold primaryComplexProductPolynomial
  have hs : (∑ b ∈ primaryElementBall (2*Y), orderedConvolution S w b*(χ b*V (norm b/Y))) =
      ∑ b ∈ orderedConvolutionSupport S, orderedConvolution S w b*(χ b*V (norm b/Y)) := by
    apply Finset.sum_bij_ne_zero (fun b _ _ => b)
    · intro b _ hn
      by_contra hb
      rw [orderedConvolution_eq_zero_of_not_mem S w hb,zero_mul] at hn
      exact hn rfl
    · intro b _ _ c _ _ h
      exact h
    · intro b hb hn
      have hp : primary b := by
        change b ∈ (Fintype.piFinset S).image (fun n => ∏ i, n i) at hb
        obtain ⟨n,hnmem,rfl⟩ := Finset.mem_image.mp hb
        have hn' : n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)) := hnmem
        have hni (i : ι) : n i ∈ primaryElementBall (2*Y) := (Fintype.mem_piFinset.mp hn') i
        exact primary_finset_prod Finset.univ n (fun i _ => (mem_primaryElementBall.mp (hni i)).1)
      have hv : V (norm b/Y) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).2).2
      have hbn : norm b ≤ 2*Y := by
        by_contra hgt
        exact hv (hV _ ((lt_div_iff₀ hY).mpr (lt_of_not_ge hgt)))
      exact ⟨b,mem_primaryElementBall.mpr ⟨hp,hbn⟩,hn,rfl⟩
    · intro b _ _
      rfl
  calc
    _ = ∑ b ∈ primaryElementBall (2*Y), orderedConvolution S w b*χ b*V (norm b/Y) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hc b hb]
    _ = ∑ b ∈ primaryElementBall (2*Y), orderedConvolution S w b*(χ b*V (norm b/Y)) := by
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := hs
    _ = _ := by
      rw [orderedConvolution_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [norm_finset_prod]
      dsimp only [w]
      ring

/-- Independent residue characters and Mellin heights remain attached to
individual factors after exact collection. -/
theorem twistedProductPolynomial_eq_unsplit (A : ι → EisensteinArithmeticFunction)
    {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hη : ∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1)
    (t : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryComplexProductPolynomial (fun i => twistArithmetic (q i) (η i) (t i) (A i))
      (mixedCubic a b) V Y = primaryUnsplitTuple A a b q η t V Y := by
  rw [primaryComplexProductPolynomial_eq_tuple _ _ V hY hV]
  unfold primaryUnsplitTuple
  apply Finset.sum_congr rfl
  intro n hn
  have hp (i : ι) : primary (n i) :=
    (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1
  simp_rw [twistArithmetic_coeff_primary _ _ (hη _) _ _ (hp _)]
  rw [mixedCubic_prod _ _ ha hb]
  unfold primaryTupleCore
  rw [← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

end CubicFirstMoment

end

end OAI
