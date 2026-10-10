import OAI.NumberTheory.CubicMoment.Estimates.PrimaryProductCoefficients
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerConvolution

namespace OAI

/-! Collecting the actual weighted element tuples gives exactly the
primary polynomial of the product of their ideal arithmetic functions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryConvolutionPolynomial (A : ι → EisensteinArithmeticFunction)
    (χ : Eisenstein → ℂ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ b ∈ primaryElementBall (2*Y),
    ((MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i):ℝ):ℂ)*χ b*V (norm b/Y)

lemma coeff_product_eq_convolution (A : ι → EisensteinArithmeticFunction)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    ((MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i):ℝ):ℂ) =
      orderedConvolution (fun _ : ι => primaryElementBall F)
        (fun i n => ((MvPowerSeries.coeff (idealExponentOf n) (A i):ℝ):ℂ)) b := by
  rw [coeff_product_primary_fiber A hb hbF,Complex.ofReal_sum]
  unfold orderedConvolution
  apply Finset.sum_congr rfl
  intro n _
  exact Complex.ofReal_prod _ _

/-- The global smooth cutoff permits collection on one finite primary
ball, although the unrestricted product support is much larger. -/
theorem primaryConvolutionPolynomial_eq_tuple (A : ι → EisensteinArithmeticFunction)
    (χ : Eisenstein → ℂ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryConvolutionPolynomial A χ V Y =
      ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        (∏ i, ((MvPowerSeries.coeff (idealExponentOf (n i)) (A i):ℝ):ℂ))*
          χ (∏ i, n i)*V ((∏ i, norm (n i))/Y) := by
  let S : ι → Finset Eisenstein := fun _ => primaryElementBall (2*Y)
  let w : ι → Eisenstein → ℂ := fun i n =>
    ((MvPowerSeries.coeff (idealExponentOf n) (A i):ℝ):ℂ)
  have hc (b : Eisenstein) (hb : b ∈ primaryElementBall (2*Y)) :
      ((MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i):ℝ):ℂ) = orderedConvolution S w b :=
    coeff_product_eq_convolution A (mem_primaryElementBall.mp hb).1 (mem_primaryElementBall.mp hb).2
  unfold primaryConvolutionPolynomial
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

end CubicFirstMoment

end

end OAI
