import OAI.NumberTheory.DirichletL.Hecke.DetectorRowwisePolynomial
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowwiseChain

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwiseMarked
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorRowwisePolynomial

theorem marked_rowwise {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (inv : Bool) (W : ℝ→ℂ) (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (P : ι→ℂ) (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (h0 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv W D x y*P i‖^2≤E)
    (h1 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv (logProfile W) D x y*P i‖^2≤E)
    (h2 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv (logProfile (logProfile W)) D x y*P i‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) inv W D (σ i) (freq i)*P i‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  let M (n : ℕ) (i : ι) (x y : ℝ) :=
    polynomial (χ i) inv ((logProfile^[n]) W) D x y*P i
  have hc1 := logProfile_cover W D S hc
  have hc2 := logProfile_cover (logProfile W) D S hc1
  have cm (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (M n i)) := by
    interval_cases n
    all_goals
      dsimp [M,Function.uncurry]
      apply Continuous.mul_const
    · exact polynomial_continuous (χ i) inv W D hD S hc
    · exact polynomial_continuous (χ i) inv (logProfile W) D hD S hc1
    · exact polynomial_continuous (χ i) inv (logProfile (logProfile W)) D hD S hc2
  have dx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x := by
    interval_cases n
    · simpa [M] using (polynomial_sigma_deriv (χ i) inv W D x y hD S hc).mul_const (P i)
    · simpa [M] using (polynomial_sigma_deriv (χ i) inv (logProfile W) D x y hD S hc1).mul_const (P i)
  have dy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (M n i x) (I*M (n+1) i x y) y := by
    interval_cases n
    · simpa [M,mul_assoc] using (polynomial_freq_deriv (χ i) inv W D x y hD S hc).mul_const (P i)
    · simpa [M,mul_assoc] using (polynomial_freq_deriv (χ i) inv (logProfile W) D x y hD S hc1).mul_const (P i)
  have he (n : ℕ) (hn : n≤2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖M n i x y‖^2≤E := by
    interval_cases n
    · simpa [M] using h0 x hx y hy
    · simpa [M] using h1 x hx y hy
    · simpa [M] using h2 x hx y hy
  exact chain_rowwise rows M cm dx dy a b c d E hab hcd σ freq hσ hf he

end SevenEighths.HeckeDetectorRowwiseMarked

end

end OAI
