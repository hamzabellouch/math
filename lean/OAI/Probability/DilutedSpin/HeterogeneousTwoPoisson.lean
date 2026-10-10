import OAI.Probability.DilutedSpin.UniformIndexCoupling

namespace OAI

section
section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {I J : Type*} [MeasurableSpace I] [MeasurableSpace J]
    (μ : Measure I) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]

/-- Quadratic integrability for a genuine random-dimensional root block. -/
theorem poisson_integrable_root_squared (r : ℝ≥0)
    {F : (n : ℕ) → RootPath I n → ℝ} {A D : ℝ}
    (hF : ∀ n x, |F n x| ≤ A+D*n) (c : ℝ) :
    Integrable (fun n : ℕ => ∫ x, (F n x-c)^2 ∂rootLaw n (fun _ => μ)) (poissonMeasure r) := by
  apply poisson_integrable_quadratic r (A := 2*(|A|+|c|)^2) (B := 2*D^2)
  intro n
  apply abs_integral_le_bound
  intro x
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : |F n x-c| ≤ |A|+|c|+|D| * n := by
    calc
      _ ≤ |F n x|+|c| := abs_sub _ _
      _ ≤ (A+D*n)+|c| := add_le_add (hF n x) le_rfl
      _ ≤ |A|+|c|+|D| * n := by
        have ha := le_abs_self A
        have hd := mul_le_mul_of_nonneg_right (le_abs_self D) hn
        linarith
  rw [abs_of_nonneg (sq_nonneg _)]
  have hs : (F n x-c)^2 ≤ (|A|+|c|+|D| * n)^2 := by
    nlinarith [sq_abs (F n x-c),abs_nonneg (F n x-c)]
  have hscaled_sq : (|D| * (n : ℝ))^2 = D^2 * (n : ℝ)^2 := by
    rw [mul_pow, sq_abs]
  nlinarith [sq_nonneg ((|A|+|c|)-|D| * n)]

/-- Two independent Poisson families, without converting both counts into
one process or conditioning away either of the count fluctuations. -/
theorem two_poisson_roots_second_moment (r s : ℝ≥0)
    {F : (k : ℕ) → RootPath I k → (n : ℕ) → RootPath J n → ℝ}
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ k n, Measurable (fun z : RootPath I k × RootPath J n => F k z.1 n z.2))
    (hB : ∀ k x n y, |F k x n y| ≤ B+C*k+D*n)
    (hrep1 : ∀ k (i : Fin k) x z n y, |F k x n y-F k (replaceRoot k x i z) n y| ≤ 2*C)
    (hadd1 : ∀ k z x n y, |F (k+1) (z,x) n y-F k x n y| ≤ C)
    (hrep2 : ∀ k x n (i : Fin n) y z, |F k x n y-F k x n (replaceRoot n y i z)| ≤ 2*D)
    (hadd2 : ∀ k x n z y, |F k x (n+1) (z,y)-F k x n y| ≤ D) (c : ℝ) :
    (∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y, (F k x n y-c)^2
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ) ∂poissonMeasure r) ≤
      3*C^2*(r : ℝ)+3*D^2*(s : ℝ)+
      (poissonRootAverage μ r (fun k x => poissonRootAverage ν s (F k x))-c)^2 := by
  let G (k : ℕ) (x : RootPath I k) := poissonRootAverage ν s (F k x)
  have hFm (k : ℕ) (x : RootPath I k) (n : ℕ) : Measurable (F k x n) :=
    (hF k n).comp (measurable_const.prodMk measurable_id)
  have hGm (k : ℕ) : Measurable (G k) := measurable_poissonRootAverage ν s (hF k)
  have hGB (k : ℕ) (x : RootPath I k) : |G k x| ≤ B+C*k+D*(s : ℝ) :=
    poissonRootAverage_bound ν s (hB k x)
  have hGr (k : ℕ) (i : Fin k) (x : RootPath I k) (z : I) :
      |G k x-G k (replaceRoot k x i z)| ≤ 2*C :=
    poissonRootAverage_stability ν s (hFm k x) (hFm k (replaceRoot k x i z))
      (hB k x) (hB k (replaceRoot k x i z)) (hrep1 k i x z)
  have hGa (k : ℕ) (z : I) (x : RootPath I k) : |G (k+1) (z,x)-G k x| ≤ C := by
    apply poissonRootAverage_stability ν s (A := B+C*(k+1)) (B := D)
      (hFm (k+1) (z,x)) (hFm k x)
    · simpa using hB (k+1) (z,x)
    · intro n y
      have h := hB k x n y
      have hk : (k : ℝ) ≤ k+1 := le_add_of_nonneg_right zero_le_one
      nlinarith
    · exact hadd1 k z x
  have houter := poisson_root_second_moment μ r hGm hGB hC hGr hGa c
  have hins (k : ℕ) (x : RootPath I k) :=
    poisson_root_second_moment ν s (hFm k x) (hB k x) hD (hrep2 k x) (hadd2 k x) c
  have hsqi (k : ℕ) : Integrable (fun x => (G k x-c)^2) (rootLaw k (fun _ => μ)) :=
    ((bounded_memLp (hGm k) (hGB k) 2).sub (memLp_const c)).integrable_sq
  have hstep (k : ℕ) :
      (∫ x, ∫ n : ℕ, ∫ y, (F k x n y-c)^2 ∂rootLaw n (fun _ => ν)
        ∂poissonMeasure s ∂rootLaw k (fun _ => μ)) ≤
      ((2*D)^2/2+D^2)*(s : ℝ) + ∫ x, (G k x-c)^2 ∂rootLaw k (fun _ => μ) := by
    have h := integral_mono_of_nonneg (μ := rootLaw k (fun _ => μ))
      (ae_of_all _ (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))))
      ((integrable_const (((2*D)^2/2+D^2)*(s : ℝ))).add (hsqi k)) (ae_of_all _ (hins k))
    simp only [Pi.add_apply] at h
    rwa [integral_add (integrable_const _) (hsqi k), integral_const,
      probReal_univ,smul_eq_mul,one_mul] at h
  have hsqint := poisson_integrable_root_squared μ r (A := B+D*(s : ℝ)) (D := C)
    (fun k x => by convert hGB k x using 1; ring) c
  have hnonneg (k : ℕ) : 0 ≤ (∫ x, ∫ n : ℕ, ∫ y, (F k x n y-c)^2
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)) :=
    integral_nonneg (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _)))
  have h := integral_mono_of_nonneg (μ := poissonMeasure r)
    (ae_of_all _ hnonneg)
    ((integrable_const (((2*D)^2/2+D^2)*(s : ℝ))).add hsqint) (ae_of_all _ hstep)
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) hsqint,integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  dsimp only [G] at houter
  nlinarith

end DilutedSpinGlass
end

end

end OAI
