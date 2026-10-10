import OAI.Analysis.FreeEntropy.GaussianEntropyEvent

namespace OAI

universe u1

noncomputable section
open MeasureTheory
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem mvPolynomial_norm_bound [DecidableEq ι] (P : MvPolynomial ι ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∃ m : ℕ,∀x : EuclideanSpace ℝ ι,
      |MvPolynomial.eval (WithLp.ofLp x) P| ≤ C*(1+‖x‖^2)^m := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨|c|,abs_nonneg _,0,by intro x; simp⟩
  | add P Q hP hQ =>
    obtain ⟨C,hC,m,hP⟩ := hP
    obtain ⟨D,hD,k,hQ⟩ := hQ
    refine ⟨C+D,add_nonneg hC hD,max m k,?_⟩
    intro x
    have hbase : 1≤1+‖x‖^2 := by nlinarith [sq_nonneg ‖x‖]
    calc
      _ ≤ |MvPolynomial.eval (WithLp.ofLp x) P|+|MvPolynomial.eval (WithLp.ofLp x) Q| := by simpa only [map_add] using abs_add_le (MvPolynomial.eval (WithLp.ofLp x) P) (MvPolynomial.eval (WithLp.ofLp x) Q)
      _ ≤ C*(1+‖x‖^2)^m+D*(1+‖x‖^2)^k := add_le_add (hP x) (hQ x)
      _ ≤ C*(1+‖x‖^2)^(max m k)+D*(1+‖x‖^2)^(max m k) := add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (le_max_left m k)) hC)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (le_max_right m k)) hD)
      _ = _ := by ring
  | mul_X P i hP =>
    obtain ⟨C,hC,m,hP⟩ := hP
    refine ⟨C,hC,m+1,?_⟩
    intro x
    have hn : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    have hn' : |x i| ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1/2)]
    calc
      _ = |MvPolynomial.eval (WithLp.ofLp x) P| * |x i| := by simp only [map_mul,MvPolynomial.eval_X,abs_mul]
      _ ≤ (C*(1+‖x‖^2)^m)*(1+‖x‖^2) := mul_le_mul (hP x) hn' (abs_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ]; ring
 namespace IsRealPolynomial
 theorem norm_bound {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) :
    ∃ C : ℝ,0 ≤ C ∧ ∃ m : ℕ,∀x : EuclideanSpace ℝ ι,|f (WithLp.ofLp x)| ≤ C*(1+‖x‖^2)^m := by
  obtain ⟨P,rfl⟩ := hf
  exact mvPolynomial_norm_bound P
 theorem smoothed_integrable {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] {s K : ℝ}
    (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) :
    Integrable (fun x => f (WithLp.ofLp x)*smoothedDensity μ s x) := by
  obtain ⟨C,hC,m,hb⟩ := hf.norm_bound
  apply smoothedIntegrable_of_bound μ hs hK hμ
    (((hf.continuous.comp (PiLp.continuous_ofLp 2 _)).mul (smoothedDensity_continuous μ hs)).aestronglyMeasurable) C m
  intro x
  change ‖f (WithLp.ofLp x)*smoothedDensity μ s x‖≤_
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (smoothedDensity_pos μ hs x)]
  exact mul_le_mul_of_nonneg_right (hb x) (smoothedDensity_pos μ hs x).le
 theorem smoothedGradient_integrable {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] {s K : ℝ}
    (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (i : ι) :
    Integrable (fun x => f (WithLp.ofLp x)*smoothedGradient μ s x i) := by
  obtain ⟨C,hC,m,hb⟩ := hf.norm_bound
  apply smoothedIntegrable_of_bound μ hs hK hμ
    ((((hf.continuous.comp (PiLp.continuous_ofLp 2 _)).stronglyMeasurable).mul (smoothedGradient_measurable μ s i)).aestronglyMeasurable) (C*((1+K)/s)) (m+1)
  intro x
  change ‖f (WithLp.ofLp x)*smoothedGradient μ s x i‖≤_
  rw [Real.norm_eq_abs,abs_mul]
  calc
    _ ≤ (C*(1+‖x‖^2)^m)*(((1+K)/s)*(1+‖x‖^2)*smoothedDensity μ s x) :=
      mul_le_mul (hb x) (smoothedGradient_polynomial_bound μ hs le_rfl hK hμ x i) (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring
 theorem hasDerivAt_line {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f)
    (x : EuclideanSpace ℝ ι) (i : ι) (r : ℝ) :
    HasDerivAt (fun t : ℝ => f (WithLp.ofLp (x+t • EuclideanSpace.single i 1)))
      (coordinateDerivative f i (WithLp.ofLp (x+r • EuclideanSpace.single i 1))) r := by
  let y := x+r • EuclideanSpace.single i 1
  have hy : (WithLp.ofLp y) i = x i+r := by simp [y]
  have hd0 := hf.hasDerivAt i (WithLp.ofLp y)
  rw [hy] at hd0
  have hd := hd0.comp r ((hasDerivAt_id r).const_add (x i))
  convert hd using 1 <;> try rfl
  · funext t
    congr 1
    ext j
    by_cases h : j=i
    · subst j; simp
    · simp [y,h,EuclideanSpace.single]
  · simp [y]
 end IsRealPolynomial
end FiniteEntropySeparation

end

end OAI
