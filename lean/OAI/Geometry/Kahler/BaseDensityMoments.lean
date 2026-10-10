import OAI.Geometry.Kahler.BasePolynomialChange

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace PinchedHartogs.BaseConstruction

lemma polynomial_weight_integrable {W : Base → ℝ} (hW : Continuous W)
    (P : MvPolynomial (Fin 2) ℂ) (U : Base ≃ₗᵢ[ℂ] Base) :
    Integrable (fun ξ : Sphere => MvPolynomial.eval (fun i => U (ξ:Base) i) P*(W ξ:ℂ)) sigma := by
  apply continuous_integrable
  apply Continuous.mul
  · exact P.continuous_eval.comp (continuous_pi (fun i => (EuclideanSpace.proj i).continuous.comp (U.continuous.comp continuous_subtype_val)))
  · exact Complex.continuous_ofReal.comp (hW.comp continuous_subtype_val)

lemma densityCorrection_polynomial_moment {k : ℕ} (hk : 0 < k) {R E : ℝ} (hR : 0 < R) (hER : E < R)
    {f b : ℝ → ℝ} {W : Base → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) (hzero : b 0=0)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (hW : ContDiff ℝ ∞ W)
    {ℓ : ℕ} (hband : PhaseBandwidth W ℓ) (hℓ : ℓ<k) (p : Sphere) (P : MvPolynomial (Fin 2) ℂ) :
    (∫ ξ : Sphere, MvPolynomial.eval (fun i => (ξ:Base) i) P*(densityCorrection k R f b W p ξ:ℂ) ∂sigma)=0 := by
  classical
  obtain ⟨Q,hQ⟩ := polynomial_change_coords (adaptedIsometry p) P
  simp_rw [← hQ]
  clear hQ
  have hc := (densityCorrection_smooth hk hER hf hb hW htail p).continuous
  induction Q using MvPolynomial.induction_on' with
  | monomial d a =>
    simp only [MvPolynomial.eval_monomial,Finsupp.prod_pow,Fin.prod_univ_two]
    have he : ∀ ξ : Sphere, a*((adaptedIsometry p (ξ:Base) 0)^d 0*(adaptedIsometry p (ξ:Base) 1)^d 1)*
        (densityCorrection k R f b W p ξ:ℂ)=a*(adaptedMonomial p (d 0) (d 1) ξ*(densityCorrection k R f b W p ξ:ℂ)) := by
      intro ξ; dsimp [adaptedMonomial]; ring
    simp_rw [he]
    rw [integral_const_mul,densityCorrection_monomial_moment hk hR hER hf hb hode hzero htail hW hband hℓ,mul_zero]
  | add Q₁ Q₂ ih₁ ih₂ =>
    simp only [map_add,add_mul]
    rw [integral_add (polynomial_weight_integrable hc Q₁ (adaptedIsometry p))
      (polynomial_weight_integrable hc Q₂ (adaptedIsometry p)),ih₁,ih₂,add_zero]

lemma density_polynomial_moment {Q : ℕ} (hQ : 2 ≤ Q) {R E : ℝ} (hR : 0 < R) (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) (hzero : b 0=0)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ)
    (p : MvPolynomial (Fin 2) ℂ) :
    (∫ ξ : Sphere, MvPolynomial.eval (fun i => (ξ:Base) i) p*(density Q R f b P j ξ:ℂ) ∂sigma)=
      MvPolynomial.eval (fun _ => 0) p := by
  classical
  have hQ0 : 0 < Q := by omega
  induction j with
  | zero => simpa only [density,Complex.ofReal_one,mul_one] using sigma_represents p
  | succ j ih =>
    have hw := density_smooth hQ0 hER hf hb htail P j
    have hband := density_bandwidth hQ0 hER hf hb htail P j
    have hi : ∀ q ∈ P (Q^(j+1)), Integrable (fun ξ : Sphere =>
        MvPolynomial.eval (fun i => (ξ:Base) i) p*(densityCorrection (Q^(j+1)) R f b (density Q R f b P j) q ξ:ℂ)) sigma := by
      intro q hq
      exact polynomial_weight_integrable (densityCorrection_smooth (pow_pos hQ0 _) hER hf hb hw htail q).continuous p (LinearIsometryEquiv.refl ℂ Base)
    have hiw : Integrable (fun ξ : Sphere => MvPolynomial.eval (fun i => (ξ:Base) i) p*(density Q R f b P j ξ:ℂ)) sigma := by
      simpa using polynomial_weight_integrable hw.continuous p (LinearIsometryEquiv.refl ℂ Base)
    simp only [density,Complex.ofReal_add,Complex.ofReal_sum,mul_add,Finset.mul_sum]
    rw [integral_add hiw (MeasureTheory.integrable_finsetSum _ hi),
      MeasureTheory.integral_finsetSum _ hi,ih]
    have hz : (∑ q ∈ P (Q^(j+1)), ∫ ξ : Sphere, MvPolynomial.eval (fun i => (ξ:Base) i) p*
        (densityCorrection (Q^(j+1)) R f b (density Q R f b P j) q ξ:ℂ) ∂sigma)=0 := by
      apply Finset.sum_eq_zero
      intro q hq
      exact densityCorrection_polynomial_moment (pow_pos hQ0 _) hR hER hf hb hode hzero htail hw hband (densityBandwidth_lt hQ j) q p
    rw [hz,add_zero]

lemma density_mass_one {Q : ℕ} (hQ : 2 ≤ Q) {R E : ℝ} (hR : 0 < R) (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) (hzero : b 0=0)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ) :
    (∫ ξ : Sphere, density Q R f b P j ξ ∂sigma)=1 := by
  have hh := density_polynomial_moment hQ hR hER hf hb hode hzero htail P j (1:MvPolynomial (Fin 2) ℂ)
  simp only [map_one,one_mul,integral_complex_ofReal] at hh
  exact Complex.ofReal_injective hh

end PinchedHartogs.BaseConstruction

end

end OAI
