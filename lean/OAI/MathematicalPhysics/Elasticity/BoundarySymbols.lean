import OAI.MathematicalPhysics.Elasticity.BoundaryCalculus

namespace OAI

section
/-! Literal anisotropic oscillatory Gaussian boundary profiles, with actual
Frechet derivatives.  The small parameter is never assigned a symbolic DN map. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryProfile
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryScaling ElasticityBoundaryWeights
-- All coordinate spaces here carry the standard finite-product Euclidean topology.
abbrev Y := Fin 3 → ℝ

def phase (δ : ℝ) : MP := C (Complex.I / (δ : ℂ))*X 0-X 2-((X 0)^2+(X 1)^2)
def envelope (δ : ℝ) (y : Y) : ℂ := Complex.exp (value (phase δ) y)
def profile (δ : ℝ) (p : MP) (y : Y) : ℂ := envelope δ y*value p y

def conjugateDerivative (δ : ℝ) (j : Fin 3) : MP →ₗ[ℂ] MP :=
  (pderiv j).toLinearMap + LinearMap.mulLeft ℂ (pderiv j (phase δ))

lemma conjugateDerivative_apply (δ : ℝ) (j : Fin 3) (p : MP) :
    conjugateDerivative δ j p=pderiv j p+pderiv j (phase δ)*p := rfl

lemma smooth_profile (δ : ℝ) (p : MP) : ContDiff ℝ (⊤ : ℕ∞) (profile δ p) :=
  ((smooth_value (phase δ)).cexp).mul (smooth_value p)

/-- Each formal conjugated partial is exactly the Frechet derivative of the
actual function in a coordinate direction. -/
theorem fderiv_profile_basis (δ : ℝ) (p : MP) (y : Y) (j : Fin 3) :
    fderiv ℝ (profile δ p) y (Pi.single j 1)=profile δ (conjugateDerivative δ j p) y := by
  have h := ((hasFDerivAt_value (phase δ) y).cexp).mul (hasFDerivAt_value p y)
  change HasFDerivAt (profile δ p) _ y at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, differential_basis]
  simp only [profile, envelope, conjugateDerivative_apply, value_add, value_mul]
  ring

/-- Polynomial dependence on the concentration parameter after multiplying the
physical derivative by delta squared. -/
def D (δ : ℝ) (j : Fin 3) : MP →ₗ[ℂ] MP :=
  if j=0 then Complex.I • LinearMap.id + (δ:ℂ) •
    ((pderiv 0).toLinearMap-(2:ℂ) • LinearMap.mulLeft ℂ (X 0))
  else if j=1 then (δ:ℂ) • ((pderiv 1).toLinearMap-(2:ℂ) • LinearMap.mulLeft ℂ (X 1))
  else (pderiv 2).toLinearMap-LinearMap.id

lemma phase_partial (δ : ℝ) (j : Fin 3) : pderiv j (phase δ) =
    ![C (Complex.I/(δ:ℂ))-(2:ℂ) • X 0, -(2:ℂ) • X 1, -1] j := by
  fin_cases j <;>
    simp [phase, smul_eq_C_mul] <;> ring_nf <;> exact (map_natCast C 2).symm

lemma conjugate_zero (δ : ℝ) (p : MP) :
    conjugateDerivative δ 0 p = (Complex.I/(δ:ℂ)) • p +
      (pderiv 0 p-(2:ℂ) • (X 0*p)) := by
  simp [conjugateDerivative_apply, phase_partial, smul_eq_C_mul]
  ring

lemma conjugate_one (δ : ℝ) (p : MP) :
    conjugateDerivative δ 1 p = pderiv 1 p-(2:ℂ) • (X 1*p) := by
  simp [conjugateDerivative_apply, phase_partial, smul_eq_C_mul]
  ring

lemma conjugate_two (δ : ℝ) (p : MP) :
    conjugateDerivative δ 2 p = pderiv 2 p-p := by
  simp [conjugateDerivative_apply, phase_partial, sub_eq_add_neg]

lemma D_eq_scaled {δ : ℝ} (hδ : δ≠0) (j : Fin 3) (p : MP) :
    D δ j p = ((δ^2*scaleFactor δ⁻¹ j : ℝ):ℂ) • conjugateDerivative δ j p := by
  have hs : δ^2*scaleFactor δ⁻¹ j = if j=2 then 1 else δ := by
    unfold scaleFactor
    split_ifs <;> field_simp
  rw [hs]
  have hc : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hδ
  have hid : (δ:ℂ)*(Complex.I/(δ:ℂ))=Complex.I := by field_simp
  fin_cases j <;> simp [D, conjugate_zero, conjugate_one, conjugate_two,
    smul_add, smul_smul, hid]

lemma scale_basis (δ : ℝ) (j : Fin 3) :
    scale δ (Pi.single j 1)=scaleFactor δ j • (Pi.single j 1) := by
  ext i
  by_cases hi : i=j
  · subst i; simp
  · simp [hi]

def physicalProfile (δ : ℝ) (p : MP) (z : Y) : ℂ := profile δ p (scale δ⁻¹ z)

lemma smooth_physicalProfile (δ : ℝ) (p : MP) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalProfile δ p) :=
  (smooth_profile δ p).comp (scale δ⁻¹).contDiff

/-- The true derivative in unscaled boundary coordinates. -/
theorem fderiv_physicalProfile_basis {δ : ℝ} (hδ : δ≠0) (p : MP) (z : Y) (j : Fin 3) :
    fderiv ℝ (physicalProfile δ p) z (Pi.single j 1) =
      ((δ^2)⁻¹:ℝ) • physicalProfile δ (D δ j p) z := by
  change fderiv ℝ (profile δ p ∘ scale δ⁻¹) z _=_
  rw [fderiv_comp z ((smooth_profile δ p).differentiable (by simp)).differentiableAt
    (scale δ⁻¹).differentiableAt, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply, scale_basis, map_smul,
    fderiv_profile_basis, D_eq_scaled hδ]
  simp only [physicalProfile, profile, value_smul, Complex.real_smul]
  have hc : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hδ
  push_cast
  field_simp

lemma phase_real (δ : ℝ) (y : Y) : (value (phase δ) y).re = -y 2-(y 0)^2-(y 1)^2 := by
  simp [phase, value, Complex.div_re, ← Complex.ofReal_pow]
  ring

lemma envelope_norm (δ : ℝ) (y : Y) :
    ‖envelope δ y‖=Real.exp (-y 2-(y 0)^2-(y 1)^2) := by
  rw [envelope, Complex.norm_exp, phase_real]

/-- Modulus squared is the proved integrable Gaussian/normal weight; the fast
oscillation does not alter it at any nonzero scale. -/
theorem profile_square_weight (δ : ℝ) (p : MP) (y : Y) :
    ({y : Y | 0<y 2} : Set Y).indicator (fun y => ‖profile δ p y‖^2) y =
      ‖value p y‖^2 * weight 2 y := by
  by_cases hy : 0<y 2
  · simp [Set.indicator, hy, profile, mul_pow, envelope_norm,
      weight, Fin.prod_univ_three, factor]
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    rw [mul_comm (Real.exp _)]
    congr 2
    ring
  · simp [Set.indicator, hy, weight, Fin.prod_univ_three, factor]

end ElasticityBoundaryProfile

end
end
section
/-! Coefficientwise linear differential operators in a genuine finite
parameter polynomial. Used to construct, not postulate, Taylor transport
coefficients of the physical boundary layer. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryParameter
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

def coeffMap (T : A →ₗ[ℂ] B) : Polynomial A →ₗ[ℂ] Polynomial B :=
  (PolynomialModule.equivPolynomial (R := ℂ)).toLinearMap.comp
    ((PolynomialModule.map ℂ T).comp
      (PolynomialModule.equivPolynomial (R := ℂ)).symm.toLinearMap)

@[simp] lemma coeffMap_monomial (T : A →ₗ[ℂ] B) (n : ℕ) (a : A) :
    coeffMap T (Polynomial.monomial n a)=Polynomial.monomial n (T a) := by
  simp [coeffMap]

@[simp] lemma coeffMap_coeff (T : A →ₗ[ℂ] B) (q : Polynomial A) (n : ℕ) :
    (coeffMap T q).coeff n=T (q.coeff n) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial k a =>
      rw [coeffMap_monomial]
      simp only [Polynomial.coeff_monomial]
      split_ifs <;> simp

lemma coeffMap_C (T : A →ₗ[ℂ] B) (a : A) :
    coeffMap T (Polynomial.C a)=Polynomial.C (T a) := by
  simpa only [Polynomial.monomial_zero_left] using coeffMap_monomial T 0 a

lemma coeffMap_X_mul (T : A →ₗ[ℂ] B) (q : Polynomial A) :
    coeffMap T (Polynomial.X*q)=Polynomial.X*coeffMap T q := by
  apply Polynomial.ext
  intro n
  cases n <;> simp [coeffMap_coeff, Polynomial.coeff_X_mul]

lemma coeffMap_monomial_one_mul (T : A →ₗ[ℂ] B) (n : ℕ) (q : Polynomial A) :
    coeffMap T (Polynomial.monomial n 1*q)=Polynomial.monomial n 1*coeffMap T q := by
  rw [Polynomial.monomial_one_right_eq_X_pow, Polynomial.monomial_one_right_eq_X_pow]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc, coeffMap_X_mul, ih, ← mul_assoc, ← pow_succ']

lemma eval_coeffMap (T : A →ₗ[ℂ] B) (q : Polynomial A) (c : ℂ) :
    (coeffMap T q).eval (algebraMap ℂ B c)=T (q.eval (algebraMap ℂ A c)) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | monomial n a =>
      rw [coeffMap_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial]
      simp only [← map_pow]
      rw [mul_comm, ← Algebra.smul_def, mul_comm a, ← Algebra.smul_def, T.map_smul]

/-- The parameter-independent and linear parts of the actual scaled derivative. -/
def E₀ (j : Fin 3) : MP →ₗ[ℂ] MP :=
  if j=0 then Complex.I • LinearMap.id else if j=1 then 0
  else (pderiv 2).toLinearMap-LinearMap.id

def E₁ (j : Fin 3) : MP →ₗ[ℂ] MP :=
  if j=0 then (pderiv 0).toLinearMap-(2:ℂ) • LinearMap.mulLeft ℂ (X 0)
  else if j=1 then (pderiv 1).toLinearMap-(2:ℂ) • LinearMap.mulLeft ℂ (X 1) else 0

lemma D_expansion (δ : ℝ) (j : Fin 3) : D δ j = E₀ j+(δ:ℂ) • E₁ j := by
  fin_cases j <;> simp [D,E₀,E₁]

def PD (j : Fin 3) : Polynomial MP →ₗ[ℂ] Polynomial MP :=
  coeffMap (E₀ j) + (LinearMap.mulLeft ℂ Polynomial.X).comp (coeffMap (E₁ j))

lemma PD_apply (j : Fin 3) (q : Polynomial MP) :
    PD j q=coeffMap (E₀ j) q+Polynomial.X*coeffMap (E₁ j) q := rfl

lemma eval_PD (j : Fin 3) (q : Polynomial MP) (δ : ℝ) :
    (PD j q).eval (C (δ:ℂ)) = D δ j (q.eval (C (δ:ℂ))) := by
  rw [PD_apply, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  have hC : C (δ:ℂ) = algebraMap ℂ MP (δ:ℂ) := rfl
  rw [hC, eval_coeffMap, eval_coeffMap, D_expansion]
  change _ = E₀ j (q.eval (algebraMap ℂ MP (δ:ℂ))) +
    (δ:ℂ) • E₁ j (q.eval (algebraMap ℂ MP (δ:ℂ)))
  rw [Algebra.smul_def]

lemma PD_monomial_one_mul (j : Fin 3) (n : ℕ) (q : Polynomial MP) :
    PD j (Polynomial.monomial n 1*q)=Polynomial.monomial n 1*PD j q := by
  rw [PD_apply, coeffMap_monomial_one_mul, coeffMap_monomial_one_mul, PD_apply]
  ring

end ElasticityBoundaryParameter

end
end
section
/-! Flat-boundary calculation for the missing DN-to-all-jets step.
This is ONLY the constant-coefficient principal boundary symbol, not the
boundary localization theorem. Frequency is the unit first tangential
covector, the domain is t>0, and the outward normal is -e₃.
-/
noncomputable section
open scoped Matrix
namespace ElasticityBoundarySymbol
abbrev F := Fin 3 → ℂ

def slope (l m : ℂ) (f : F) : F :=
  ![-((l+m)/(l+3*m))*(f 0+Complex.I*f 2),0,
    ((l+m)/(l+3*m))*(f 2-Complex.I*f 0)]

def solution (l m : ℂ) (f : F) (t : ℝ) : F :=
  fun j => Complex.exp (-(t : ℂ))*(f j+(t : ℂ)*slope l m f j)

def first (l m : ℂ) (f : F) (t : ℝ) : F :=
  fun j => Complex.exp (-(t : ℂ))*(slope l m f j-f j-(t : ℂ)*slope l m f j)

def second (l m : ℂ) (f : F) (t : ℝ) : F :=
  fun j => Complex.exp (-(t : ℂ))*(f j+((t : ℂ)-2)*slope l m f j)

lemma solution_derivative (l m : ℂ) (f : F) (t : ℝ) (j : Fin 3) :
    HasDerivAt (fun s => solution l m f s j) (first l m f t j) t := by
  have he : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ)))
      (-Complex.exp (-(t : ℂ))) t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).neg).cexp
  convert he.mul ((Complex.ofRealCLM.hasDerivAt.mul_const (slope l m f j)).const_add (f j)) using 1 <;>
    first | rfl | (dsimp [solution,first]; ring)

lemma first_derivative (l m : ℂ) (f : F) (t : ℝ) (j : Fin 3) :
    HasDerivAt (fun s => first l m f s j) (second l m f t j) t := by
  have he : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ)))
      (-Complex.exp (-(t : ℂ))) t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).neg).cexp
  convert he.mul ((Complex.ofRealCLM.hasDerivAt.mul_const (slope l m f j)).const_sub
    (slope l m f j-f j)) using 1 <;>
    first | rfl | (dsimp [first,second]; ring)

@[simp] lemma solution_boundary (l m : ℂ) (f : F) : solution l m f 0=f := by
  ext j
  simp [solution]

def fourierDiv (l m : ℂ) (f : F) (t : ℝ) : ℂ :=
  Complex.I*solution l m f t 0+first l m f t 2

def fourierGradDiv (l m : ℂ) (f : F) (t : ℝ) : F :=
  ![Complex.I*fourierDiv l m f t,0,
    Complex.I*first l m f t 0+second l m f t 2]

def fourierPhysical (l m : ℂ) (f : F) (t : ℝ) : F :=
  fun j => m*(second l m f t j-solution l m f t j)+(l+m)*fourierGradDiv l m f t j

/-- Literal Fourier-transformed constant elasticity PDE, not a prescribed
symbol assigned by definition to the DN map. -/
theorem solution_physical (l m : ℂ) (hp : l+3*m≠0) (f : F) (t : ℝ) :
    fourierPhysical l m f t=0 := by
  have hq : m*3+l≠0 := by convert hp using 1; ring
  ext j
  fin_cases j <;>
    dsimp [fourierPhysical,fourierGradDiv,fourierDiv,solution,first,second,slope]
  all_goals field_simp [hp]
  all_goals ring_nf
  all_goals norm_num
  all_goals field_simp [hq]
  all_goals ring

def traction (l m : ℂ) (f : F) : F :=
  ![-m*(first l m f 0 0+Complex.I*f 2),-m*first l m f 0 1,
    -l*fourierDiv l m f 0-2*m*first l m f 0 2]

def symbol (l m : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![2*m*(l+2*m)/(l+3*m),0,-Complex.I*(2*m^2/(l+3*m));
    0,m,0;
    Complex.I*(2*m^2/(l+3*m)),0,2*m*(l+2*m)/(l+3*m)]

theorem traction_symbol (l m : ℂ) (hp : l+3*m≠0) (f : F) :
    traction l m f=(symbol l m).mulVec f := by
  have hq : l+m*3≠0 := by convert hp using 1; ring
  have hq' : m*3+l≠0 := by convert hp using 1; ring
  ext j
  fin_cases j <;>
    simp [traction,first,fourierDiv,solution,slope,symbol,Matrix.mulVec,
      dotProduct,Fin.sum_univ_three]
  all_goals ring_nf
  all_goals field_simp [hq,hq']
  all_goals ring

/-- Both constants are encoded in the principal symbol. -/
theorem symbol_injective {l₁ m₁ l₂ m₂ : ℂ} (hm : m₁≠0)
    (hp₁ : l₁+3*m₁≠0) (hp₂ : l₂+3*m₂≠0)
    (hs : symbol l₁ m₁=symbol l₂ m₂) : l₁=l₂ ∧ m₁=m₂ := by
  have he : m₁=m₂ := by
    simpa [symbol] using congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 1 1) hs
  subst m₂
  have h02 : -Complex.I*(2*m₁^2/(l₁+3*m₁)) = -Complex.I*(2*m₁^2/(l₂+3*m₁)) := by
    simpa [symbol] using congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 2) hs
  have hd := (mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) h02)
  have hx := (div_eq_div_iff hp₁ hp₂).mp hd
  have hn : (2 : ℂ)*m₁^2≠0 := mul_ne_zero two_ne_zero (pow_ne_zero _ hm)
  have hden := mul_left_cancel₀ hn hx
  exact ⟨(add_right_cancel hden).symm,rfl⟩

theorem real_symbol_injective {l₁ m₁ l₂ m₂ : ℝ}
    (hm₁ : 0 < m₁) (he₁ : 0<3*l₁+2*m₁) (hm₂ : 0 < m₂) (he₂ : 0<3*l₂+2*m₂)
    (hs : symbol (l₁ : ℂ) (m₁ : ℂ)=symbol (l₂ : ℂ) (m₂ : ℂ)) : l₁=l₂ ∧ m₁=m₂ := by
  have hp₁ : l₁+3*m₁≠0 := ne_of_gt (by linarith)
  have hp₂ : l₂+3*m₂≠0 := ne_of_gt (by linarith)
  have hp₁' : (l₁ : ℂ)+3*(m₁ : ℂ)≠0 := by exact_mod_cast hp₁
  have hp₂' : (l₂ : ℂ)+3*(m₂ : ℂ)≠0 := by exact_mod_cast hp₂
  have hh := symbol_injective (Complex.ofReal_ne_zero.mpr hm₁.ne') hp₁' hp₂' hs
  exact ⟨Complex.ofReal_injective hh.1,Complex.ofReal_injective hh.2⟩

end ElasticityBoundarySymbol

end
end
section
/-!
Polynomial-amplitude inversion for the frozen physical half-space operator.
This is the arbitrary-order normal ODE used in a boundary-layer construction:
every exp(-t)-polynomial forcing has an exp(-t)-polynomial solution with
zero boundary value. No pseudodifferential solvability is assumed.
-/
noncomputable section
open Polynomial
namespace ElasticityBoundarySymbol
abbrev P := Polynomial ℂ

/-- Differentiation of the polynomial amplitude after factoring out exp(-t). -/
def shiftedDerivative (c : ℂ) : P →ₗ[ℂ] P :=
  Polynomial.derivative - c • LinearMap.id

@[simp] lemma shiftedDerivative_apply (c : ℂ) (p : P) :
    shiftedDerivative c p = derivative p - c • p := rfl

lemma polynomial_derivative_surjective : Function.Surjective (Polynomial.derivative : P →ₗ[ℂ] P) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨u, hu⟩ := hp
      obtain ⟨v, hv⟩ := hq
      exact ⟨u+v, by rw [map_add, hu, hv]⟩
  | monomial n a =>
      refine ⟨monomial (n+1) (a / (n+1)), ?_⟩
      rw [derivative_monomial_succ, div_mul_cancel₀]
      exact Nat.cast_add_one_ne_zero n

/-- Although differentiation is nilpotent only degree by degree, each nonzero
scalar shift is onto the whole space of finite polynomials. -/
lemma shiftedDerivative_surjective (c : ℂ) (hc : c≠0) :
    Function.Surjective (shiftedDerivative c) := by
  have hm : ∀ n : ℕ, ∀ a : ℂ, ∃ q : P, shiftedDerivative c q=monomial n a := by
    intro n
    induction n with
    | zero =>
        intro a
        refine ⟨C (-a/c), ?_⟩
        simp only [shiftedDerivative_apply, derivative_C, zero_sub, smul_C]
        rw [← map_neg, monomial_zero_left]
        congr 1
        simp only [smul_eq_mul, neg_div, mul_neg, neg_neg]
        exact mul_div_cancel₀ a hc
    | succ n ih =>
        intro a
        obtain ⟨q, hq⟩ := ih (a * (n+1))
        let p : P := monomial (n+1) a
        have hd : derivative p=monomial n (a*(n+1)) := derivative_monomial_succ a n
        refine ⟨c⁻¹ • (q-p), ?_⟩
        rw [map_smul, map_sub, hq, ← hd, shiftedDerivative_apply]
        rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨u, hu⟩ := hp
      obtain ⟨v, hv⟩ := hq
      exact ⟨u+v, by rw [map_add, hu, hv]⟩
  | monomial n a => exact hm n a

/-- The amplitude operator for d²/dt²-1 on exp(-t) times a polynomial. -/
def laplaceAmplitude : P →ₗ[ℂ] P :=
  Polynomial.derivative.comp (shiftedDerivative 2)

lemma laplaceAmplitude_apply (p : P) :
    laplaceAmplitude p=derivative (derivative p)-(2 : ℂ) • derivative p := by
  simp [laplaceAmplitude, shiftedDerivative]

lemma laplaceAmplitude_surjective : Function.Surjective laplaceAmplitude :=
  polynomial_derivative_surjective.comp (shiftedDerivative_surjective 2 two_ne_zero)

lemma laplaceAmplitude_commutes (p : P) :
    laplaceAmplitude (shiftedDerivative 1 p)=shiftedDerivative 1 (laplaceAmplitude p) := by
  simp only [laplaceAmplitude_apply, shiftedDerivative_apply, map_sub, map_smul,
    one_smul]
  module

lemma shiftedDerivative_sq (p : P) :
    shiftedDerivative 1 (shiftedDerivative 1 p)=laplaceAmplitude p+p := by
  simp only [laplaceAmplitude_apply, shiftedDerivative_apply, map_sub, one_smul]
  module

/-- The actual Fourier-transformed isotropic physical elasticity operator on
polynomial amplitudes, tangential covector (1,0), inward normal t. -/
def polynomialPhysical (l m : ℂ) (p : Fin 3 → P) : Fin 3 → P :=
  ![m • laplaceAmplitude (p 0) - (l+m) • p 0 +
      (Complex.I*(l+m)) • shiftedDerivative 1 (p 2),
    m • laplaceAmplitude (p 1),
    (Complex.I*(l+m)) • shiftedDerivative 1 (p 0) +
      (l+2*m) • laplaceAmplitude (p 2) + (l+m) • p 2]

/-- A polynomial differential adjugate; the middle polarization uses the same
scalar determinant, so all three components admit one uniform construction. -/
def polynomialAdjugate (l m : ℂ) (p : Fin 3 → P) : Fin 3 → P :=
  ![(l+2*m) • laplaceAmplitude (p 0) + (l+m) • p 0 -
      (Complex.I*(l+m)) • shiftedDerivative 1 (p 2),
    (l+2*m) • laplaceAmplitude (p 1),
    -(Complex.I*(l+m)) • shiftedDerivative 1 (p 0) +
      m • laplaceAmplitude (p 2) - (l+m) • p 2]

lemma polynomial_adjugate_identity (l m : ℂ) (p : Fin 3 → P) :
    polynomialPhysical l m (polynomialAdjugate l m p) =
      fun i => (m*(l+2*m)) • laplaceAmplitude (laplaceAmplitude (p i)) := by
  funext i
  fin_cases i <;> simp [polynomialPhysical, polynomialAdjugate,
    laplaceAmplitude_apply, smul_add, smul_sub, smul_smul]
  all_goals match_scalars
  all_goals ring_nf
  all_goals try simp only [Complex.I_sq]
  all_goals ring

/-- No exceptional polynomial degree occurs in the normal recurrence. -/
theorem polynomialPhysical_surjective (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) :
    Function.Surjective (polynomialPhysical l m) := by
  intro p
  have hq : ∀ i : Fin 3, ∃ q : P,
      laplaceAmplitude (laplaceAmplitude q)=(m*(l+2*m))⁻¹ • p i := by
    intro i
    exact (laplaceAmplitude_surjective.comp laplaceAmplitude_surjective) _
  choose q hq using hq
  refine ⟨polynomialAdjugate l m q, ?_⟩
  rw [polynomial_adjugate_identity]
  funext i
  rw [hq, smul_smul, mul_inv_cancel₀ (mul_ne_zero hm he), one_smul]

end ElasticityBoundarySymbol

end
end
section
/-! Zero-Dirichlet inversion, with a literal exponential-polynomial ODE
interpretation. This is the normal component of the boundary quasimode
recursion, not a replacement for variable-coefficient boundary localization. -/
noncomputable section
open Polynomial
namespace ElasticityBoundarySymbol

def homogeneousPolynomial (l m : ℂ) (f : F) (i : Fin 3) : P :=
  C (f i) + X * C (slope l m f i)

@[simp] lemma homogeneousPolynomial_boundary (l m : ℂ) (f : F) (i : Fin 3) :
    (homogeneousPolynomial l m f i).eval 0 = f i := by
  simp [homogeneousPolynomial]

lemma homogeneousPolynomial_physical (l m : ℂ) (hp : l+3*m≠0) (f : F) :
    polynomialPhysical l m (homogeneousPolynomial l m f) = 0 := by
  have hp' : m*3+l≠0 := by convert hp using 1; ring
  have hp'' : l+m*3≠0 := by simpa only [mul_comm] using hp
  funext i
  apply Polynomial.funext
  intro z
  fin_cases i <;>
    simp [polynomialPhysical, homogeneousPolynomial, laplaceAmplitude_apply,
      shiftedDerivative_apply, slope, smul_eq_C_mul]
  all_goals field_simp [hp, hp']
  all_goals ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals field_simp [hp'']
  all_goals ring

lemma polynomialPhysical_sub (l m : ℂ) (p q : Fin 3 → P) :
    polynomialPhysical l m (p-q) = polynomialPhysical l m p - polynomialPhysical l m q := by
  funext i
  fin_cases i <;> simp [polynomialPhysical, smul_sub] <;> abel

/-- Every polynomial forcing has a decaying-polynomial solution with exactly
zero Dirichlet data. No exceptional normal order is excluded. -/
theorem polynomialPhysical_zero_boundary_surjective (l m : ℂ)
    (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0) (p : Fin 3 → P) :
    ∃ q : Fin 3 → P, polynomialPhysical l m q = p ∧ ∀ i, (q i).eval 0 = 0 := by
  obtain ⟨q, hq⟩ := polynomialPhysical_surjective l m hm he p
  let f : F := fun i => (q i).eval 0
  refine ⟨q-homogeneousPolynomial l m f, ?_, ?_⟩
  · rw [polynomialPhysical_sub, hq, homogeneousPolynomial_physical l m hp, sub_zero]
  · intro i
    simp [f]

def decayingPolynomial (p : P) (t : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ)) * p.eval (t : ℂ)

lemma decayingPolynomial_derivative (p : P) (t : ℝ) :
    HasDerivAt (decayingPolynomial p) (decayingPolynomial (shiftedDerivative 1 p) t) t := by
  have he : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ)))
      (-Complex.exp (-(t : ℂ))) t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).neg).cexp
  have hp : HasDerivAt (fun s : ℝ => p.eval (s : ℂ)) (p.derivative.eval (t : ℂ)) t := by
    exact (p.hasDerivAt (t : ℂ)).comp_ofReal
  convert he.mul hp using 1 <;>
    first | rfl | (simp [decayingPolynomial, shiftedDerivative_apply]; ring)

lemma decayingPolynomial_laplace (p : P) (t : ℝ) :
    decayingPolynomial (shiftedDerivative 1 (shiftedDerivative 1 p)) t -
      decayingPolynomial p t = decayingPolynomial (laplaceAmplitude p) t := by
  rw [shiftedDerivative_sq]
  simp [decayingPolynomial, mul_add]

/-- Physical Fourier ODE, retaining the normal derivatives instead of assigning
a boundary symbol by definition. -/
def decayingPhysical (l m : ℂ) (q : Fin 3 → P) (t : ℝ) : F :=
  ![m * (decayingPolynomial (shiftedDerivative 1 (shiftedDerivative 1 (q 0))) t -
        decayingPolynomial (q 0) t) - (l+m) * decayingPolynomial (q 0) t +
      Complex.I*(l+m)*decayingPolynomial (shiftedDerivative 1 (q 2)) t,
    m * (decayingPolynomial (shiftedDerivative 1 (shiftedDerivative 1 (q 1))) t -
        decayingPolynomial (q 1) t),
    Complex.I*(l+m)*decayingPolynomial (shiftedDerivative 1 (q 0)) t +
      (l+2*m) * (decayingPolynomial (shiftedDerivative 1 (shiftedDerivative 1 (q 2))) t -
        decayingPolynomial (q 2) t) + (l+m)*decayingPolynomial (q 2) t]

lemma decayingPhysical_eq (l m : ℂ) (q : Fin 3 → P) (t : ℝ) :
    decayingPhysical l m q t = fun i => decayingPolynomial (polynomialPhysical l m q i) t := by
  funext i
  fin_cases i <;>
    simp [decayingPhysical, polynomialPhysical, laplaceAmplitude_apply,
      decayingPolynomial, smul_eq_C_mul] <;> ring

/-- Literal ODE solution for each exp(-t)-polynomial forcing, with zero boundary.
Its first and second derivatives are certified above. -/
theorem decayingPhysical_zero_boundary_surjective (l m : ℂ)
    (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0) (p : Fin 3 → P) :
    ∃ q : Fin 3 → P,
      (∀ t, decayingPhysical l m q t = fun i => decayingPolynomial (p i) t) ∧
      ∀ i, decayingPolynomial (q i) 0 = 0 := by
  obtain ⟨q, hq, hb⟩ := polynomialPhysical_zero_boundary_surjective l m hm he hp p
  exact ⟨q, fun t => by rw [decayingPhysical_eq, hq],
    fun i => by simp [decayingPolynomial, hb]⟩

end ElasticityBoundarySymbol

end
end
section
/-! Tangential polynomial amplitudes and the zero-boundary normal right inverse.
These are finite polynomials, rather than a formal assumption that a localized
physical parametrix exists. -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace ElasticityBoundaryRecursion
open ElasticityBoundarySymbol
abbrev V := Fin 3 → P
abbrev TangentialIndex := Fin 2 →₀ ℕ
abbrev Amplitude := TangentialIndex →₀ V

def normalOperator (l m : ℂ) : V →ₗ[ℂ] V :=
  LinearMap.pi
    ![m • laplaceAmplitude.comp (LinearMap.proj 0) - (l+m) • LinearMap.proj 0 +
        (Complex.I*(l+m)) • (shiftedDerivative 1).comp (LinearMap.proj 2),
      m • laplaceAmplitude.comp (LinearMap.proj 1),
      (Complex.I*(l+m)) • (shiftedDerivative 1).comp (LinearMap.proj 0) +
        (l+2*m) • laplaceAmplitude.comp (LinearMap.proj 2) + (l+m) • LinearMap.proj 2]

@[simp] lemma normalOperator_apply (l m : ℂ) (p : V) :
    normalOperator l m p = polynomialPhysical l m p := by
  funext i
  fin_cases i <;> rfl

def boundary : V →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun p i := (p i).eval 0
  map_add' p q := by ext i; simp
  map_smul' c p := by ext i; simp

@[simp] lemma boundary_apply (p : V) (i : Fin 3) : boundary p i = (p i).eval 0 := rfl

def zeroBoundary : Submodule ℂ V := LinearMap.ker boundary

def zeroNormalOperator (l m : ℂ) : zeroBoundary →ₗ[ℂ] V :=
  (normalOperator l m).comp zeroBoundary.subtype

lemma zeroNormalOperator_surjective (l m : ℂ) (hm : m≠0)
    (he : l+2*m≠0) (hp : l+3*m≠0) : Function.Surjective (zeroNormalOperator l m) := by
  intro p
  obtain ⟨q, hq, hb⟩ := polynomialPhysical_zero_boundary_surjective l m hm he hp p
  refine ⟨⟨q, by change boundary q=0; ext i; exact hb i⟩, ?_⟩
  simpa only [zeroNormalOperator, LinearMap.comp_apply, Submodule.subtype_apply,
    normalOperator_apply] using hq

/-- A genuine linear right inverse on the zero boundary subspace. -/
theorem exists_normalInverse (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0) :
    ∃ S : V →ₗ[ℂ] V, (normalOperator l m).comp S = LinearMap.id ∧
      boundary.comp S = 0 := by
  obtain ⟨S, hS⟩ := (zeroNormalOperator l m).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (zeroNormalOperator_surjective l m hm he hp))
  refine ⟨zeroBoundary.subtype.comp S, ?_, ?_⟩
  · exact hS
  · apply LinearMap.ext
    intro p
    funext i
    exact congrFun (S p).property i

/-- Applying the physical normal operator to each tangential monomial. -/
def normalAmplitude (l m : ℂ) : Amplitude →ₗ[ℂ] Amplitude :=
  Finsupp.mapRange.linearMap (normalOperator l m)

def boundaryAmplitude : Amplitude →ₗ[ℂ] (TangentialIndex →₀ (Fin 3 → ℂ)) :=
  Finsupp.mapRange.linearMap boundary

@[simp] lemma normalAmplitude_apply (l m : ℂ) (p : Amplitude) (a : TangentialIndex) :
    normalAmplitude l m p a = polynomialPhysical l m (p a) := normalOperator_apply l m (p a)

@[simp] lemma boundaryAmplitude_apply (p : Amplitude) (a : TangentialIndex) (i : Fin 3) :
    boundaryAmplitude p a i = (p a i).eval 0 := rfl

theorem exists_amplitudeInverse (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0) :
    ∃ S : Amplitude →ₗ[ℂ] Amplitude, (normalAmplitude l m).comp S=LinearMap.id ∧
      boundaryAmplitude.comp S=0 := by
  obtain ⟨S, hS, hB⟩ := exists_normalInverse l m hm he hp
  refine ⟨Finsupp.mapRange.linearMap S, ?_, ?_⟩
  · apply LinearMap.ext
    intro p
    apply Finsupp.ext
    intro a
    funext i
    exact congrFun (LinearMap.congr_fun hS (p a)) i
  · apply LinearMap.ext
    intro p
    apply Finsupp.ext
    intro a
    funext i
    exact congrFun (LinearMap.congr_fun hB (p a)) i

/-- Successive coefficients of a triangular polynomial-amplitude equation.
The zeroth coefficient is prescribed; all positive coefficients have zero
physical boundary values. -/
theorem triangular_amplitudes (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (A : ℕ → (Amplitude →ₗ[ℂ] Amplitude)) (hA : A 0=normalAmplitude l m)
    (p₀ : Amplitude) (h₀ : normalAmplitude l m p₀=0) :
    ∃ p : ℕ → Amplitude, p 0=p₀ ∧
      (∀ n, 0<n → boundaryAmplitude (p n)=0) ∧
      ∀ n, ∑ k ∈ Finset.range (n+1), A k (p (n-k))=0 := by
  obtain ⟨S, hS, hB⟩ := exists_amplitudeInverse l m hm he hp
  let p : ℕ → Amplitude := Nat.strongRec fun n prev =>
    if hn : n=0 then p₀ else -S (∑ k : Fin n,
      A (k.val+1) (prev (n-(k.val+1)) (by omega)))
  have hrec (n : ℕ) : p n = if hn : n=0 then p₀ else -S (∑ k : Fin n,
      A (k.val+1) (p (n-(k.val+1)))) := by
    conv_lhs => unfold p; rw [Nat.strongRec_eq]
  have hzero : p 0=p₀ := by rw [hrec]; simp
  refine ⟨p, hzero, ?_, ?_⟩
  · intro n hn
    rw [hrec, dite_eq_right (by omega), map_neg]
    have hb := LinearMap.congr_fun hB (∑ k : Fin n, A (k.val+1) (p (n-(k.val+1))))
    simpa using congrArg Neg.neg hb
  · intro n
    have hsum : (∑ k ∈ Finset.range (n+1), A k (p (n-k))) =
        A 0 (p n) + ∑ k : Fin n, A (k.val+1) (p (n-(k.val+1))) := by
      rw [Finset.sum_range_succ']
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [Nat.sub_zero]
      exact add_comm _ _
    rw [hsum, hA]
    by_cases hn : n=0
    · subst n
      simpa [hzero] using h₀
    · rw [hrec, dite_eq_right hn, map_neg]
      have hs := LinearMap.congr_fun hS (∑ k : Fin n, A (k.val+1) (p (n-(k.val+1))))
      change normalAmplitude l m (S _) = _ at hs
      rw [hs, LinearMap.id_apply, neg_add_cancel]

end ElasticityBoundaryRecursion

end
end
section
/-! The normal inverse on literal multivariable polynomial amplitudes.  No
identification of formal symbols with physical derivatives is assumed: the
normal operator here consists of the actual formal partial derivatives, whose
evaluations agree with the corresponding Fréchet derivatives. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryMVNormal
open MvPolynomial ElasticityBoundarySymbol ElasticityBoundaryMVCalculus
abbrev W := Fin 3 → MP

def d : MP →ₗ[ℂ] MP := (pderiv 2).toLinearMap
def shift : MP →ₗ[ℂ] MP := d - LinearMap.id
def lap : MP →ₗ[ℂ] MP := d.comp (d - (2:ℂ) • LinearMap.id)

@[simp] lemma d_apply (p : MP) : d p=pderiv 2 p := rfl
@[simp] lemma shift_apply (p : MP) : shift p=pderiv 2 p-p := rfl
lemma lap_apply (p : MP) : lap p=pderiv 2 (pderiv 2 p)-(2:ℂ) • pderiv 2 p := by
  simp [lap, d]

def normal (l m : ℂ) : W →ₗ[ℂ] W :=
  LinearMap.pi
    ![m • lap.comp (LinearMap.proj 0) - (l+m) • LinearMap.proj 0 +
        (Complex.I*(l+m)) • shift.comp (LinearMap.proj 2),
      m • lap.comp (LinearMap.proj 1),
      (Complex.I*(l+m)) • shift.comp (LinearMap.proj 0) +
        (l+2*m) • lap.comp (LinearMap.proj 2) + (l+m) • LinearMap.proj 2]

lemma normal_apply (l m : ℂ) (p : W) : normal l m p =
    ![m • lap (p 0) - (l+m) • p 0 + (Complex.I*(l+m)) • shift (p 2),
      m • lap (p 1), (Complex.I*(l+m)) • shift (p 0) +
        (l+2*m) • lap (p 2) + (l+m) • p 2] := by funext i; fin_cases i <;> rfl

def lift : P →ₐ[ℂ] MP := Polynomial.aeval (X 2)

@[simp] lemma lift_C (c : ℂ) : lift (Polynomial.C c)=C c := by simp [lift]
@[simp] lemma lift_X : lift Polynomial.X=X 2 := by simp [lift]

lemma d_lift (p : P) : d (lift p)=lift (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
      simp only [d_apply, lift, Polynomial.aeval_monomial, algebraMap_eq,
        Polynomial.derivative_monomial, pderiv_C_mul, pderiv_pow, pderiv_X_self, mul_one,
        map_mul, map_natCast]
      ring

lemma pderiv_lift (p : P) : pderiv 2 (lift p)=lift (Polynomial.derivative p) := d_lift p

lemma shift_lift (p : P) : shift (lift p)=lift (shiftedDerivative 1 p) := by
  change d (lift p)-lift p=_
  rw [d_lift, shiftedDerivative_apply, one_smul, map_sub]

lemma lap_lift (p : P) : lap (lift p)=lift (laplaceAmplitude p) := by
  change d (d (lift p)-(2:ℂ) • lift p)=_
  rw [map_sub, map_smul, d_lift, d_lift, laplaceAmplitude_apply, map_sub, map_smul]

lemma normal_lift (l m : ℂ) (p : Fin 3 → P) :
    normal l m (fun i => lift (p i)) = fun i => lift (polynomialPhysical l m p i) := by
  funext i
  fin_cases i <;>
    simp [normal_apply, polynomialPhysical, lap_lift, pderiv_lift]

lemma shift_mul {b : MP} (hb : pderiv 2 b=0) (p : MP) :
    shift (b*p)=b*shift p := by simp only [shift_apply, pderiv_mul, hb, zero_mul, zero_add]; ring
lemma lap_mul {b : MP} (hb : pderiv 2 b=0) (p : MP) : lap (b*p)=b*lap p := by
  simp only [lap_apply, pderiv_mul, hb, zero_mul, zero_add, smul_eq_C_mul]
  ring
lemma normal_mul (l m : ℂ) {b : MP} (hb : pderiv 2 b=0) (p : W) :
    normal l m (fun i => b*p i) = fun i => b*normal l m p i := by
  funext i
  fin_cases i <;> simp [normal_apply, shift_mul hb, lap_mul hb, smul_eq_C_mul] <;> ring

/-- The actual restriction of a polynomial to the flat boundary. -/
def boundaryRing : MP →ₐ[ℂ] MP := MvPolynomial.aeval (fun i => if i=2 then 0 else X i)
def boundary : W →ₗ[ℂ] W := LinearMap.pi (fun i => boundaryRing.toLinearMap.comp (LinearMap.proj i))
@[simp] lemma boundary_apply (p : W) (i : Fin 3) : boundary p i=boundaryRing (p i) := rfl

lemma boundary_lift (p : P) : boundaryRing (lift p)=C (p.eval 0) := by
  induction p using Polynomial.induction_on with
  | C c => simp [lift, boundaryRing]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.eval_add]
  | monomial n c _ => simp [lift, boundaryRing]

lemma monomial_split (a : Fin 3 →₀ ℕ) (c : ℂ) :
    monomial (a.erase 2) 1 * lift (Polynomial.monomial (a 2) c) = monomial a c := by
  simp only [lift, Polynomial.aeval_monomial, algebraMap_eq, C_mul_X_pow_eq_monomial,
    monomial_mul_monomial, one_mul, Finsupp.erase_add_single]

lemma normal_zeroBoundary_surjective (l m : ℂ) (hm : m≠0)
    (he : l+2*m≠0) (hp : l+3*m≠0) :
    Function.Surjective ((normal l m).comp (LinearMap.ker boundary).subtype) := by
  let R := LinearMap.range ((normal l m).comp (LinearMap.ker boundary).subtype)
  have hmono (i : Fin 3) (a : Fin 3 →₀ ℕ) (c : ℂ) : Pi.single i (monomial a c) ∈ R := by
    let p : Fin 3 → P := Pi.single i (Polynomial.monomial (a 2) c)
    obtain ⟨q,hq,hb⟩ := polynomialPhysical_zero_boundary_surjective l m hm he hp p
    let b : MP := monomial (a.erase 2) 1
    have hbd : pderiv 2 b=0 := by simp [b]
    let v : W := fun j => b*lift (q j)
    have hv : v ∈ LinearMap.ker boundary := by
      change boundary v=0
      funext j
      simp [v, boundary_lift, hb]
    refine ⟨⟨v,hv⟩, ?_⟩
    change normal l m v = Pi.single i (monomial a c)
    rw [show v=(fun j => b*lift (q j)) from rfl, normal_mul l m hbd, normal_lift, hq]
    funext j
    by_cases hj : j=i
    · subst j
      simpa [p,b] using monomial_split a c
    · simp [p,hj]
  have hsingle (i : Fin 3) (p : MP) : Pi.single i p ∈ R := by
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq => simpa only [Pi.single_add] using R.add_mem hp hq
    | monomial a c => exact hmono i a c
  intro p
  have hsum : (∑ i, Pi.single i (p i)) ∈ R := R.sum_mem (fun i _ => hsingle i (p i))
  have heq : (∑ i, Pi.single i (p i)) = p := by
    funext j; simp [Pi.single_apply]
  rw [heq] at hsum
  exact hsum

/-- A literal multivariable-polynomial right inverse with zero boundary values. -/
theorem exists_inverse (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0) :
    ∃ S : W →ₗ[ℂ] W, (normal l m).comp S=LinearMap.id ∧ boundary.comp S=0 := by
  obtain ⟨S,hS⟩ := ((normal l m).comp (LinearMap.ker boundary).subtype).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (normal_zeroBoundary_surjective l m hm he hp))
  refine ⟨(LinearMap.ker boundary).subtype.comp S,hS,?_⟩
  apply LinearMap.ext
  intro p
  exact (S p).property

end ElasticityBoundaryMVNormal

end
end
section
/-! Actual second derivatives and the literal frozen elasticity operator on
boundary profiles. The coefficients below act on physical tensor indices. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryLayerOperator
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile ElasticityBoundaryMVNormal
abbrev Y := Fin 3 → ℝ

lemma second_physicalProfile {δ : ℝ} (hδ : δ≠0) (p : MP) (z : Y) (α β : Fin 3) :
    fderiv ℝ (fun x => fderiv ℝ (physicalProfile δ p) x (Pi.single β 1)) z (Pi.single α 1) =
      ((δ^4)⁻¹:ℝ) • physicalProfile δ (D δ α (D δ β p)) z := by
  simp_rw [fderiv_physicalProfile_basis hδ]
  change fderiv ℝ (((δ^2)⁻¹:ℝ) • physicalProfile δ (D δ β p)) z _ = _
  rw [fderiv_const_smul ((smooth_physicalProfile δ (D δ β p)).differentiable (by simp)).differentiableAt]
  rw [smul_apply, fderiv_physicalProfile_basis hδ, smul_smul]
  congr 1
  field_simp

/-- The isotropic elasticity tensor in fixed (orthonormal) coordinates. -/
def elasticityTensor (l m : ℂ) (i α j β : Fin 3) : ℂ :=
  l*(if i=α then 1 else 0)*(if j=β then 1 else 0) +
  m*((if i=j then 1 else 0)*(if α=β then 1 else 0) +
    (if i=β then 1 else 0)*(if α=j then 1 else 0))

/-- A principal tensor acts on actual polynomial conjugated derivatives. -/
def principal (a : Fin 3 → Fin 3 → Fin 3 → Fin 3 → MP) (δ : ℝ) : W →ₗ[ℂ] W :=
  LinearMap.pi (fun i => ∑ α, ∑ j, ∑ β,
    (LinearMap.mulLeft ℂ (a i α j β)).comp ((D δ α).comp ((D δ β).comp (LinearMap.proj j))))

lemma principal_apply (a : Fin 3 → Fin 3 → Fin 3 → Fin 3 → MP) (δ : ℝ) (p : W) (i : Fin 3) :
    principal a δ p i = ∑ α, ∑ j, ∑ β, a i α j β * D δ α (D δ β (p j)) := by
  simp [principal, LinearMap.sum_apply]

lemma D_zero (j : Fin 3) (p : MP) :
    D 0 j p = ![Complex.I • p, 0, pderiv 2 p-p] j := by
  fin_cases j <;> simp [D]

/-- The leading operator in the high-frequency construction is precisely the
normal operator for which a zero-boundary inverse was proved. -/
theorem principal_leading_is_normal (l m : ℂ) :
    principal (fun i α j β => C (elasticityTensor l m i α j β)) 0 = normal l m := by
  apply LinearMap.ext
  intro p
  funext i
  rw [principal_apply, normal_apply]
  have hI : (C Complex.I : MP)^2 = -1 := by rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have h2 : C (2:ℂ) = (2:MP) := map_natCast C 2
  fin_cases i <;>
    simp [Fin.sum_univ_three, elasticityTensor, D_zero, lap_apply, shift_apply, map_sub,
      smul_eq_C_mul, map_add, map_mul,
      smul_sub, h2] <;> ring_nf <;> simp only [hI] <;> ring

end ElasticityBoundaryLayerOperator

end
end
section
/-! The finite-parameter differential operator of the actual Taylor-expanded
divergence tensor. No leading normal operator is stipulated. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryTensorSeries
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryProfile ElasticityBoundaryParameter ElasticityBoundaryLayerOperator

abbrev Tensor := Fin 3 → Fin 3 → Fin 3 → Fin 3 → Polynomial MP
abbrev Lower := Fin 3 → Fin 3 → Fin 3 → Polynomial MP

def pack : (Fin 3 → Polynomial MP) →ₗ[ℂ] Polynomial W :=
  ∑ i, (coeffMap (LinearMap.single ℂ (fun _ : Fin 3 => MP) i)).comp (LinearMap.proj i)

def unpack (i : Fin 3) : Polynomial W →ₗ[ℂ] Polynomial MP := coeffMap (LinearMap.proj i)

lemma pack_coeff (q : Fin 3 → Polynomial MP) (n : ℕ) (i : Fin 3) :
    (pack q).coeff n i = (q i).coeff n := by
  simp [pack, LinearMap.sum_apply, Polynomial.finsetSum_coeff, coeffMap_coeff,
    Pi.single_apply]

lemma unpack_pack (q : Fin 3 → Polynomial MP) (i : Fin 3) : unpack i (pack q)=q i := by
  apply Polynomial.ext
  intro n
  exact pack_coeff q n i

lemma pack_unpack (q : Polynomial W) : pack (fun i => unpack i q)=q := by
  ext n i
  simp [pack_coeff,unpack]

lemma eval_unpack (q : Polynomial W) (δ : ℝ) (i : Fin 3) :
    (unpack i q).eval (C (δ:ℂ))=(q.eval (algebraMap ℂ W (δ:ℂ))) i := by
  have h := eval_coeffMap (A := W) (B := MP) (LinearMap.proj i) q (δ:ℂ)
  change _ = (q.eval (algebraMap ℂ W (δ:ℂ))) i at h
  exact h

lemma eval_pack (q : Fin 3 → Polynomial MP) (δ : ℝ) (i : Fin 3) :
    (pack q).eval (algebraMap ℂ W (δ:ℂ)) i=(q i).eval (C (δ:ℂ)) := by
  rw [← eval_unpack, unpack_pack]

lemma pack_monomial_mul (n : ℕ) (q : Fin 3 → Polynomial MP) :
    pack (fun i => Polynomial.monomial n 1*q i)=Polynomial.monomial n 1*pack q := by
  simp only [pack, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    coeffMap_monomial_one_mul, Finset.mul_sum]

def operator (a : Tensor) (b : Lower) : Polynomial W →ₗ[ℂ] Polynomial W :=
  pack.comp (LinearMap.pi fun i =>
    (∑ α, ∑ j, ∑ β, (LinearMap.mulLeft ℂ (a i α j β)).comp
      ((PD α).comp ((PD β).comp (unpack j)))) +
    ((LinearMap.mulLeft ℂ (Polynomial.X^2)).comp
      (∑ j, ∑ β, (LinearMap.mulLeft ℂ (b i j β)).comp ((PD β).comp (unpack j)))))

lemma unpack_operator (a : Tensor) (b : Lower) (q : Polynomial W) (i : Fin 3) :
    unpack i (operator a b q) =
      (∑ α, ∑ j, ∑ β, a i α j β * PD α (PD β (unpack j q))) +
      Polynomial.X^2 * (∑ j, ∑ β, b i j β * PD β (unpack j q)) := by
  simp only [operator, LinearMap.comp_apply, unpack_pack, LinearMap.pi_apply,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.mulLeft_apply]

/-- Evaluation reproduces the actual scaled principal part and the delta^2
lower-order coefficient-gradient part of a divergence-form operator. -/
theorem eval_operator (a : Tensor) (b : Lower) (q : Polynomial W) (δ : ℝ) (i : Fin 3) :
    (operator a b q).eval (algebraMap ℂ W (δ:ℂ)) i =
      principal (fun i α j β => (a i α j β).eval (C (δ:ℂ))) δ
        (q.eval (algebraMap ℂ W (δ:ℂ))) i +
      (δ:ℂ)^2 • (∑ j, ∑ β, (b i j β).eval (C (δ:ℂ)) *
        D δ β ((q.eval (algebraMap ℂ W (δ:ℂ))) j)) := by
  rw [← eval_unpack, unpack_operator]
  simp only [Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, eval_PD, eval_unpack, principal_apply,
    smul_eq_C_mul, map_pow]

lemma unpack_monomial_mul (i : Fin 3) (n : ℕ) (q : Polynomial W) :
    unpack i (Polynomial.monomial n 1*q)=Polynomial.monomial n 1*unpack i q := by
  unfold unpack
  exact coeffMap_monomial_one_mul (A := W) (B := MP) (LinearMap.proj i) n q

lemma unpack_operator_monomial_mul (a : Tensor) (b : Lower) (n : ℕ)
    (q : Polynomial W) (i : Fin 3) :
    unpack i (operator a b (Polynomial.monomial n 1*q)) =
      Polynomial.monomial n 1*unpack i (operator a b q) := by
  rw [unpack_operator, unpack_operator]
  simp only [unpack_monomial_mul, PD_monomial_one_mul]
  have hm (c p : Polynomial MP) : c*(Polynomial.monomial n 1*p)=
      Polynomial.monomial n 1*(c*p) := mul_left_comm _ _ _
  simp_rw [hm, ← Finset.mul_sum]
  rw [hm, ← mul_add]

lemma operator_monomial_mul (a : Tensor) (b : Lower) (n : ℕ) (q : Polynomial W) :
    operator a b (Polynomial.monomial n 1*q)=Polynomial.monomial n 1*operator a b q := by
  rw [← pack_unpack (operator a b (Polynomial.monomial n 1*q))]
  simp_rw [unpack_operator_monomial_mul]
  rw [pack_monomial_mul, pack_unpack]

def coefficient (a : Tensor) (b : Lower) (k : ℕ) : W →ₗ[ℂ] W :=
  ((Polynomial.lcoeff W k).restrictScalars ℂ).comp
    ((operator a b).comp (Polynomial.CAlgHom (R := ℂ) (A := W)).toLinearMap)

lemma coefficient_apply (a : Tensor) (b : Lower) (k : ℕ) (p : W) :
    coefficient a b k p = (operator a b (Polynomial.C p)).coeff k := rfl

/-- Its leading coefficient is exactly the proved normal operator whenever
its actual tensor at the base point is the isotropic physical tensor. -/
theorem coefficient_zero (a : Tensor) (b : Lower) (l m : ℂ)
    (ha : ∀ i α j β, (a i α j β).coeff 0=C (elasticityTensor l m i α j β)) :
    coefficient a b 0=normal l m := by
  apply LinearMap.ext
  intro p
  funext i
  rw [coefficient_apply, Polynomial.coeff_zero_eq_eval_zero]
  have h := eval_operator a b (Polynomial.C p) 0 i
  simp only [Complex.ofReal_zero, map_zero, Polynomial.eval_C,
    zero_pow (by norm_num : (2:ℕ)≠0), zero_smul, add_zero] at h
  simp_rw [← Polynomial.coeff_zero_eq_eval_zero, ha] at h
  rw [principal_leading_is_normal] at h
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using h

end ElasticityBoundaryTensorSeries

end
end
section
/-! Finite-order polynomial amplitudes with an exact high-order residual
factor, for use in actual smooth boundary profiles. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryMVTower
open ElasticityBoundaryMVNormal

/-- Successive coefficients of a triangular polynomial-amplitude equation.
The zeroth coefficient is prescribed; all positive coefficients have zero
physical boundary values. -/
theorem triangular_amplitudes (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (A : ℕ → (W →ₗ[ℂ] W)) (hA : A 0=normal l m)
    (p₀ : W) (h₀ : normal l m p₀=0) :
    ∃ p : ℕ → W, p 0=p₀ ∧
      (∀ n, 0<n → boundary (p n)=0) ∧
      ∀ n, ∑ k ∈ Finset.range (n+1), A k (p (n-k))=0 := by
  obtain ⟨S, hS, hB⟩ := exists_inverse l m hm he hp
  let p : ℕ → W := Nat.strongRec fun n prev =>
    if hn : n=0 then p₀ else -S (∑ k : Fin n,
      A (k.val+1) (prev (n-(k.val+1)) (by omega)))
  have hrec (n : ℕ) : p n = if hn : n=0 then p₀ else -S (∑ k : Fin n,
      A (k.val+1) (p (n-(k.val+1)))) := by
    conv_lhs => unfold p; rw [Nat.strongRec_eq]
  have hzero : p 0=p₀ := by rw [hrec]; simp
  refine ⟨p, hzero, ?_, ?_⟩
  · intro n hn
    rw [hrec, dite_eq_right (by omega), map_neg]
    have hb := LinearMap.congr_fun hB (∑ k : Fin n, A (k.val+1) (p (n-(k.val+1))))
    simpa using congrArg Neg.neg hb
  · intro n
    have hsum : (∑ k ∈ Finset.range (n+1), A k (p (n-k))) =
        A 0 (p n) + ∑ k : Fin n, A (k.val+1) (p (n-(k.val+1))) := by
      rw [Finset.sum_range_succ']
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [Nat.sub_zero]
      exact add_comm _ _
    rw [hsum, hA]
    by_cases hn : n=0
    · subst n
      simpa [hzero] using h₀
    · rw [hrec, dite_eq_right hn, map_neg]
      have hs := LinearMap.congr_fun hS (∑ k : Fin n, A (k.val+1) (p (n-(k.val+1))))
      change normal l m (S _) = _ at hs
      rw [hs, LinearMap.id_apply, neg_add_cancel]

/-- The literal residual polynomial of two finite operator/amplitude series. -/
def residualPolynomial (A : ℕ → W →ₗ[ℂ] W) (p : ℕ → W) (K N : ℕ) : Polynomial W :=
  ∑ k ∈ Finset.range (K+1), ∑ n ∈ Finset.range (N+1),
    Polynomial.monomial (k+n) (A k (p n))

lemma residual_coefficient (A : ℕ → W →ₗ[ℂ] W) (p : ℕ → W) {K N d : ℕ}
    (hK : d≤K) (hN : d≤N) :
    (residualPolynomial A p K N).coeff d =
      ∑ k ∈ Finset.range (d+1), A k (p (d-k)) := by
  classical
  simp only [residualPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  have hi (k : ℕ) : (∑ n ∈ Finset.range (N+1), if k+n=d then A k (p n) else 0) =
      if k≤d then A k (p (d-k)) else 0 := by
    by_cases hk : k≤d
    · rw [ite_eq_left hk]
      rw [Finset.sum_eq_single (d-k)]
      · simp [Nat.add_sub_of_le hk]
      · intro n _ hn
        rw [ite_eq_right (by omega)]
      · intro hn
        exact False.elim (hn (Finset.mem_range.mpr (by omega)))
    · rw [ite_eq_right hk]
      apply Finset.sum_eq_zero
      intro n _
      rw [ite_eq_right (by omega)]
  simp_rw [hi]
  have hs : (∑ k ∈ Finset.range (K+1), if k≤d then A k (p (d-k)) else 0) =
      ∑ k ∈ Finset.range (d+1), if k≤d then A k (p (d-k)) else 0 := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    rw [ite_eq_right (by simp only [Finset.mem_range] at hk; omega)]
  rw [hs]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ite_eq_left (by simp only [Finset.mem_range] at hk; omega)]

/-- All orders up to N cancel as an exact polynomial identity, leaving an
actual finite polynomial times delta^(N+1), not just a formal asymptotic. -/
theorem residual_high_order_factor (A : ℕ → W →ₗ[ℂ] W) (p : ℕ → W) {K N : ℕ}
    (hKN : N≤K)
    (hc : ∀ n, ∑ k ∈ Finset.range (n+1), A k (p (n-k))=0) :
    ∃ R : Polynomial W, residualPolynomial A p K N=Polynomial.X^(N+1)*R := by
  have hd : Polynomial.X^(N+1) ∣ residualPolynomial A p K N := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro d hd
    rw [residual_coefficient A p (by omega) (by omega), hc]
  obtain ⟨R,hR⟩ := hd
  exact ⟨R,hR⟩

/-- A finite correction family for every prescribed leading physical normal
solution, with zero boundary corrections and exact arbitrary-order cancellation. -/
theorem finite_physical_amplitudes (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (A : ℕ → W →ₗ[ℂ] W) (hA : A 0=normal l m)
    (p₀ : W) (h₀ : normal l m p₀=0) (N K : ℕ) (hKN : N≤K) :
    ∃ (p : ℕ → W) (R : Polynomial W), p 0=p₀ ∧
      (∀ n, 0<n → boundary (p n)=0) ∧
      residualPolynomial A p K N=Polynomial.X^(N+1)*R := by
  obtain ⟨p,hp0,hb,hc⟩ := triangular_amplitudes l m hm he hp A hA p₀ h₀
  obtain ⟨R,hR⟩ := residual_high_order_factor A p hKN hc
  exact ⟨p,R,hp0,hb,hR⟩

end ElasticityBoundaryMVTower

end
end

end OAI
