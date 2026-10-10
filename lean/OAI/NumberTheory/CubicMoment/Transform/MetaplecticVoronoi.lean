import OAI.NumberTheory.CubicMoment.Transform.MetaplecticHeight
import OAI.NumberTheory.CubicMoment.Angular.AngularAlgebra
import OAI.NumberTheory.CubicGram.PeriodicPoisson

namespace OAI

/-! The literal level/angular Voronoi input of Dunn--Radziwill,
arXiv:2109.07463v3, Proposition 5.3, equations (5.79)--(5.82), pp.33--34.
The raw formula is kept separate from its proved Gauss/phase normalization.
The index `n` below denotes the actual frequency `n / lambda`; zero is excluded.
No estimate for a completed sum is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev MetaplecticDualArgument := {n : Eisenstein // n ≠ 0}

def metaplecticFrequency (n : MetaplecticDualArgument) : ℂ :=
  (n.val : ℂ)/traceLambda

lemma metaplecticFrequency_ne_zero (n : MetaplecticDualArgument) :
    metaplecticFrequency n ≠ 0 :=
  div_ne_zero (fun h => n.property (Subtype.ext h)) traceLambda_ne_zero

def complexAngular (ℓ : ℤ) (z : ℂ) : ℂ := (z/(‖z‖:ℂ))^ℓ

@[simp] lemma complexAngular_coe (ℓ : ℤ) (a : Eisenstein) :
    complexAngular ℓ a = theta ℓ a := rfl

def metaplecticGammaQuotient (ℓ : ℤ) (s : ℂ) : ℂ :=
  (Complex.Gamma (5/6+(|ℓ|:ℤ)/2-s)*Complex.Gamma (7/6+(|ℓ|:ℤ)/2-s))/
    (Complex.Gamma (s+(|ℓ|:ℤ)/2-1/6)*Complex.Gamma (s+(|ℓ|:ℤ)/2+1/6))

/-- Equation (5.81), parameterized on the vertical line `Re s = -sigma`. -/
def metaplecticTransform (ℓ : ℤ) (W : ℝ → ℂ) (σ v : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,
    (v:ℂ)^(((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ (((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I)*
      mellin W (((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I)

/-- Equation (5.68), written as its exact squarefree Euler product. -/
def metaplecticLocalCoefficient (r : Eisenstein) (n : MetaplecticDualArgument) : ℂ :=
  ∏ p ∈ primaryPrimeFactors r,
    ((if p ∣ n.val then norm p-1 else -1 : ℝ):ℂ)

def metaplecticCommonNorm (r : Eisenstein) (n : MetaplecticDualArgument) : ℝ :=
  ∏ p ∈ (primaryPrimeFactors r).filter (fun p => p ∣ n.val), norm p

lemma norm_metaplecticLocalCoefficient_le {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) :
    ‖metaplecticLocalCoefficient r n‖ ≤ metaplecticCommonNorm r n := by
  rw [metaplecticLocalCoefficient,norm_prod]
  have hp (p : Eisenstein) (hp : p ∈ primaryPrimeFactors r) : 1 ≤ norm p :=
    one_le_norm (primaryPrimeFactor_spec hr hp).1.2.ne_zero
  calc
    _ ≤ ∏ p ∈ primaryPrimeFactors r, if p ∣ n.val then norm p else 1 := by
      apply Finset.prod_le_prod₀ (fun _ _ => _root_.norm_nonneg _)
      intro p hpm
      split_ifs with h
      · simp only [Complex.norm_real,Real.norm_eq_abs]
        rw [abs_of_nonneg (by linarith [hp p hpm])]
        linarith
      · norm_num
    _ = metaplecticCommonNorm r n := by
      simp only [metaplecticCommonNorm,Finset.prod_ite,Finset.prod_const_one,mul_one]

/-- Support read from (5.79), avoiding the repeated ramified exponent in
the printed (5.67). The coefficient bound follows from (5.7), (5.13), (5.14).
The two supported factors may have arbitrarily large exponents. -/
def MetaplecticCoefficientBounds
    (a : Eisenstein → MetaplecticDualArgument → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r → Squarefree r →
    ∀ n : MetaplecticDualArgument, a r n*metaplecticLocalCoefficient r n ≠ 0 →
      ∃ (j : ℤ) (ζ : Eisensteinˣ) (h h' w : Eisenstein),
        -1 ≤ j ∧ primary h ∧ primary h' ∧ primary w ∧
        (∃ k : ℕ, h ∣ r^k) ∧ (∃ k : ℕ, h' ∣ r^k) ∧
        IsCoprime w r ∧ Squarefree (h*w) ∧
        metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3 ∧
        ‖a r n‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')

def metaplecticDualTerm (a : Eisenstein → MetaplecticDualArgument → ℂ)
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (σ X : ℝ)
    (nd : MetaplecticDualArgument × PrimaryArgument) : ℂ :=
  if IsCoprime (nd.2:Eisenstein) r then
    a r nd.1*metaplecticLocalCoefficient r nd.1/
      ((Complex.normSq (metaplecticFrequency nd.1)*norm nd.2^(5/2:ℝ):ℝ):ℂ)*
      complexAngular (-ℓ) ((nd.2:Eisenstein)^3*metaplecticFrequency nd.1)*
      metaplecticTransform ℓ W σ
        ((2*Real.pi)^4*Complex.normSq ((nd.2:Eisenstein)^3*
          metaplecticFrequency nd.1)*X/(norm r)^2)
  else 0

def metaplecticRawCompleted (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' du : PrimaryArgument × PrimaryArgument,
    if IsCoprime (du.1:Eisenstein) r then
      (Real.sqrt (norm du.1):ℂ)*gauss du.2*theta ℓ (du.2*du.1^3)*
        star (cubicSymbol r du.2)*W (norm (du.2*du.1^3)/X)
    else 0

def metaplecticCompleted (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' du : PrimaryArgument × PrimaryArgument,
    if IsCoprime (du.1:Eisenstein) r then
      (Real.sqrt (norm du.1):ℂ)*gauss (r*du.2)*theta ℓ (r*(du.2*du.1^3))*
        W (norm (du.2*du.1^3)/X)
    else 0

def metaplecticRawMain (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  if ℓ = 0 then
    ((metaplecticA0*X^(5/6:ℝ)*metaplecticTotient r*norm r^(-5/3:ℝ):ℝ):ℂ)*
      mellin W (5/6)*star ((Real.sqrt (norm r):ℂ)*gauss r)
  else 0

def metaplecticMain (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  if ℓ = 0 then
    ((metaplecticA0*X^(5/6:ℝ)*metaplecticTotient r*norm r^(-7/6:ℝ):ℝ):ℂ)*
      mellin W (5/6)
  else 0

def metaplecticRawPrefactor (r : Eisenstein) (ℓ : ℤ) : ℂ :=
  star ((Real.sqrt (norm r):ℂ)*gauss r)/
    ((3^(7/2:ℝ)*(2*Real.pi)^2:ℝ):ℂ)*((star (r:ℂ)/(r:ℂ))^(-ℓ))

def metaplecticPrefactor (r : Eisenstein) (ℓ : ℤ) : ℂ :=
  ((Real.sqrt (norm r)/(3^(7/2:ℝ)*(2*Real.pi)^2):ℝ):ℂ)*theta (3*ℓ) r

/-- The only new analytic identity assumed here is DR Proposition 5.3.
Its absolute convergence is part of the published proof of (5.80).
The input retains the actual transform, frequency lattice, local Euler
coefficients and global theta-coefficient support. -/
def MetaplecticVoronoiInput
    (a : Eisenstein → MetaplecticDualArgument → ℂ) : Prop :=
  MetaplecticCoefficientBounds a ∧
  ∀ r : Eisenstein, primary r → Squarefree r → ∀ ℓ : ℤ,
    ∀ W : ℝ → ℂ, HasCompactSupport W → tsupport W ⊆ Ioi 0 →
      ContDiff ℝ ∞ W → ∀ X : ℝ, 0 < X → ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
        Summable (metaplecticDualTerm a r ℓ W σ X) ∧
        metaplecticRawCompleted r ℓ W X = metaplecticRawMain r ℓ W X+
          metaplecticRawPrefactor r ℓ*∑' nd, metaplecticDualTerm a r ℓ W σ X nd

lemma metaplecticCompleted_eq_raw {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) :
    metaplecticCompleted r ℓ W X = gauss r*theta ℓ r*metaplecticRawCompleted r ℓ W X := by
  rw [metaplecticCompleted,metaplecticRawCompleted,← tsum_mul_left]
  apply tsum_congr
  intro du
  split_ifs
  · rw [gauss_mul hr du.2.property,theta_mul,cubic_reciprocity du.2.property hr]
    ring
  · ring

lemma gauss_mul_conj_unnormalized {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    gauss r*star ((Real.sqrt (norm r):ℂ)*gauss r) = (Real.sqrt (norm r):ℂ) := by
  rw [star_mul]
  simp only [Complex.star_def,Complex.conj_ofReal]
  calc
    _ = (Real.sqrt (norm r):ℂ)*(gauss r*(starRingEnd ℂ) (gauss r)) := by ring
    _ = _ := by
      rw [Complex.mul_conj',norm_gauss_of_squarefree hr hs]
      norm_num

lemma angular_conjugate_ratio {r : Eisenstein} (hr : r ≠ 0) (ℓ : ℤ) :
    theta ℓ r*((star (r:ℂ)/(r:ℂ))^(-ℓ)) = theta (3*ℓ) r := by
  have hz : (r:ℂ) ≠ 0 := fun h => hr (Subtype.ext h)
  have hn : (‖(r:ℂ)‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hratio : star (r:ℂ)/(r:ℂ) = ((r:ℂ)/(‖(r:ℂ)‖:ℂ))^(-2:ℤ) := by
    rw [zpow_neg,zpow_ofNat,← inv_pow,inv_div]
    field_simp
    simpa [pow_two,mul_comm] using (Complex.mul_conj' (r:ℂ))
  rw [hratio,← zpow_mul]
  simp only [theta]
  rw [← zpow_add₀ (div_ne_zero hz hn)]
  congr 1
  ring

lemma metaplecticMain_normalization {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) :
    gauss r*theta ℓ r*metaplecticRawMain r ℓ W X = metaplecticMain r ℓ W X := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp only [metaplecticRawMain,metaplecticMain,ite_true,theta_zero,mul_one]
    have hp : norm r^(-5/3:ℝ)*Real.sqrt (norm r) = norm r^(-7/6:ℝ) := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_add (norm_pos_of_ne_zero (primary_ne_zero hr))]
      congr 1
      norm_num
    have hc :
        ((metaplecticA0*X^(5/6:ℝ)*metaplecticTotient r*norm r^(-5/3:ℝ):ℝ):ℂ)*
          (Real.sqrt (norm r):ℂ) =
        ((metaplecticA0*X^(5/6:ℝ)*metaplecticTotient r*norm r^(-7/6:ℝ):ℝ):ℂ) := by
      rw [← Complex.ofReal_mul,mul_assoc,hp]
    calc
      _ = ((metaplecticA0*X^(5/6:ℝ)*metaplecticTotient r*norm r^(-5/3:ℝ):ℝ):ℂ)*
          (gauss r*star ((Real.sqrt (norm r):ℂ)*gauss r))*mellin W (5/6) := by ring
      _ = _ := by rw [gauss_mul_conj_unnormalized hr hs,hc]
  · simp [metaplecticRawMain,metaplecticMain,hℓ]

lemma metaplecticPrefactor_normalization {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) (ℓ : ℤ) :
    gauss r*theta ℓ r*metaplecticRawPrefactor r ℓ = metaplecticPrefactor r ℓ := by
  unfold metaplecticRawPrefactor metaplecticPrefactor
  calc
    _ = (gauss r*star ((Real.sqrt (norm r):ℂ)*gauss r))/
        ((3^(7/2:ℝ)*(2*Real.pi)^2:ℝ):ℂ)*
        (theta ℓ r*((star (r:ℂ)/(r:ℂ))^(-ℓ))) := by ring
    _ = _ := by
      rw [gauss_mul_conj_unnormalized hr hs,angular_conjugate_ratio (primary_ne_zero hr)]
      push_cast
      rfl

/-- The manuscript's normalized angular Voronoi identity, derived from
the published raw formula. The theta coefficients remain explicit. -/
theorem metaplectic_angular_voronoi
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hs : Squarefree r) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X σ : ℝ} (hX : 0 < X) (hσ : 0 < σ)
    (hσ' : σ < 1/10000) :
    metaplecticCompleted r ℓ W X = metaplecticMain r ℓ W X+
      metaplecticPrefactor r ℓ*∑' nd, metaplecticDualTerm a r ℓ W σ X nd := by
  rw [metaplecticCompleted_eq_raw hr,
    (hV.2 r hr hs ℓ W hW hpos hsm X hX σ hσ hσ').2,mul_add,
    metaplecticMain_normalization hr hs,← mul_assoc,
    metaplecticPrefactor_normalization hr hs]

lemma norm_metaplecticPrefactor {r : Eisenstein} (hr : r ≠ 0) (ℓ : ℤ) :
    ‖metaplecticPrefactor r ℓ‖ =
      Real.sqrt (norm r)/(3^(7/2:ℝ)*(2*Real.pi)^2) := by
  rw [metaplecticPrefactor,norm_mul,norm_theta hr,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg]
  positivity

/-- On the critical line the two numerator Gamma factors are the
conjugates of the denominator factors, so the angular quotient has norm one. -/
lemma norm_metaplecticGammaQuotient_critical (ℓ : ℤ) (t : ℝ) :
    ‖metaplecticGammaQuotient ℓ ((1/2:ℝ)+(t:ℂ)*Complex.I)‖ = 1 := by
  let s : ℂ := (1/2:ℝ)+(t:ℂ)*Complex.I
  let z₁ : ℂ := s+(|ℓ|:ℤ)/2-1/6
  let z₂ : ℂ := s+(|ℓ|:ℤ)/2+1/6
  have h₁ : 0 < z₁.re := by
    have h := abs_nonneg (ℓ:ℝ)
    norm_num [z₁,s]
    linarith
  have h₂ : 0 < z₂.re := by
    have h := abs_nonneg (ℓ:ℝ)
    norm_num [z₂,s]
    linarith
  have hn := mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos h₁)
    (Complex.Gamma_ne_zero_of_re_pos h₂)
  have hc₂ : (starRingEnd ℂ) (2:ℂ) = 2 := map_natCast (starRingEnd ℂ) 2
  have hc₆ : (starRingEnd ℂ) (6:ℂ) = 6 := map_natCast (starRingEnd ℂ) 6
  have he₁ : 5/6+(|ℓ|:ℤ)/2-s = star z₁ := by
    dsimp [z₁,s]
    norm_num [Complex.star_def,map_div]
    rw [hc₂,hc₆]
    ring
  have he₂ : 7/6+(|ℓ|:ℤ)/2-s = star z₂ := by
    dsimp [z₂,s]
    norm_num [Complex.star_def,map_div]
    rw [hc₂,hc₆]
    ring
  change ‖(Complex.Gamma (5/6+(|ℓ|:ℤ)/2-s)*
    Complex.Gamma (7/6+(|ℓ|:ℤ)/2-s))/(Complex.Gamma z₁*Complex.Gamma z₂)‖ = 1
  rw [he₁,he₂]
  simp only [Complex.star_def,Complex.Gamma_conj,norm_div,norm_mul,Complex.norm_conj]
  exact div_self (by simpa only [norm_mul] using norm_ne_zero_iff.mpr hn)

end CubicFirstMoment

end

end OAI
