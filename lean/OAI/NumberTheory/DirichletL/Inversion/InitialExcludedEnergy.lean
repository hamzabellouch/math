import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPolynomial

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialExcludedEnergy
open HeckeFamily HeckeDyadic InverseInitialExcludedPolynomial
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

def deletionWeight (χ:Character)(j:Ideal O):ℂ:=
  (moebius j:ℂ)*idealCoeff χ j*(j.absNorm:ℂ)^(-(1/2:ℂ))

theorem deletionWeight_norm_le_one (χ:Character){j:Ideal O}(hj:j≠0):
    ‖deletionWeight χ j‖≤1 := by
  have hn:1≤(j.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj)
  have hp:0<(j.absNorm:ℝ):=lt_of_lt_of_le zero_lt_one hn
  have hw:‖(j.absNorm:ℂ)^(-(1/2:ℂ))‖≤1:=by
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hp]
    apply Real.rpow_le_one_of_one_le_of_nonpos hn
    norm_num
  dsimp [deletionWeight]
  rw [norm_mul,norm_mul]
  calc
    _≤1*1:=mul_le_mul
      (by simpa only [one_mul] using (mul_le_mul (CubicEisenstein.norm_ideal_moebius_le_one j)
        (idealCoeff_norm_le_one χ j) (norm_nonneg _) zero_le_one)) hw
      (norm_nonneg _) (by positivity)
    _=1:=one_mul _

theorem marked_pointwise (χ:Character)(S:Finset (Ideal O))(hS:∀P∈S,Prime P)
    (W:ℝ→ℂ)(X σ t b:ℝ)(hX:0<X)(hW:∀x,W x≠0→x≤b)(mark:ℂ):
    ‖polynomial χ true W X σ t*mark‖^2≤
    ((idealDivisors (∏P∈S,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈S,P),
        ‖polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖^2 := by
  rw [inverse_polynomial_decomposition χ S hS W X σ t b hX hW,Finset.sum_mul]
  have hn:‖∑j∈idealDivisors (∏P∈S,P),
      ((moebius j:ℂ)*idealCoeff χ j*(j.absNorm:ℂ)^(-(1/2:ℂ)))*
        polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖≤
      ∑j∈idealDivisors (∏P∈S,P),
        ‖polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖:=by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro j hj
    change ‖deletionWeight χ j*polynomial _ _ _ _ _ _*mark‖≤_
    rw [mul_assoc,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    apply deletionWeight_norm_le_one χ
    exact ne_zero_of_dvd_ne_zero (prime_product_squarefree S hS).ne_zero
      ((mem_idealDivisors (prime_product_squarefree S hS).ne_zero).mp hj)
  have hh:=Finset.sum_mul_sq_le_sq_mul_sq (idealDivisors (∏P∈S,P))
    (fun _=>(1:ℝ)) (fun j=>‖polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mpr hn |>.trans
    hh

theorem marked_family {ι:Type*}(rows:Finset ι)(χ:ι→Character)
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(W:ℝ→ℂ)(X σ t b:ℝ)
    (hX:0<X)(hW:∀x,W x≠0→x≤b)(mark:ι→ℂ)(weight:ι→ℝ)
    (hw:∀u∈rows,0≤weight u):
    (∑u∈rows,weight u*‖polynomial (χ u) true W X σ t*mark u‖^2)≤
      ((idealDivisors (∏P∈S,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈S,P),∑u∈rows,weight u*
        ‖polynomial ((χ u).excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark u‖^2 := by
  calc
    _≤∑u∈rows,weight u*(((idealDivisors (∏P∈S,P)).card:ℝ)*
      ∑j∈idealDivisors (∏P∈S,P),
        ‖polynomial ((χ u).excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t*mark u‖^2):=by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (marked_pointwise (χ u) S hS W X σ t b hX hW (mark u)) (hw u hu)
    _=_:=by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro u hu
      ring

end SevenEighths.InverseInitialExcludedEnergy

end

end OAI
