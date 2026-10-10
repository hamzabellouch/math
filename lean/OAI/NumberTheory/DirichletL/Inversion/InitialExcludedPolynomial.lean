import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedSource
import OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary
import OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialExcludedPolynomial
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge
open InverseInitialExcludedSource IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

theorem prime_product_squarefree (S:Finset (Ideal O))(hS:∀P∈S,Prime P):
    Squarefree (∏P∈S,P) := by
  have hz:(∏P∈S,P)≠0:=Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)
  apply (squarefree_iff_nodup_normalizedFactors hz).mpr
  have he:normalizedFactors (∏P∈S,P)=S.val:=by
    simpa using normalizedFactors_prod_of_prime (m:=S.val) (fun P hP=>hS P hP)
  rw [he]
  exact S.nodup

theorem deleted_coefficient_product (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(I:Ideal O):
    idealCoeff (χ.excludePrimes S hS) I=
      if IsCoprime I (∏P∈S,P) then idealCoeff χ I else 0 := by
  rw [idealCoeff_excludePrimes,IsCoprime.prod_right_iff]
  congr 1

theorem residual_source (χ:Character)(S A:Finset (Ideal O))(hS:∀P∈S,Prime P)
    {j:Ideal O}(hj:j∣∏P∈S,P)(W:ℝ→ℂ)(X:ℝ)
    (hcover:∀I:Ideal O,I≠0→W ((I.absNorm:ℝ)/X)≠0→I∈A):
    (∑c∈columns A (∏P∈S,P) j,(moebius c:ℂ)*idealCoeff χ c*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))))=
    ∑'c:Ideal O,(moebius c:ℂ)*idealCoeff (χ.excludePrimes S hS) c*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have hP:=prime_product_squarefree S hS
  have hj0:=ne_zero_of_dvd_ne_zero hP.ne_zero hj
  symm
  calc
    _ = ∑c∈columns A (∏P∈S,P) j,(moebius c:ℂ)*idealCoeff (χ.excludePrimes S hS) c*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
      apply tsum_eq_sum
      intro c hc
      by_cases hcs:Squarefree c
      · by_cases hcp:IsCoprime c (∏P∈S,P)
        · have hw:W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ)))=0:=by
            by_contra hw
            apply hc
            apply (mem_columns hP hj).mpr
            refine ⟨hcs,hcp,hcover (j*c) (mul_ne_zero hj0 hcs.ne_zero) ?_⟩
            rwa [cutoff_argument]
          rw [hw,mul_zero]
        · rw [deleted_coefficient_product,ite_eq_right hcp,mul_zero,zero_mul]
      · rw [moebius_of_not_squarefree hcs,Int.cast_zero,zero_mul,zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [deleted_coefficient_product,ite_eq_left ((mem_columns hP hj).mp hc).2.1]

theorem source_decomposition (χ:Character)(S A:Finset (Ideal O))(hS:∀P∈S,Prime P)
    (W:ℝ→ℂ)(X:ℝ)(hcover:∀I:Ideal O,I≠0→W ((I.absNorm:ℝ)/X)≠0→I∈A):
    (∑I∈A,(moebius I:ℂ)*idealCoeff χ I*W ((I.absNorm:ℝ)/X))=
    ∑j∈idealDivisors (∏P∈S,P),((moebius j:ℂ)*idealCoeff χ j)*
      ∑'c:Ideal O,(moebius c:ℂ)*idealCoeff (χ.excludePrimes S hS) c*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have he:=polynomial_decomposition A (prime_product_squarefree S hS)
    (idealCoeff χ).toMonoidHom (fun _=>1) W X
  simp only [mul_one] at he
  trans ∑j∈idealDivisors (∏P∈S,P),((moebius j:ℂ)*idealCoeff χ j)*
    ∑c∈columns A (∏P∈S,P) j,(moebius c:ℂ)*idealCoeff χ c*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ)))
  · exact he
  apply Finset.sum_congr rfl
  intro j hj
  rw [residual_source χ S A hS ((mem_idealDivisors (prime_product_squarefree S hS).ne_zero).mp hj) W X hcover]

theorem polynomial_all_ideals (χ:Character)(W:ℝ→ℂ)(X σ t:ℝ):
    polynomial χ true W X σ t=(X:ℂ)^(-(1/2:ℂ))*
      ∑'I:Ideal O,(moebius I:ℂ)*idealCoeff χ I*
        (W ((I.absNorm:ℝ)/X)*(((I.absNorm:ℝ)/X:ℝ):ℂ)^(-shift σ t)) := by
  unfold polynomial
  congr 1
  let f:Ideal O→ℂ:=fun I=>(moebius I:ℂ)*idealCoeff χ I*
    (W ((I.absNorm:ℝ)/X)*(((I.absNorm:ℝ)/X:ℝ):ℂ)^(-shift σ t))
  have hf:Function.support f⊆{I:Ideal O|I≠0}:=by
    intro I hi hz
    subst I
    exact hi (by simp only [f,map_zero,mul_zero,zero_mul])
  have he:=tsum_subtype_eq_of_support_subset hf
  calc
    _=∑'I:{I:Ideal O//I≠0},f I.val:=by
      apply tsum_congr
      intro I
      simp only [summand,coefficient,ite_true,HeckeDyadic.norm,f]
      ring
    _=_:=he

theorem scale_normalization (X n:ℝ)(hX:0<X)(hn:0<n):
    (n:ℂ)^(-(1/2:ℂ))*((X/n:ℝ):ℂ)^(-(1/2:ℂ))=(X:ℂ)^(-(1/2:ℂ)) := by
  rw [←Complex.mul_cpow_ofReal_nonneg hn.le (div_pos hX hn).le,
    ←Complex.ofReal_mul,mul_div_cancel₀ _ hn.ne']

theorem inverse_polynomial_decomposition (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(W:ℝ→ℂ)(X σ t b:ℝ)(hX:0<X)
    (hW:∀x,W x≠0→x≤b):
    polynomial χ true W X σ t=
    ∑j∈idealDivisors (∏P∈S,P),
      ((moebius j:ℂ)*idealCoeff χ j*(j.absNorm:ℂ)^(-(1/2:ℂ)))*
        polynomial (χ.excludePrimes S hS) true W (X/(j.absNorm:ℝ)) σ t := by
  let A:=ConcretePrimeRowBridge.idealsUpTo ⌈X*b⌉₊
  let V:ℝ→ℂ:=fun x=>W x*(x:ℂ)^(-shift σ t)
  have hc:∀I:Ideal O,I≠0→W ((I.absNorm:ℝ)/X)≠0→I∈A:=
    InverseInitialRawDictionary.finite_source_cover W X b hX hW
  have hcv:∀I:Ideal O,I≠0→V ((I.absNorm:ℝ)/X)≠0→I∈A:=by
    intro I hi hv
    apply hc I hi
    intro hw
    exact hv (by simp [V,hw])
  rw [polynomial_eq_finite χ true W X σ t A hc]
  have hsource:=source_decomposition χ S A hS V X hcv
  have hfinite:(∑I∈A,coefficient χ true I*W ((I.absNorm:ℝ)/X)*
      (((I.absNorm:ℝ)/X:ℝ):ℂ)^(-shift σ t))=
      ∑I∈A,(moebius I:ℂ)*idealCoeff χ I*V ((I.absNorm:ℝ)/X):=by
    apply Finset.sum_congr rfl
    intro I hi
    simp only [coefficient,ite_true,V]
    ring
  rw [hfinite,hsource,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd: j∣∏P∈S,P:=(mem_idealDivisors (prime_product_squarefree S hS).ne_zero).mp hj
  have hj0:j≠0:=ne_zero_of_dvd_ne_zero (prime_product_squarefree S hS).ne_zero hjd
  have hjpos:0<(j.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  rw [polynomial_all_ideals]
  have hn:=scale_normalization X (j.absNorm:ℝ) hX hjpos
  simp only [Complex.ofReal_natCast] at hn
  dsimp only [V]
  rw [←hn]
  ring

end SevenEighths.InverseInitialExcludedPolynomial

end

end OAI
