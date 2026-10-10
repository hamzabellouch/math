import Mathlib
import OAI.NumberTheory.CubicGram.FrequencyGauss
import OAI.NumberTheory.CubicGram.PeriodicPoisson

namespace OAI

/-! Primary mixed characters and squarefree coset Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicSymbol_cube_of_isCoprime {c : Eisenstein} (hc : primary c)
    (v : Eisenstein) (hv : IsCoprime c v) : cubicSymbol c v ^ 3 = 1 := by
  revert v
  apply primary_induction (b := c) ?_ ?_ hc
  · intro v _
    rw [cubicSymbol_one_lower, one_pow]
  · intro p b hp hb ih v hv
    rw [cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hb), mul_pow,
      cubicSymbol_prime hp, cubicSymbolAtPrime_unit_cube hp
        (residue_isUnit_of_isCoprime hv.of_mul_left_left), ih v hv.of_mul_left_right,
      one_mul]

lemma cubicSymbol_three_lambda {c : Eisenstein} (hc : primary c) :
    cubicSymbol c (3 * lambdaE) = 1 := by
  rw [three_lambda_cube, pow_succ, pow_two, cubicSymbol_mul_upper hc,
    cubicSymbol_mul_upper hc, cubicSymbol_neg hc]
  simpa only [pow_succ, pow_two, pow_zero, one_mul] using
    cubicSymbol_cube_of_isCoprime hc lambdaE (primary_coprime_lambda hc)

def mixedSymbol (a b v : Eisenstein) : ℂ := cubicSymbol a v * star (cubicSymbol b v)

lemma mixedSymbol_mul {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (v w : Eisenstein) : mixedSymbol a b (v*w) = mixedSymbol a b v * mixedSymbol a b w := by
  simp only [mixedSymbol, cubicSymbol_mul_upper ha, cubicSymbol_mul_upper hb, star_mul']
  ring

lemma mixedSymbol_three_lambda {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    mixedSymbol a b (3*lambdaE) = 1 := by
  simp only [mixedSymbol, cubicSymbol_three_lambda ha, cubicSymbol_three_lambda hb,
    star_one, mul_one]

lemma mixedSymbol_congr {a b v w : Eisenstein}
    (h : Ideal.Quotient.mk (modulus (a*b)) v = Ideal.Quotient.mk (modulus (a*b)) w) :
    mixedSymbol a b v = mixedSymbol a b w := by
  have hd : a*b ∣ v-w := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  unfold mixedSymbol
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub
    (dvd_trans (dvd_mul_right a b) hd))]
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub
    (dvd_trans (dvd_mul_left b a) hd))]

end CubicFirstMoment

namespace CubicFirstMoment

def primaryMixedFourier (a b h : Eisenstein) : ℂ :=
  ∑' v : Residues (a*b), mixedSymbol a b (3 * residueRepresentative (a*b) v) *
    (Real.fourierChar (tracePair (residueRepresentative (a*b) v : ℂ)
      ((h : ℂ) / (((a*b : Eisenstein) : ℂ) * traceLambda))) : ℂ)

lemma primaryMixedFourier_eq {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (h : Eisenstein) :
    primaryMixedFourier a b h = (Real.sqrt (norm (a*b)) : ℂ) * mixedFrequencyGauss a b h := by
  have hc := primary_mul ha hb
  have hc0 := primary_ne_zero hc
  have hc0' : ((a*b : Eisenstein) : ℂ) ≠ 0 := fun he => hc0 (Subtype.ext he)
  obtain ⟨u, hu⟩ := residue_isUnit_of_isCoprime (primary_coprime_lambda hc)
  let e := u.mulLeft
  let F (v : Residues (a*b)) :=
    mixedSymbol a b (3 * residueRepresentative (a*b) v) *
    (Real.fourierChar (tracePair (residueRepresentative (a*b) v : ℂ)
      ((h : ℂ) / (((a*b : Eisenstein) : ℂ) * traceLambda))) : ℂ)
  have hreindex (v : Residues (a*b)) :
      Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus (a*b)) (lambdaE * residueRepresentative (a*b) v) := by
    rw [residueRepresentative_spec, map_mul, residueRepresentative_spec]
    change (u : Residues (a*b)) * v = _
    rw [hu]
  have hF (v : Residues (a*b)) : F (e v) =
      mixedSymbol a b (residueRepresentative (a*b) v) *
        additivePhase (a*b) (h * residueRepresentative (a*b) v) := by
    dsimp only [F]
    rw [mixedSymbol_congr (show Ideal.Quotient.mk (modulus (a*b))
      (3 * residueRepresentative (a*b) (e v)) = Ideal.Quotient.mk (modulus (a*b))
      (3 * (lambdaE * residueRepresentative (a*b) v)) by rw [map_mul, map_mul, hreindex])]
    rw [← mul_assoc, mixedSymbol_mul ha hb, mixedSymbol_three_lambda ha hb, one_mul,
      tracePhase_congr hc0 h (hreindex v), additivePhase_fourierChar]
    congr 2
    unfold tracePair
    congr 2
    simp only [Subalgebra.coe_mul, lambdaE_coe]
    field_simp [traceLambda_ne_zero]
  unfold primaryMixedFourier
  change (∑' v, F v) = _
  rw [← e.tsum_eq F]
  simp_rw [hF]
  unfold mixedFrequencyGauss
  have hs : (Real.sqrt (norm (a*b)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (Complex.normSq_pos.mpr hc0'))
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  rfl

theorem primaryMixedFourier_squarefree {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (h : Eisenstein) :
    primaryMixedFourier a b h = (Real.sqrt (norm (a*b)) : ℂ) *
      (gauss a * star (gauss b)) * (star (cubicSymbol a h) * cubicSymbol b h) := by
  rw [primaryMixedFourier_eq ha hb, mixedFrequencyGauss_squarefree ha hb hsa hsb hab]
  ring

end CubicFirstMoment

namespace CubicFirstMoment

lemma traceFourier_affine (f : 𝓢(ℂ, ℂ)) (z q : ℂ) (hq : q ≠ 0) (w : ℂ) :
    traceFourier (fun x => f (z + q * x)) w =
      (Complex.normSq q)⁻¹ • ((Real.fourierChar (tracePair z (w/q)) : ℂ) *
        traceFourier f (w/q)) := by
  simpa only [traceFourier_translation] using
    (traceFourier_complexMul q hq (fun y => f (z+y)) w)

theorem poisson_eisenstein_periodic_coset (c : Eisenstein) (hc : c ≠ 0)
    (ψ : Residues c → ℂ) (f : 𝓢(ℂ, ℂ)) (z q : ℂ) (hq : q ≠ 0) :
    ∑' a : Eisenstein, ψ (Ideal.Quotient.mk (modulus c) a) * f (z+q*(a : ℂ)) =
      (2 / (Real.sqrt 3 * norm c * Complex.normSq q) : ℝ) • ∑' h : Eisenstein,
        (∑' v : Residues c, ψ v *
          (Real.fourierChar (tracePair (residueRepresentative c v : ℂ)
            ((h : ℂ) / ((c : ℂ) * traceLambda))) : ℂ)) *
        (Real.fourierChar (tracePair z ((h : ℂ) / (q*(c : ℂ)*traceLambda))) : ℂ) *
        traceFourier f ((h : ℂ) / (q*(c : ℂ)*traceLambda)) := by
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexMulEquiv q hq)
    (f.compSubConstCLM ℂ (-z))
  have hg : (g : ℂ → ℂ) = (fun x => f (z+q*x)) := by
    funext x
    simp [g, add_comm]
  have he := poisson_eisenstein_periodic c hc ψ g
  rw [hg] at he
  simp_rw [traceFourier_affine f z q hq] at he
  have hfreq (h : Eisenstein) : ((h : ℂ) / ((c : ℂ)*traceLambda)) / q =
      (h : ℂ) / (q*(c : ℂ)*traceLambda) := by ring
  simp_rw [hfreq, mul_smul_comm, ← mul_assoc] at he
  rw [tsum_const_smul'', smul_smul] at he
  convert he using 1
  congr 1
  ring

end CubicFirstMoment

namespace CubicFirstMoment

theorem poisson_primary_mixed_squarefree {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (f : 𝓢(ℂ, ℂ)) :
    ∑' s : Eisenstein, mixedSymbol a b (a*b+3*s) * f ((a*b+3*s : Eisenstein) : ℂ) =
      (2 / (Real.sqrt 3 * norm (a*b) * 9) : ℝ) • ∑' h : Eisenstein,
        ((Real.sqrt (norm (a*b)) : ℂ) * (gauss a * star (gauss b)) *
          (star (cubicSymbol a h) * cubicSymbol b h)) *
        (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ) *
        traceFourier f ((h : ℂ) / (3*((a*b : Eisenstein) : ℂ)*traceLambda)) := by
  have hc0 := primary_ne_zero (primary_mul ha hb)
  have hc0' : ((a*b : Eisenstein) : ℂ) ≠ 0 := fun h => hc0 (Subtype.ext h)
  let ψ (v : Residues (a*b)) := mixedSymbol a b (3*residueRepresentative (a*b) v)
  have hψ (s : Eisenstein) : ψ (Ideal.Quotient.mk (modulus (a*b)) s) =
      mixedSymbol a b (a*b+3*s) := by
    apply mixedSymbol_congr
    simp only [map_mul, map_add, residueRepresentative_spec]
    have hz : Ideal.Quotient.mk (modulus (a*b)) (a*b) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton (a*b)))
    rw [map_mul] at hz
    rw [hz, zero_add]
  have hphase (h : Eisenstein) : tracePair ((a*b : Eisenstein) : ℂ)
      ((h : ℂ) / (3*((a*b : Eisenstein) : ℂ)*traceLambda)) =
      tracePair (h : ℂ) (1 / (3*traceLambda)) := by
    unfold tracePair
    congr 2
    field_simp
  have hfin (h : Eisenstein) : (∑' v : Residues (a*b), ψ v *
      (Real.fourierChar (tracePair (residueRepresentative (a*b) v : ℂ)
        ((h : ℂ) / (((a*b : Eisenstein) : ℂ)*traceLambda))) : ℂ)) =
      (Real.sqrt (norm (a*b)) : ℂ) * (gauss a * star (gauss b)) *
        (star (cubicSymbol a h) * cubicSymbol b h) :=
    primaryMixedFourier_squarefree ha hb hsa hsb hab h
  have he := poisson_eisenstein_periodic_coset (a*b) hc0 ψ f
    ((a*b : Eisenstein) : ℂ) 3 (by norm_num)
  simp_rw [hψ, hfin, hphase] at he
  have h3 : ((3 : Eisenstein) : ℂ) = 3 := rfl
  norm_num [Subalgebra.coe_add, Subalgebra.coe_mul, Complex.normSq_ofNat, h3] at he ⊢
  exact he

end CubicFirstMoment
end
end
end

end OAI
