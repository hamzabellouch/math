import Mathlib
import OAI.NumberTheory.CubicGram.ResidueCharacters
import OAI.NumberTheory.CubicGram.LatticePoisson

namespace OAI

/-! Periodic lattice Poisson summation and exact trace frequencies. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment
open CubicPoisson

def traceFourierSchwartz (f : 𝓢(ℂ, ℂ)) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Complex.conjCLE.trans (complexMulEquiv 2 (by norm_num))) (𝓕 f)

lemma traceFourierSchwartz_apply (f : 𝓢(ℂ, ℂ)) (w : ℂ) :
    traceFourierSchwartz f w = traceFourier f w := by
  change (𝓕 f) (2 * star w) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq, traceFourier]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Circle.smul_def, smul_eq_mul]
  congr 2
  simp only [real_inner_eq_re_inner ℂ, RCLike.inner_apply, tracePair,
    Complex.star_def, RCLike.re_to_complex, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.re_ofNat, Complex.im_ofNat]
  congr 1
  ring

lemma schwartz_summable_eisenstein (f : 𝓢(ℂ, ℂ)) :
    Summable (fun a : Eisenstein => f (a : ℂ)) := by
  apply coordinatesEquiv.toEquiv.summable_iff.mp
  change Summable (fun n : Fin 2 → ℤ => f (coordinatesEquiv n : ℂ))
  simpa only [coordinatesEquiv_coe, eisensteinPullback,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply] using
      schwartz_summable_integerCoordinates (eisensteinPullback f)

lemma schwartz_summable_eisenstein_coset (f : 𝓢(ℂ, ℂ)) (q : ℂ) (hq : q ≠ 0) (z : ℂ) :
    Summable (fun a : Eisenstein => f (z + q * (a : ℂ))) := by
  have h := schwartz_summable_eisenstein
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexMulEquiv q hq)
      (f.compSubConstCLM ℂ (-z)))
  simpa only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    complexMulEquiv_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add,
    add_comm] using h

lemma traceFourier_summable_eisenstein (f : 𝓢(ℂ, ℂ)) (q : ℂ) (hq : q ≠ 0) :
    Summable (fun h : Eisenstein => traceFourier f ((h : ℂ) / q)) := by
  have h := schwartz_summable_eisenstein_coset
    (traceFourierSchwartz f) q⁻¹ (inv_ne_zero hq) 0
  simpa only [traceFourierSchwartz_apply, zero_add, div_eq_mul_inv, mul_comm] using h

lemma traceFourier_phase_summable (f : 𝓢(ℂ, ℂ)) (q : ℂ) (hq : q ≠ 0) (z : ℂ) :
    Summable (fun h : Eisenstein =>
      (Real.fourierChar (tracePair z ((h : ℂ) / q)) : ℂ) *
        traceFourier f ((h : ℂ) / q)) := by
  apply Summable.of_norm_bounded (traceFourier_summable_eisenstein f q hq).norm
  intro h
  simp only [norm_mul, Circle.norm_coe, one_mul, le_refl]

end CubicFirstMoment

namespace CubicFirstMoment

def residueCosetMap (c : Eisenstein) (x : Residues c × Eisenstein) : Eisenstein :=
  residueRepresentative c x.1 + c * x.2

lemma residueCosetMap_mk (c : Eisenstein) (x : Residues c × Eisenstein) :
    Ideal.Quotient.mk (modulus c) (residueCosetMap c x) = x.1 := by
  simp only [residueCosetMap, map_add, map_mul, residueRepresentative_spec]
  have h : Ideal.Quotient.mk (modulus c) c = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton c)
  simp [h]

lemma residueCosetMap_bijective {c : Eisenstein} (hc : c ≠ 0) :
    Function.Bijective (residueCosetMap c) := by
  constructor
  · intro x y h
    have hxy : x.1 = y.1 := by
      simpa only [residueCosetMap_mk] using congrArg (Ideal.Quotient.mk (modulus c)) h
    apply Prod.ext hxy
    have : c * x.2 = c * y.2 := by
      simpa only [residueCosetMap, hxy, add_right_inj] using h
    exact mul_left_cancel₀ hc this
  · intro a
    let v := Ideal.Quotient.mk (modulus c) a
    have hd : c ∣ a - residueRepresentative c v := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
      change Ideal.Quotient.mk (modulus c) (a - residueRepresentative c v) = 0
      rw [map_sub, residueRepresentative_spec]
      exact sub_self _
    obtain ⟨b, hb⟩ := hd
    exact ⟨(v, b), by dsimp [residueCosetMap]; linear_combination -hb⟩

end CubicFirstMoment

namespace CubicFirstMoment

lemma periodic_schwartz_summable (c : Eisenstein) (hc : c ≠ 0)
    (ψ : Residues c → ℂ) (f : 𝓢(ℂ, ℂ)) :
    Summable (fun a : Eisenstein => ψ (Ideal.Quotient.mk (modulus c) a) * f (a : ℂ)) := by
  let : Finite (Residues c) := finite_residues hc
  let : Fintype (Residues c) := Fintype.ofFinite _
  let C := ∑ v : Residues c, ‖ψ v‖
  apply Summable.of_norm_bounded ((schwartz_summable_eisenstein f).norm.mul_left C)
  intro a
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (_root_.norm_nonneg _)
  exact Finset.single_le_sum (fun v _ => _root_.norm_nonneg (ψ v)) (Finset.mem_univ _)

theorem poisson_eisenstein_periodic (c : Eisenstein) (hc : c ≠ 0)
    (ψ : Residues c → ℂ) (f : 𝓢(ℂ, ℂ)) :
    ∑' a : Eisenstein, ψ (Ideal.Quotient.mk (modulus c) a) * f (a : ℂ) =
      (2 / (Real.sqrt 3 * norm c) : ℝ) • ∑' h : Eisenstein,
        (∑' v : Residues c, ψ v *
          (Real.fourierChar (tracePair (residueRepresentative c v : ℂ)
            ((h : ℂ) / ((c : ℂ) * traceLambda))) : ℂ)) *
        traceFourier f ((h : ℂ) / ((c : ℂ) * traceLambda)) := by
  classical
  let : Finite (Residues c) := finite_residues hc
  let : Fintype (Residues c) := Fintype.ofFinite _
  have hc' : (c : ℂ) ≠ 0 := fun h => hc (Subtype.ext h)
  let e := Equiv.ofBijective (residueCosetMap c) (residueCosetMap_bijective hc)
  let F (v : Residues c) (a : Eisenstein) :=
    ψ v * f ((residueRepresentative c v : ℂ) + (c : ℂ) * (a : ℂ))
  have hreindex : (fun x : Residues c × Eisenstein =>
      ψ (Ideal.Quotient.mk (modulus c) (e x)) * f (e x : ℂ)) = Function.uncurry F := by
    funext x
    change ψ (Ideal.Quotient.mk (modulus c) (residueCosetMap c x)) * _ = _
    rw [residueCosetMap_mk]
    rfl
  have hs : Summable (Function.uncurry F) := by
    rw [← hreindex]
    exact e.summable_iff.mpr (periodic_schwartz_summable c hc ψ f)
  calc
    _ = ∑' x : Residues c × Eisenstein, Function.uncurry F x := by
      rw [← hreindex]
      exact (e.tsum_eq _).symm
    _ = ∑ v : Residues c, ψ v * ∑' a : Eisenstein,
        f ((residueRepresentative c v : ℂ) + (c : ℂ) * (a : ℂ)) := by
      rw [hs.tsum_prod]
      simp only [tsum_fintype, F, Function.uncurry, tsum_mul_left]
    _ = _ := by
      simp_rw [poisson_eisenstein_coset f (c : ℂ) hc']
      let K : ℝ := 2 / (Real.sqrt 3 * norm c)
      change (∑ v : Residues c, ψ v * (K • ∑' h : Eisenstein,
        (Real.fourierChar (tracePair (residueRepresentative c v : ℂ)
          ((h : ℂ) / ((c : ℂ) * traceLambda))) : ℂ) *
        traceFourier f ((h : ℂ) / ((c : ℂ) * traceLambda)))) = _
      simp_rw [mul_smul_comm, ← tsum_mul_left]
      rw [← Finset.smul_sum]
      congr 1
      rw [← Summable.tsum_finsetSum]
      · apply tsum_congr
        intro h
        simp only [tsum_fintype, Finset.sum_mul, mul_assoc]
      · intro v _
        exact (traceFourier_phase_summable f ((c : ℂ) * traceLambda)
          (mul_ne_zero hc' traceLambda_ne_zero) (residueRepresentative c v : ℂ)).mul_left (ψ v)

end CubicFirstMoment

namespace CubicFirstMoment

def lambdaE : Eisenstein := 1 + 2 * omegaE

lemma lambdaE_coe : (lambdaE : ℂ) = traceLambda := rfl

lemma lambdaE_sq : lambdaE ^ 2 = -3 := by
  dsimp [lambdaE]
  linear_combination 4 * omegaE_quadratic

lemma three_lambda_cube : (3 : Eisenstein) * lambdaE = (-lambdaE) ^ 3 := by
  rw [pow_succ, neg_sq, lambdaE_sq]
  ring

lemma primary_coprime_lambda {c : Eisenstein} (hc : primary c) :
    IsCoprime c lambdaE := by
  obtain ⟨k, hk⟩ := hc
  refine ⟨1, lambdaE * k, ?_⟩
  linear_combination hk + k * lambdaE_sq

lemma tracePair_div_lambda_integral (z : Eisenstein) :
    ∃ n : ℤ, tracePair (z : ℂ) (1 / traceLambda) = (n : ℝ) := by
  obtain ⟨⟨a,b⟩, rfl⟩ := ofCoords_surjective z
  refine ⟨b, ?_⟩
  have hd : dualRealCoords ![0, 1] = 1 / traceLambda := by
    rw [dualRealCoords_eq]
    simp
  have hc : (ofCoords a b : ℂ) = eisensteinRealCoords ![(a : ℝ), (b : ℝ)] := by
    simp [eisensteinRealCoords_apply, ofCoords_coe]
  rw [hc, ← hd, dualRealCoords_trace]
  simp [Fin.sum_univ_two]

lemma fourierChar_int (n : ℤ) : (Real.fourierChar (n : ℝ) : ℂ) = 1 := by
  rw [Real.fourierChar_apply]
  push_cast
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  congr 1
  ring

lemma tracePhase_div_lambda_one (z : Eisenstein) :
    (Real.fourierChar (tracePair (z : ℂ) (1 / traceLambda)) : ℂ) = 1 := by
  obtain ⟨n, hn⟩ := tracePair_div_lambda_integral z
  rw [hn, fourierChar_int]

lemma additivePhase_fourierChar (p v : Eisenstein) :
    additivePhase p v = (Real.fourierChar (tracePair (v : ℂ) (1 / (p : ℂ))) : ℂ) := by
  rw [Real.fourierChar_apply]
  unfold additivePhase tracePair
  dsimp only
  congr 1
  have hz : ∀ z : ℂ, z + star z = (2 * z.re : ℝ) := by
    intro z
    apply Complex.ext <;> simp
    ring
  rw [hz]
  push_cast
  rw [one_div, ← div_eq_mul_inv]
  ring

lemma tracePhase_congr {c v w : Eisenstein} (hc : c ≠ 0) (h : Eisenstein)
    (he : Ideal.Quotient.mk (modulus c) v = Ideal.Quotient.mk (modulus c) w) :
    (Real.fourierChar (tracePair (v : ℂ) ((h : ℂ) / ((c : ℂ) * traceLambda))) : ℂ) =
      (Real.fourierChar (tracePair (w : ℂ) ((h : ℂ) / ((c : ℂ) * traceLambda))) : ℂ) := by
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have hc' : (c : ℂ) ≠ 0 := fun h => hc (Subtype.ext h)
  have hv : (v : ℂ) = (w : ℂ) + (c : ℂ) * (k : ℂ) := by
    exact_mod_cast (show v = w+c*k by linear_combination hk)
  rw [hv, tracePair_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]
  have hp : tracePair ((c : ℂ) * (k : ℂ)) ((h : ℂ) / ((c : ℂ) * traceLambda)) =
      tracePair ((k*h : Eisenstein) : ℂ) (1 / traceLambda) := by
    unfold tracePair
    congr 2
    push_cast
    field_simp
  rw [hp, tracePhase_div_lambda_one, mul_one]

end CubicFirstMoment

end
end
end

end OAI
