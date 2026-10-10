import Mathlib
import OAI.NumberTheory.CubicGauss.LatticePoisson

namespace OAI

/-! Residue-class theta transforms and primitive additive trace characters. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment.HeckeTheta
def residueCosetMap (q : Eisenstein) (v : Residues q × Eisenstein) : Eisenstein :=
  residueRepresentative q v.1 + q * v.2

lemma residueCosetMap_bijective (q : Eisenstein) (hq : q ≠ 0) :
    Function.Bijective (residueCosetMap q) := by
  have hmq : Ideal.Quotient.mk (modulus q) q = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  constructor
  · rintro ⟨v,a⟩ ⟨w,b⟩ h
    have he := congrArg (Ideal.Quotient.mk (modulus q)) h
    simp only [residueCosetMap, map_add, map_mul, residueRepresentative_spec,
      hmq,
      zero_mul, add_zero] at he
    subst w
    have hab : a = b := mul_left_cancel₀ hq (add_left_cancel h)
    exact Prod.ext rfl hab
  · intro a
    have hh : a - residueRepresentative q (Ideal.Quotient.mk (modulus q) a) ∈ modulus q := by
      apply Ideal.Quotient.eq.mp
      rw [residueRepresentative_spec]
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp hh
    exact ⟨(Ideal.Quotient.mk (modulus q) a,b), by dsimp [residueCosetMap]; linear_combination -hb⟩

noncomputable def residueCosetEquiv (q : Eisenstein) (hq : q ≠ 0) :
    Residues q × Eisenstein ≃ Eisenstein :=
  Equiv.ofBijective (residueCosetMap q) (residueCosetMap_bijective q hq)

@[simp] lemma residueCosetEquiv_apply (q : Eisenstein) (hq : q ≠ 0)
    (v : Residues q) (b : Eisenstein) :
    residueCosetEquiv q hq (v,b) = residueRepresentative q v + q * b := rfl

lemma norm_pos {q : Eisenstein} (hq : q ≠ 0) : 0 < norm q :=
  lt_of_le_of_ne (norm_nonneg q) (Ne.symm (mt norm_eq_zero_iff.mp hq))

lemma coe_ne_zero {q : Eisenstein} (hq : q ≠ 0) : (q : ℂ) ≠ 0 := by
  exact fun h => hq (Subtype.ext h)

lemma coset_norm (q r b : Eisenstein) (hq : q ≠ 0) :
    norm (r + q*b) = norm q * Complex.normSq ((b : ℂ) + (r : ℂ) / (q : ℂ)) := by
  have he : ((r + q*b : Eisenstein) : ℂ) =
      (q : ℂ) * ((b : ℂ) + (r : ℂ) / (q : ℂ)) := by
    change (r : ℂ) + (q : ℂ) * b = _
    field_simp [coe_ne_zero hq]
    ring
  rw [norm, he, Complex.normSq_mul]
  rfl

lemma coset_gaussian_poisson (q r : Eisenstein) (hq : q ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    (∑' b : Eisenstein, Complex.exp (-(Real.pi : ℂ) * t * (norm (r+q*b) : ℂ))) =
      2 / ((Real.sqrt 3 : ℂ) * t * norm q) *
      ∑' b : Eisenstein,
        Complex.exp (-(4 * (Real.pi : ℂ)) / (3 * t * norm q) * (norm b : ℂ)) *
          tracePhase b ((r : ℂ) / q) := by
  have he : (fun b : Eisenstein => Complex.exp (-(Real.pi : ℂ) * t * (norm (r+q*b) : ℂ))) =
      (fun b : Eisenstein => Complex.exp (-(Real.pi : ℂ) * ((t * norm q : ℝ) : ℂ) *
        (Complex.normSq ((b : ℂ) + (r : ℂ) / q) : ℂ))) := by
    funext b
    rw [coset_norm q r b hq]
    push_cast
    congr 1
    ring
  rw [he, lattice_gaussian_poisson (t*norm q) ((r : ℂ)/q) (mul_pos ht (norm_pos hq))]
  push_cast
  simp only [mul_assoc]

 

def residueFourier (q : Eisenstein) (w : Residues q → ℂ) (b : Eisenstein) : ℂ :=
  ∑' v : Residues q, w v * tracePhase b ((residueRepresentative q v : ℂ) / q)

 

def residueTheta (q : Eisenstein) (w : Residues q → ℂ) (t : ℝ) : ℂ :=
  ∑' a : Eisenstein, w (Ideal.Quotient.mk (modulus q) a) *
    Complex.exp (-(Real.pi : ℂ) * t * (norm a : ℂ))

lemma weighted_lattice_gaussian_summable (q : Eisenstein) (hq : q ≠ 0)
    (w : Residues q → ℂ) (t : ℝ) (ht : 0 < t) :
    Summable (fun a : Eisenstein => w (Ideal.Quotient.mk (modulus q) a) *
      Complex.exp (-(Real.pi : ℂ) * t * (norm a : ℂ))) := by
  let : Finite (Residues q) := finite_residues hq
  let : Fintype (Residues q) := Fintype.ofFinite _
  have hs := (lattice_gaussian_summable t 0 ht).norm.mul_left
    (∑ v : Residues q, ‖w v‖)
  simp only [add_zero] at hs
  refine hs.of_norm_bounded fun a => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun v _ => _root_.norm_nonneg (w v))
      (Finset.mem_univ (Ideal.Quotient.mk (modulus q) a))) (_root_.norm_nonneg _)

lemma phase_gaussian_summable (q : Eisenstein) (hq : q ≠ 0)
    (t : ℝ) (ht : 0 < t) (z : ℂ) :
    Summable (fun b : Eisenstein =>
      Complex.exp (-(4 * (Real.pi : ℂ)) / (3 * t * norm q) * (norm b : ℂ)) *
        tracePhase b z) := by
  convert lattice_gaussian_phase_summable (4/(3*t*norm q)) z
    (by positivity [norm_pos hq]) using 1
  ext b
  congr 1
  congr 1
  push_cast
  ring

 

theorem residue_theta_poisson (q : Eisenstein) (hq : q ≠ 0)
    (w : Residues q → ℂ) (t : ℝ) (ht : 0 < t) :
    residueTheta q w t =
      2 / ((Real.sqrt 3 : ℂ) * t * norm q) * ∑' b : Eisenstein,
        Complex.exp (-(4 * (Real.pi : ℂ)) / (3 * t * norm q) * (norm b : ℂ)) *
          residueFourier q w b := by
  let : Finite (Residues q) := finite_residues hq
  let : Fintype (Residues q) := Fintype.ofFinite _
  have hmq : Ideal.Quotient.mk (modulus q) q = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hf := weighted_lattice_gaussian_summable q hq w t ht
  have hprod := ((residueCosetEquiv q hq).summable_iff.mpr hf).tsum_prod
  simp only [Function.comp_apply] at hprod
  rw [residueTheta, ← (residueCosetEquiv q hq).tsum_eq
    (fun a : Eisenstein => w (Ideal.Quotient.mk (modulus q) a) *
      Complex.exp (-(Real.pi : ℂ) * t * (norm a : ℂ))), hprod]
  simp only [residueCosetEquiv_apply, map_add, map_mul, hmq, zero_mul, add_zero,
    residueRepresentative_spec, tsum_mul_left]
  simp_rw [coset_gaussian_poisson q _ hq t ht]
  rw [tsum_fintype]
  simp_rw [mul_left_comm (w _) (2 / ((Real.sqrt 3 : ℂ) * t * norm q))]
  rw [← Finset.mul_sum]
  congr 1
  simp only [residueFourier, tsum_fintype]
  simp_rw [← tsum_mul_left, Finset.mul_sum, mul_left_comm]
  simpa only [mul_assoc, mul_left_comm] using
    (Summable.tsum_finsetSum (s := Finset.univ) (fun v _ =>
      (phase_gaussian_summable q hq t ht ((residueRepresentative q v : ℂ)/q)).mul_left (w v))).symm

lemma tracePhase_add_right (b z w : ℂ) :
    tracePhase b (z+w) = tracePhase b z * tracePhase b w := by
  simp only [tracePhase, mul_add, add_div, star_add]
  rw [← Complex.exp_add]
  congr 1
  ring

lemma tracePhase_integral (b a : Eisenstein) : tracePhase b a = 1 := by
  obtain ⟨⟨m,n⟩,he⟩ := ofCoords_surjective (b*a)
  have hc : (b : ℂ)*(a : ℂ) = (m : ℂ)+(n : ℂ)*omega := by
    exact congrArg (fun z : Eisenstein => (z : ℂ)) he.symm
  simp only [tracePhase]
  rw [hc]
  have ht := trace_div_lambda_coordinates (m : ℝ) (n : ℝ)
  simp only [Complex.ofReal_intCast] at ht
  rw [ht, mul_comm _ (n : ℂ), Complex.exp_int_mul_two_pi_mul_I]

lemma tracePhase_modulus_congr (q : Eisenstein) (hq : q ≠ 0)
    (v w : Eisenstein)
    (h : Ideal.Quotient.mk (modulus q) v = Ideal.Quotient.mk (modulus q) w)
    (b : Eisenstein) :
    tracePhase b ((v : ℂ)/q) = tracePhase b ((w : ℂ)/q) := by
  obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have hv : v = w+q*a := by linear_combination ha
  have hd : ((v : ℂ)/q) = (w : ℂ)/q+(a : ℂ) := by
    rw [hv]
    change ((w : ℂ)+(q : ℂ)*a)/q = _
    rw [add_div,mul_div_cancel_left₀ _ (coe_ne_zero hq)]
  rw [hd,tracePhase_add_right,tracePhase_integral,mul_one]

 

def residueTraceChar (q : Eisenstein) (hq : q ≠ 0) : AddChar (Residues q) ℂ where
  toFun v := tracePhase 1 ((residueRepresentative q v : ℂ)/q)
  map_zero_eq_one' := by
    have h := tracePhase_modulus_congr q hq (residueRepresentative q 0) 0
      (by simp [residueRepresentative_spec]) 1
    simpa [tracePhase] using h
  map_add_eq_mul' v w := by
    have h := tracePhase_modulus_congr q hq (residueRepresentative q (v+w))
      (residueRepresentative q v+residueRepresentative q w)
      (by simp [residueRepresentative_spec]) 1
    simp only [Subalgebra.coe_one] at h
    rw [h]
    change tracePhase 1 (((residueRepresentative q v : ℂ)+
      (residueRepresentative q w : ℂ))/q) = _
    rw [add_div,tracePhase_add_right]

lemma residueTraceChar_mk (q : Eisenstein) (hq : q ≠ 0) (a : Eisenstein) :
    residueTraceChar q hq (Ideal.Quotient.mk (modulus q) a) =
      tracePhase 1 ((a : ℂ)/q) := by
  exact tracePhase_modulus_congr q hq _ a (residueRepresentative_spec q _) 1

lemma residueTraceChar_mul_mk (q : Eisenstein) (hq : q ≠ 0)
    (v : Residues q) (b : Eisenstein) :
    residueTraceChar q hq (v*Ideal.Quotient.mk (modulus q) b) =
      tracePhase b ((residueRepresentative q v : ℂ)/q) := by
  conv_lhs => rw [← residueRepresentative_spec q v, ← map_mul, residueTraceChar_mk]
  simp only [tracePhase, one_mul, Subalgebra.coe_mul]
  congr 2; ring_nf

lemma phase_real_eq_one_iff (y : ℝ) :
    Complex.exp (2*(Real.pi : ℂ)*I*(y : ℂ))=1 ↔ ∃ n : ℤ, y=(n : ℝ) := by
  have hc : 2*(Real.pi : ℂ)*I ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    · exact I_ne_zero
  constructor
  · intro h
    obtain ⟨n,hn⟩ := Complex.exp_eq_one_iff.mp h
    have hy : (y : ℂ)=(n : ℂ) := mul_left_cancel₀ hc (by simpa [mul_comm] using hn)
    exact ⟨n, by exact_mod_cast hy⟩
  · rintro ⟨n,rfl⟩
    simpa [mul_comm] using Complex.exp_int_mul_two_pi_mul_I n

 

lemma trace_dual_integral (z : ℂ) (h : ∀ b : Eisenstein, tracePhase b z=1) :
    ∃ a : Eisenstein, (a : ℂ)=z := by
  let x : ℝ := z.re+z.im/Real.sqrt 3
  let y : ℝ := 2*z.im/Real.sqrt 3
  have hz : z=(x : ℂ)+(y : ℂ)*omega := complex_coordinates z
  have hy : Complex.exp (2*(Real.pi : ℂ)*I*(y : ℂ))=1 := by
    have hh := h (ofCoords (0+1) 0)
    rw [hz,dual_phase] at hh
    simpa using hh
  have hx : Complex.exp (2*(Real.pi : ℂ)*I*((x-y : ℝ) : ℂ))=1 := by
    have hh := h (ofCoords (1+(-1)) 1)
    rw [hz,dual_phase] at hh
    simpa [sub_eq_add_neg] using hh
  obtain ⟨n,hn⟩ := (phase_real_eq_one_iff y).mp hy
  obtain ⟨m,hm⟩ := (phase_real_eq_one_iff (x-y)).mp hx
  refine ⟨ofCoords (m+n) n, ?_⟩
  rw [hz,ofCoords_coe]
  have hx' : x=(m : ℝ)+(n : ℝ) := by linarith
  rw [hx',hn]
  push_cast
  rfl

theorem residueTraceChar_primitive (q : Eisenstein) (hq : q ≠ 0) :
    (residueTraceChar q hq).IsPrimitive := by
  intro v hv hshift
  have hphase (b : Eisenstein) :
      tracePhase b ((residueRepresentative q v : ℂ)/q)=1 := by
    rw [← residueTraceChar_mul_mk q hq]
    have hh := DFunLike.congr_fun hshift (Ideal.Quotient.mk (modulus q) b)
    exact hh
  obtain ⟨a,ha⟩ := trace_dual_integral _ hphase
  have he : residueRepresentative q v = q*a := by
    apply Subtype.ext
    change (residueRepresentative q v : ℂ)=(q : ℂ)*(a : ℂ)
    rw [ha,mul_div_cancel₀ _ (coe_ne_zero hq)]
  apply hv
  rw [← residueRepresentative_spec q v, he, map_mul]
  have hmq : Ideal.Quotient.mk (modulus q) q = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  rw [hmq,zero_mul]

end CubicFirstMoment.HeckeTheta
end

end OAI
