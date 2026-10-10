import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveConductor
import OAI.NumberTheory.CubicGram.PeriodicPoisson
import Mathlib.NumberTheory.GaussSum

namespace OAI

/-! The perfect codifferent pairing on every Eisenstein residue ring.
Unlike the trace pairing without the different, this includes ramified moduli. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

private lemma fourierChar_eq_one_integer {t : ℝ} :
    (Real.fourierChar t : ℂ) = 1 ↔ ∃ n : ℤ, t = n := by
  rw [Real.fourierChar_apply, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, Complex.ofReal_injective ?_⟩
    apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
    convert hn using 1
    push_cast
    ring
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    push_cast
    ring

/-- The integral dual of the trace lattice is the inverse different. -/
lemma residue_trace_dual_lattice (z : ℂ)
    (h : ∀ n : Eisenstein, ∃ k : ℤ,
      tracePair (n : ℂ) (z / traceLambda) = k) :
    ∃ a : Eisenstein, (a : ℂ) = z := by
  obtain ⟨n, hn⟩ := h 1
  obtain ⟨k, hk⟩ := h omegaE
  have htrace (w : ℂ) : w + star w = (2 * w.re : ℝ) := by
    apply Complex.ext <;> simp [two_mul]
  have hn' : z / traceLambda + star (z / traceLambda) = n := by
    rw [htrace]
    have hnR : 2 * (z / traceLambda).re = (n : ℝ) := by
      simpa only [tracePair, Subalgebra.coe_one, one_mul] using hn
    exact_mod_cast hnR
  have hk' : omega * (z / traceLambda) + star (omega * (z / traceLambda)) = k := by
    rw [htrace]
    have hkR : 2 * (omega * (z / traceLambda)).re = (k : ℝ) := by
      simpa only [tracePair, omegaE] using hk
    exact_mod_cast hkR
  have ht := trace_pair_lattice hn' hk'
  field_simp [traceLambda_ne_zero] at ht
  refine ⟨ofCoords (n + k) n, ?_⟩
  rw [ofCoords_coe]
  dsimp only [traceLambda] at ht
  push_cast at ht ⊢
  linear_combination -(1/3 : ℂ) * ht +
    ((2*(n:ℂ)+4*(k:ℂ))/3) * omega_quadratic

/-- Canonical primitive additive character modulo any nonzero Eisenstein integer. -/
def residueFourierChar (q : Eisenstein) (hq : q ≠ 0) : AddChar (Residues q) ℂ where
  toFun a := Real.fourierChar (tracePair (residueRepresentative q a : ℂ)
    (1 / ((q : ℂ) * traceLambda)))
  map_zero_eq_one' := by
    have he := tracePhase_congr hq 1 (show
      Ideal.Quotient.mk (modulus q) (residueRepresentative q 0) =
        Ideal.Quotient.mk (modulus q) 0 by rw [residueRepresentative_spec, map_zero])
    simp only [Subalgebra.coe_one] at he
    rw [he]
    simp [tracePair]
  map_add_eq_mul' a b := by
    have he := tracePhase_congr hq 1 (show
      Ideal.Quotient.mk (modulus q) (residueRepresentative q (a+b)) =
        Ideal.Quotient.mk (modulus q) (residueRepresentative q a + residueRepresentative q b)
        by rw [map_add, residueRepresentative_spec, residueRepresentative_spec,
          residueRepresentative_spec])
    simp only [Subalgebra.coe_one] at he
    rw [he]
    simp only [Subalgebra.coe_add, tracePair_add_left, AddChar.map_add_eq_mul,
      Circle.coe_mul]

@[simp] lemma residueFourierChar_mk (q : Eisenstein) (hq : q ≠ 0) (a : Eisenstein) :
    residueFourierChar q hq (Ideal.Quotient.mk (modulus q) a) =
      (Real.fourierChar (tracePair (a : ℂ) (1 / ((q : ℂ) * traceLambda))) : ℂ) := by
  exact tracePhase_congr hq 1 (residueRepresentative_spec _ _)

lemma residueFourierChar_isPrimitive (q : Eisenstein) (hq : q ≠ 0) :
    (residueFourierChar q hq).IsPrimitive := by
  intro a ha hshift
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hall (n : Eisenstein) :
      (Real.fourierChar (tracePair (n : ℂ) (((r : ℂ)/(q : ℂ))/traceLambda)) : ℂ) = 1 := by
    have he := congrArg (fun ψ : AddChar (Residues q) ℂ =>
      ψ (Ideal.Quotient.mk (modulus q) n)) hshift
    simp only [AddChar.mulShift_apply, ← map_mul, residueFourierChar_mk,
      AddChar.one_apply] at he
    convert he using 1
    congr 2
    unfold tracePair
    congr 2
    push_cast
    ring
  obtain ⟨b, hb⟩ := residue_trace_dual_lattice ((r : ℂ)/(q : ℂ))
    (fun n => fourierChar_eq_one_integer.mp (hall n))
  have hqC : (q : ℂ) ≠ 0 := fun he => hq (Subtype.ext he)
  have hr : r = q*b := by
    apply Subtype.ext
    push_cast
    rw [hb]
    field_simp
  apply ha
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton.mpr ⟨b, hr⟩

/-- The finite Fourier transform of the actual residue multiplicative character. -/
def residueCharacterFourier (q : Eisenstein) (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ) (a : Residues q) : ℂ :=
  gaussSum χ ((residueFourierChar q hq).mulShift a)

/-- Unit frequencies satisfy the exact Gauss eigenrelation for every modulus. -/
lemma residueCharacterFourier_unit (q : Eisenstein) (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ) (a : (Residues q)ˣ) :
    residueCharacterFourier q hq χ a =
      (star χ) a * gaussSum χ (residueFourierChar q hq) := by
  unfold residueCharacterFourier
  rw [gaussSum_mulShift_eq]
  rw [MulChar.star_eq_inv]

end CubicFirstMoment

end

end OAI
