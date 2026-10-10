import OAI.NumberTheory.JointDickman.Amplification.CRTMean
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeResidueChannel

namespace OAI

/-! # The actual divisibility-site mean is the independent prime law -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem uniform_zero_bit_mass (p : ℕ) [NeZero p] (b : Bool) :
    finitePushMass (fun _ : ZMod p => (1 : ℝ)/p) (fun a => decide (a = 0)) b =
      bernoulliBitMass (1/(p : ℝ)) b := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  cases b
  · simp [finitePushMass,bernoulliBitMass]
    have he (x : ZMod p) : (if x = 0 then 0 else (p : ℝ)⁻¹) =
        (p : ℝ)⁻¹ - (if x = 0 then (p : ℝ)⁻¹ else 0) := by split_ifs <;> simp
    simp_rw [he]
    rw [sum_sub_distrib]
    simp [hp]
  · simp [finitePushMass,bernoulliBitMass]

theorem uniform_prime_site_mean (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (F : (Q → Bool) → ℝ) :
    (∑ n ∈ range (∏ p : Q, p.val), F (fun p => decide (p.val ∣ n))) /
      (∏ p : Q, (p.val : ℝ)) = ∑ x, fullPrimeMass Q x*F x := by
  let : ∀ p : Q, NeZero p.val := fun p => ⟨(hQ p p.property).ne_zero⟩
  have hcop : Pairwise (fun p q : Q => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hQ p p.property) (hQ q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have hcrt := crt_uniform_mean (fun p : Q => p.val) hcop
    (fun x => F (fun p => decide (x p = 0)))
  have hpush := finiteProductMass_pushforward_test
    (fun p : Q => fun _ : ZMod p.val => (1 : ℝ)/p.val)
    (fun p : Q => fun a : ZMod p.val => decide (a = 0)) (fun x => (F x : ℂ))
  have hlocal : (fun p : Q => finitePushMass
      (fun _ : ZMod p.val => (1 : ℝ)/p.val) (fun a => decide (a = 0))) =
      (fun p : Q => bernoulliBitMass (1/(p.val : ℝ))) := by
    funext p b
    exact uniform_zero_bit_mass p.val b
  rw [hlocal] at hpush
  have hpushR : (∑ x, fullPrimeMass Q x*F x) =
      ∑ x, finiteProductMass (fun p : Q => fun _ : ZMod p.val => (1 : ℝ)/p.val) x *
        F (fun p => decide (x p = 0)) := by
    exact_mod_cast hpush
  rw [hpushR]
  simpa only [ZMod.natCast_eq_zero_iff] using hcrt

theorem prime_site_average_tendsto (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (F : (Q → Bool) → ℝ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, F (fun p => decide (p.val ∣ n)))/(N : ℝ))
      atTop (𝓝 (∑ x, fullPrimeMass Q x*F x)) := by
  let : ∀ p : Q, NeZero p.val := fun p => ⟨(hQ p p.property).ne_zero⟩
  let : NeZero (∏ p : Q, p.val) := ⟨prod_ne_zero_iff.mpr (fun p _ => NeZero.ne p.val)⟩
  have hcop : Pairwise (fun p q : Q => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hQ p p.property) (hQ q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  let e := ZMod.prodEquivPi (fun p : Q => p.val) hcop
  let f : ZMod (∏ p : Q, p.val) → ℂ := fun a => (F (fun p => decide (e a p = 0)) : ℂ)
  have he (n : ℕ) : e (n : ZMod (∏ p : Q, p.val)) = (n : ∀ p : Q, ZMod p.val) := map_natCast e n
  have hm : residueMean f = (∑ x, fullPrimeMass Q x*F x : ℝ) := by
    rw [residueMean,residue_sum_eq_range]
    dsimp only [f]
    simp only [he,Pi.natCast_apply,ZMod.natCast_eq_zero_iff]
    have hh := uniform_prime_site_mean Q hQ F
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hh
    push_cast at hc
    simpa only [Nat.cast_prod,Complex.ofReal_sum,Complex.ofReal_mul] using hc
  have ht := (Complex.continuous_re.tendsto _).comp (periodicAverage_tendsto f)
  rw [hm] at ht
  change Tendsto (fun N => (periodicAverage f N).re) atTop _ at ht
  simpa only [periodicAverage,f,he,Pi.natCast_apply,ZMod.natCast_eq_zero_iff,
    ← Complex.ofReal_sum,← Complex.ofReal_natCast,← Complex.ofReal_div,Complex.ofReal_re,
    Function.comp_apply] using ht

end JointDickman

end OAI
