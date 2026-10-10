import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplificationWeight

namespace OAI

/-! # The positive periodic amplification has mean one -/

namespace Ostmann

open scoped BigOperators

theorem primeCRTFunction_mean_one (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (F : ∀ p : ℕ, ZMod p → ℂ)
    (hF : ∀ p (h : p ∈ ps), @additiveFourier p ⟨(hp p h).ne_zero⟩ (F p) 0 = 1) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    additiveFourier (primeCRTFunction ps hp hc F) 0 = 1 := by
  induction ps with
  | nil =>
    intro _
    change @additiveFourier 1 _ (fun _ => 1) 0 = 1
    simp [additiveFourier_apply]
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : NeZero p := ⟨(hp p List.mem_cons_self).ne_zero⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    change additiveFourier (fun x : ZMod (p * ps.prod) =>
      F p ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) x).1 *
      primeCRTFunction ps hp' hcp.2 F
        ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) x).2) 0 = 1
    rw [additiveFourier_crt (m := p) (n := ps.prod)]
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero, mul_zero]
    rw [hF p List.mem_cons_self,
      ih hp' hcp.2 (fun q hq => hF q (List.mem_cons_of_mem p hq)), mul_one]

noncomputable def amplificationCRT (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) : ZMod Q.toList.prod → ℂ :=
  primeCRTFunction Q.toList (primeSet_list_prime Q hQ) (primeSet_list_coprime Q hQ)
    (fun p x => 1 + (1 / 16 : ℂ) * (centeredDensity (D p) x : ℂ))

theorem amplificationCRT_intCast (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) :
    amplificationCRT Q hQ D (n : ZMod Q.toList.prod) = (amplificationWeight Q D n : ℂ) := by
  rw [amplificationCRT, primeCRTFunction_intCast, amplificationWeight]
  push_cast
  simp

theorem amplificationCRT_mean_one (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) :
    let : NeZero Q.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime Q hQ)).ne'⟩
    additiveFourier (amplificationCRT Q hQ D) 0 = 1 := by
  apply primeCRTFunction_mean_one
  intro p hp
  let : NeZero p := ⟨(primeSet_list_prime Q hQ p hp).ne_zero⟩
  have hsum : (∑ x : ZMod p, (centeredDensity (D p) x : ℂ)) = 0 := by
    rw [← Complex.ofReal_sum, centeredDensity_sum, Complex.ofReal_zero]
  rw [additiveFourier_apply]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one,
    Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast (primeSet_list_prime Q hQ p hp).ne_zero)

end Ostmann

end OAI
