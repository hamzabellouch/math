import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFourierBounds
import OAI.NumberTheory.Ostmann.Characters.PeriodicLinearPhase

namespace OAI

/-! # Multiplying the local correlation bounds over the prime factors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The actual function on the product modulus obtained from local prime functions. -/
noncomputable def primeCRTFunction (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (F : ∀ p : ℕ, ZMod p → ℂ) : ZMod ps.prod → ℂ := by
  cases ps with
  | nil => exact fun _ => 1
  | cons p ps =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let e := ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)
    exact fun x => F p (e x).1 * primeCRTFunction ps hp' hcp.2 F (e x).2

theorem primeCRTFunction_intCast (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (F : ∀ p : ℕ, ZMod p → ℂ) (n : ℤ) :
    primeCRTFunction ps hp hc F (n : ZMod ps.prod) = (ps.map fun p => F p (n : ZMod p)).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    change F p ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1))
      (n : ZMod (p * ps.prod))).1 * primeCRTFunction ps hp' hcp.2 F
        ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1))
          (n : ZMod (p * ps.prod))).2 = _
    rw [map_intCast]
    change F p (n : ZMod p) * primeCRTFunction ps hp' hcp.2 F (n : ZMod ps.prod) = _
    rw [ih hp' hcp.2]
    rfl

/-- Probability-normalized Fourier coefficients multiply under CRT. -/
theorem primeCRTFunction_coefficient_le (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (F : ∀ p : ℕ, ZMod p → ℂ) (A : ℕ → ℝ)
    (hA : ∀ p ∈ ps, 0 ≤ A p)
    (hF : ∀ p (h : p ∈ ps), ∀ u : ZMod p, ‖@additiveFourier p ⟨(hp p h).ne_zero⟩ (F p) u‖ ≤ A p) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    ∀ u, ‖additiveFourier (primeCRTFunction ps hp hc F) u‖ ≤ (ps.map A).prod := by
  induction ps with
  | nil =>
    intro _ u
    change ZMod 1 at u
    change ‖additiveFourier (fun _ : ZMod 1 => (1 : ℂ)) u‖ ≤ 1
    simp [additiveFourier_apply]
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : NeZero p := ⟨(hp p List.mem_cons_self).ne_zero⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    intro _ u
    change ZMod (p * ps.prod) at u
    change ‖additiveFourier (fun x : ZMod (p * ps.prod) =>
      F p ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) x).1 *
      primeCRTFunction ps hp' hcp.2 F
        ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) x).2) u‖ ≤ _
    rw [additiveFourier_crt (m := p) (n := ps.prod), norm_mul]
    exact mul_le_mul (hF p List.mem_cons_self _)
      (ih hp' hcp.2 (fun q hq => hA q (List.mem_cons_of_mem p hq))
        (fun q hq => hF q (List.mem_cons_of_mem p hq)) _)
      (norm_nonneg _) (hA p List.mem_cons_self)

/-- A dyadic interval long compared with the period absorbs the Fourier-grid loss. -/
theorem weighted_periodic_linear_long_bound (q : ℕ) [NeZero q]
    (f : ZMod q → ℂ) (A α : ℝ) (hA : 0 ≤ A)
    (hf : ∀ u, ‖additiveFourier f u‖ ≤ A) (w : ℕ → ℂ) (N : ℕ)
    (hN : (q : ℝ) * (1 + Real.log q) ≤ N) :
    ‖∑ n ∈ Finset.range N, w n * (f (n : ZMod q) * realAdditivePhase α ^ n)‖ ≤
      discreteVariation w N * (4 * A * N) := by
  apply (weighted_periodic_linear_phase_bound q f A α hA hf w N).trans
  apply mul_le_mul_of_nonneg_left _ (by
    unfold discreteVariation
    positivity)
  nlinarith

end Ostmann

end OAI
