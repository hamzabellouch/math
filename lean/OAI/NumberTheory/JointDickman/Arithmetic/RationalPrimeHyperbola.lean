import OAI.NumberTheory.JointDickman.Arithmetic.PrimeHyperbolaDeletion

namespace OAI

/-! # The full rational prime bilinear sum -/
namespace JointDickman
open Finset

lemma prime_phase_coefficient_bound (b c : ℕ → ℂ) (θ : ℝ)
    (hb : ∀ p, p.Prime → ‖b p‖ ≤ Real.log p) (hc : ∀ m, ‖c m‖ ≤ 1)
    (p m : ℕ) (hp : p.Prime) :
    ‖b p*c m*additivePhase (θ*p*m)‖ ≤ Real.log p := by
  rw [norm_mul,norm_mul,norm_additivePhase,mul_one]
  exact (mul_le_mul_of_nonneg_left (hc m) (norm_nonneg _)).trans (by simpa using hb p hp)

theorem full_prime_hyperbola_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (b c : ℕ → ℂ) (N Z H q a : ℕ),
    0 < N → 0 < Z → Z ≤ N → 0 < H → 0 < q → a.Coprime q →
    (∀ p, p.Prime → ‖b p‖ ≤ Real.log p) → (∀ m, ‖c m‖ ≤ 1) →
    ‖∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p),
      b p*c m*additivePhase ((a:ℝ)/q*p*m)‖ ≤
      2*N*Real.log 4*(1+Real.log Z) +
      (1+Real.log N/Real.log 2)*(N:ℝ)*
        (Real.log 4*(2/(H:ℝ)+2/(Z:ℝ)) + H*Real.sqrt
          (C*rationalHyperbolaBudget N Z (Real.log (2*(N:ℝ))) q)) := by
  obtain ⟨C,hC,htail⟩ := truncated_prime_hyperbola_bound
  refine ⟨C,hC,?_⟩
  intro b c N Z H q a hN hZ hZN hH hq ha hb hc
  let G := fun p m : ℕ => b p*c m*additivePhase ((a:ℝ)/q*p*m)
  have hp : ‖∑ p ∈ Nat.primesLE Z, ∑ m ∈ Ioc 0 (N/p), G p m‖ ≤
      N*Real.log 4*(1+Real.log Z) := by
    apply small_prime_bilinear_norm_le
    intro p hp m hm
    exact prime_phase_coefficient_bound b c _ hb hc p m (Nat.mem_primesLE.mp hp).2
  have hm : ‖∑ m ∈ Ioc 0 Z, ∑ p ∈ Nat.primesLE (N/m), if Z<p then G p m else 0‖ ≤
      N*Real.log 4*(1+Real.log Z) := by
    apply small_integer_bilinear_norm_le (fun p m => if Z<p then G p m else 0)
    intro m hm p hp
    split_ifs
    · exact prime_phase_coefficient_bound b c _ hb hc p m (Nat.mem_primesLE.mp hp).2
    · simpa only [norm_zero] using Real.log_natCast_nonneg p
  have he := prime_hyperbola_split G N Z hZN hZ
  change ‖∑ p ∈ Nat.primesLE N, ∑ m ∈ Ioc 0 (N/p), G p m‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  have ht := htail b c N Z H q a hN hZ hH hq ha hb hc
  change ‖∑ p ∈ (Nat.primesLE (N/Z)).filter (fun p => Z<p), ∑ m ∈ Ioc Z (N/p), G p m‖ ≤ _ at ht
  have hsum := add_le_add (add_le_add hp hm) ht
  convert hsum using 1
  ring

end JointDickman

end OAI
