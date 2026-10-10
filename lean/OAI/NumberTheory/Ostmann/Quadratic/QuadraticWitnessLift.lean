import OAI.NumberTheory.Ostmann.QuadraticCenter.DivisorQuadraticWitness

namespace OAI

/-! # An actual small-kernel witness supplies the simultaneous integer lift -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_quadratic_witness_lift (B : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hB : 3 ≤ B) (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
      (k : ℕ) (e : Fin k ↪ P) (t : ℕ → ℤ) (tM : ℤ) (h₀ : ℕ) (X : ℝ),
      0 < X → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      Real.exp (10 * T) ≤ (primeTupleProduct P e : ℝ) / X →
      (primeTupleProduct P e : ℝ) / X ≤ Real.exp (14 * T) →
      (∀ i, ((e i).1 : ℤ) ∣ tM - t (e i).1) →
      (∃ U V : Finset ℕ, U ⊆ Q ∧ V ⊆ Q ∧ ∃ s : ℕ, 0 < s ∧ s ≤ Q.toList.prod ^ 4 ∧
        (Real.sqrt 2) ^ U.card * Real.exp (-(Q.card : ℝ)) <
          ‖primeDivisorPositive Q hQ D
            (divisorQuadraticScalar (quadraticInverseResidue (primeTupleProduct P e)) V)
            (fun _ => (h₀ : ℝ) + (tM : ℝ) / primeTupleProduct P e) Φ
            ((primeTupleProduct P e : ℝ) / X) V.toList.prod U s‖) →
      ∃ a ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊, ∃ n : ℤ,
        |(n : ℝ)| ≤ X * Real.exp (13 * T / 100) ∧
        ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1 := by
  filter_upwards [eventual_primeDivisorPositive_phase_witness B Φ hB hΦ] with T hw
  intro Q hQ D P hP k e t tM h₀ X hX hL hK hRlo hRhi ht hW
  obtain ⟨U, V, hU, hV, s, hs, hsL, hwitness⟩ := hW
  obtain ⟨a, ha, b, hab⟩ := hw Q hQ D U V (primeTupleProduct P e) h₀ s
    ((tM : ℝ) / primeTupleProduct P e) ((primeTupleProduct P e : ℝ) / X) Q.card
    hU hV hs hsL hL (Nat.cast_nonneg _) hK hRlo hRhi hwitness
  let n := approximationLift a (primeTupleProduct P e) tM b
  have hM := primeTupleProduct_pos P hP e
  have hMR : (0 : ℝ) < primeTupleProduct P e := by exact_mod_cast hM
  refine ⟨a, ha, n, ?_, ?_⟩
  · apply (approximationLift_abs_bound a (primeTupleProduct P e) hM tM b _ hab).trans
    apply le_of_eq
    field_simp
  · intro i
    exact approximationLift_congruence a (primeTupleProduct P e) (e i).1 tM b (t (e i).1)
      (Finset.dvd_prod_of_mem (fun j : Fin k => (e j).1) (Finset.mem_univ i)) (ht i)

end Ostmann

end OAI
