import Mathlib

namespace OAI

namespace Problem340.Register

variable {X E : Type*} [AddCommGroup E] [Module ℝ E]

theorem register_reset_at
    (x0 : X) (embed : E → X) (hembed : embed 0 = x0) (S : X → E)
    (a : ℕ → ℝ) (input : ℕ → E) (v : ℕ → X)
    (hrec : ∀ n, v (n + 1) = embed (a n • S (v n) + input n))
    (k : ℕ) (ha : a k = 0) (hu : input k = 0) : v (k + 1) = x0 := by
  simp [hrec k, ha, hu, hembed]

theorem register_zero_on_interval
    (x0 : X) (embed : E → X) (hembed : embed 0 = x0) (S : X → E) (hS : S x0 = 0)
    (a : ℕ → ℝ) (input : ℕ → E) (v : ℕ → X)
    (hrec : ∀ n, v (n + 1) = embed (a n • S (v n) + input n))
    (s j : ℕ) (hvs : v s = x0)
    (hu : ∀ n, s ≤ n → n < j → input n = 0) :
    ∀ n, s ≤ n → n ≤ j → v n = x0 := by
  intro n hsn
  induction n, hsn using Nat.le_induction with
  | base => exact fun _ => hvs
  | succ n hsn ih =>
      intro hnj
      have hn : n ≤ j := by omega
      have hu' : input n = 0 := hu n hsn (by omega)
      simp [hrec n, ih hn, hS, hu', hembed]

theorem register_zero_after_reset
    (x0 : X) (embed : E → X) (hembed : embed 0 = x0) (S : X → E) (hS : S x0 = 0)
    (a : ℕ → ℝ) (input : ℕ → E) (v : ℕ → X)
    (hrec : ∀ n, v (n + 1) = embed (a n • S (v n) + input n))
    (k : ℕ) (ha : a k = 0) (hu : ∀ n, k ≤ n → input n = 0) :
    ∀ n, k + 1 ≤ n → v n = x0 := by
  have hvk : v (k + 1) = x0 := register_reset_at x0 embed hembed S a input v hrec k ha
    (hu k le_rfl)
  intro n hn
  exact register_zero_on_interval x0 embed hembed S hS a input v hrec (k + 1) n hvk
    (fun i hi _ => hu i (by omega)) n hn le_rfl

theorem register_eventually_zero
    (x0 : X) (embed : E → X) (hembed : embed 0 = x0) (S : X → E) (hS : S x0 = 0)
    (a : ℕ → ℝ) (input : ℕ → E) (v : ℕ → X)
    (hrec : ∀ n, v (n + 1) = embed (a n • S (v n) + input n))
    (hreset : ∀ N : ℕ, ∃ k, N ≤ k ∧ a k = 0)
    (hu : ∀ᶠ n in Filter.atTop, input n = 0) :
    ∀ᶠ n in Filter.atTop, v n = x0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hu
  obtain ⟨k, hNk, hk⟩ := hreset N
  apply Filter.eventually_atTop.mpr
  refine ⟨k + 1, ?_⟩
  exact register_zero_after_reset x0 embed hembed S hS a input v hrec k hk
    (fun n hn => hN n (hNk.trans hn))

theorem registers_eventually_zero {ι : Type*} [Finite ι]
    (x0 : X) (embed : E → X) (hembed : embed 0 = x0) (S : X → E) (hS : S x0 = 0)
    (a : ℕ → ℝ) (input : ℕ → ι → E) (v : ℕ → ι → X)
    (hrec : ∀ n i, v (n + 1) i = embed (a n • S (v n i) + input n i))
    (hreset : ∀ N : ℕ, ∃ k, N ≤ k ∧ a k = 0)
    (hu : ∀ i, ∀ᶠ n in Filter.atTop, input n i = 0) :
    ∀ᶠ n in Filter.atTop, ∀ i, v n i = x0 := by
  apply Filter.eventually_all.mpr
  intro i
  exact register_eventually_zero x0 embed hembed S hS a (fun n => input n i)
    (fun n => v n i) (fun n => hrec n i) hreset (hu i)

end Problem340.Register

end OAI
