import OAI.Geometry.HeilbronnTriangle.LiftingProbability
import OAI.Geometry.HeilbronnTriangle.DeterminantResidue
import OAI.Geometry.HeilbronnTriangle.BadTripleAverage
import OAI.Geometry.HeilbronnTriangle.DigitObstruction

namespace OAI


namespace Problem355.LiftingProbability

open Finset

noncomputable section

 theorem auxiliaryWeight_nonneg {Ω B : Type*} [Fintype Ω]
    (q s : ℕ) (w : Ω → ℝ) (V : Ω → Finset B)
    (hw : ∀ ω, 0 ≤ w ω) (b : Fin 3 → B) :
    0 ≤ auxiliaryWeight q s w V b := by
  unfold auxiliaryWeight
  exact mul_nonneg (by positivity) (inclusionMass_nonneg w V hw b)

theorem lifted_small_event_eq_zero
    {X A Ω B : Type*} [DecidableEq X] [Fintype Ω]
    (f : X → A) (g : X → (Fin 3 → B)) (d : X → ℤ)
    (O : Finset A) (w : Ω → ℝ) (V : Ω → Finset B)
    (s M : ℕ) (S : Finset X) (τ : ℤ)
    (hlarge : ∀ x ∈ S, f x ∈ O → τ < |d x|) :
    (∑ x ∈ S.filter (fun x => |d x| ≤ τ), liftedMass f g O w V s M x) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x hx
  have hxS := (Finset.mem_filter.mp hx).1
  have hxτ := (Finset.mem_filter.mp hx).2
  have hnot : f x ∉ O := fun hf => (not_lt_of_ge hxτ) (hlarge x hxS hf)
  simp [liftedMass, residueMass, mainMass, hnot]

theorem lifted_small_event_eq_zero_of_polynomial
    {X A Ω B : Type*} [DecidableEq X] [Fintype Ω]
    (f : X → A) (g : X → (Fin 3 → B)) (d : X → ℤ)
    (O : Finset A) (w : Ω → ℝ) (V : Ω → Finset B)
    (s M : ℕ) (S : Finset X) (τ : ℤ)
    (p : Polynomial ℤ) (base : ℤ) (hbase : 2 ≤ base) (k : ℕ)
    (hcoeff : ∀ i ≤ k, 50 * |p.coeff i| ≤ 3 * (base - 1))
    (hk : p.coeff k ≠ 0) (hτ : τ ≤ base ^ k / 2)
    (hres : ∀ x ∈ S, f x ∈ O → d x ≡ p.eval base [ZMOD base ^ (k + 1)]) :
    (∑ x ∈ S.filter (fun x => |d x| ≤ τ), liftedMass f g O w V s M x) = 0 := by
  apply lifted_small_event_eq_zero f g d O w V s M S τ
  intro x hx hf
  exact lt_of_le_of_lt hτ
    (DigitEncoding.polynomial_obstruction p base hbase k hcoeff hk (hres x hx hf))

theorem lifted_small_event_le
    {X A Ω B : Type*} [DecidableEq X] [DecidableEq A] [Fintype Ω]
    (f : X → A) (g : X → (Fin 3 → B)) (d : X → ℤ)
    (O : Finset A) (hO : O.Nonempty) (w : Ω → ℝ) (V : Ω → Finset B)
    (s h q L : ℕ) (hs : 0 < s) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L)
    (hw : ∀ ω, 0 ≤ w ω) (S : Finset X)
    {τ : ℤ} (hwidth : 2 * τ < h) (c : ZMod h)
    (hres : ∀ x ∈ S, f x ∈ O → (d x : ZMod h) = c)
    {D E c₀ C R : ℝ} (hD : 0 < D) (hE : 0 < E) (hc₀ : 0 < c₀) (hC : 0 ≤ C)
    (horbit : c₀ * (h : ℝ) ^ 8 / (D ^ 3 * E ^ 2) ≤ (O.card : ℝ))
    (hcount : ∀ t : ℤ, |t| ≤ τ →
      (∑ x ∈ (S.filter (fun x => f x ∈ O)).filter (fun x => d x = t),
        auxiliaryWeight q s w V (g x)) ≤
          C * R ^ 2 * ((L * (h * q) : ℕ) : ℝ) ^ 6 / (D ^ 2 * E ^ 2)) :
    (∑ x ∈ S.filter (fun x => |d x| ≤ τ), liftedMass f g O w V s (L ^ 9) x) ≤
      (C / c₀) * R ^ 2 * (h : ℝ) * D / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
  classical
  rw [exact_lifting_identity f g O hO w V s h q L hs hh hq hL]
  rw [Finset.filter_comm]
  apply Sampling.lifting_weighted_count_bound
  · exact_mod_cast hh
  · exact_mod_cast (Nat.mul_pos hL (Nat.mul_pos hh hq))
  · exact hD
  · exact hE
  · exact_mod_cast Finset.card_pos.mpr hO
  · exact hc₀
  · exact Finset.sum_nonneg fun x hx => auxiliaryWeight_nonneg q s w V hw (g x)
  · exact horbit
  · apply DeterminantResidue.sum_small_le_of_fiber_bound
      (S.filter (fun x => f x ∈ O)) d (fun x => auxiliaryWeight q s w V (g x))
      hwidth c
    · intro x hx
      exact hres x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
    · positivity
    · exact hcount

end
end Problem355.LiftingProbability

end OAI
