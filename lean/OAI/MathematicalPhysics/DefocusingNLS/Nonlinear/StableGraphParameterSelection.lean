import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphCoordinateContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphSelection

namespace OAI

/-! # Continuous parameter selection for the contracting stable graph

Only strong continuity of the linear blocks and coordinate continuity of the
sources are used. The backward inverse is fixed while the starting radius
and initial data vary.
-/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local notation "X" => (ℕ →ᵇ E) × (ℕ →ᵇ F)

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
theorem stableGraph_source_norm_le (N : X → (ℕ →ᵇ E)) (ρ ε : ℝ)
    (hρ : 0 ≤ ρ) (hN : ∀ x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      dist (N x) (N y) ≤ (1 / 16 : ℝ) * dist x y)
    (hN0 : ‖N 0‖ ≤ ε) (x : X) (hx : ‖x‖ ≤ ρ) :
    ‖N x‖ ≤ ρ / 16 + ε := by
  have hh := hN x 0 hx (by simpa using hρ)
  have ht := norm_add_le (N x - N 0) (N 0)
  rw [sub_add_cancel] at ht
  rw [dist_zero_right, dist_eq_norm] at hh
  linarith

theorem exists_continuous_stableGraph_selection
    (A : P → ℕ → E →L[ℝ] E) (B : P → ℕ → F →L[ℝ] E)
    (hA : ∀ p n, ‖A p n‖ ≤ 1 / 8) (hB : ∀ p n, ‖B p n‖ ≤ 1 / 16)
    (hAc : ∀ n, Continuous (fun z : P × E => A z.1 n z.2))
    (hBc : ∀ n, Continuous (fun z : P × F => B z.1 n z.2))
    (R : F →L[ℝ] F) (hR : ‖R‖ ≤ 1) (w : P → E) (hw : Continuous w)
    (N : P → X → (ℕ →ᵇ E)) (H : P → X → (ℕ →ᵇ F))
    (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε)
    (hN : ∀ p x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      dist (N p x) (N p y) ≤ (1 / 16 : ℝ) * dist x y)
    (hH : ∀ p x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      dist (H p x) (H p y) ≤ (1 / 16 : ℝ) * dist x y)
    (hN0 : ∀ p, ‖N p 0‖ ≤ ε) (hH0 : ∀ p, ‖H p 0‖ ≤ ε)
    (hNc : ∀ x : P → X, (∀ p, ‖x p‖ ≤ ρ) →
      (∀ n, Continuous (fun p => (x p).1 n)) →
      (∀ n, Continuous (fun p => (x p).2 n)) →
      ∀ n, Continuous (fun p => N p (x p) n))
    (hHc : ∀ x : P → X, (∀ p, ‖x p‖ ≤ ρ) →
      (∀ n, Continuous (fun p => (x p).1 n)) →
      (∀ n, Continuous (fun p => (x p).2 n)) →
      ∀ n, Continuous (fun p => H p (x p) n))
    (hsmall : ∀ p, ‖w p‖ + 2 * ε ≤ ρ / 2) :
    ∃ z : P → X,
      (∀ p, stableGraphMap (A p) (B p) (hA p) (hB p) R hR (w p) (N p) (H p) (z p) = z p) ∧
      (∀ p, ‖z p‖ ≤ ρ) ∧
      (∀ p, ‖z p‖ ≤ 2 * (‖w p‖ + 2 * ε)) ∧
      (∀ p, (z p).1 0 = w p) ∧
      (∀ n, Continuous (fun p => ((z p).1 n, (z p).2 n))) := by
  classical
  choose z hz hfix hbound _huniq using fun p => exists_stableGraph_fixedPoint
    (A p) (B p) (hA p) (hB p) R hR (w p) (N p) (H p) ρ ε hρ hε
    (hN p) (hH p) (hN0 p) (hH0 p) (hsmall p)
  let T := fun p => stableGraphMap (A p) (B p) (hA p) (hB p) R hR (w p) (N p) (H p)
  have hcontract : ∀ p x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      dist (T p x) (T p y) ≤ (1 / 2 : ℝ) * dist x y := by
    intro p x y hx hy
    exact stableGraphMap_dist_le (A p) (B p) (hA p) (hB p) R hR (w p)
      (N p) (H p) x y (hN p x y hx hy) (hH p x y hx hy)
  have hmap : ∀ p x, ‖x‖ ≤ ρ → ‖T p x‖ ≤ ρ := by
    intro p x hx
    have ht := norm_add_le (T p x - T p 0) (T p 0)
    rw [sub_add_cancel] at ht
    have hc := hcontract p x 0 hx (by simpa using hρ)
    rw [dist_zero_right, dist_eq_norm] at hc
    have hzero := stableGraphMap_zero_bound (A p) (B p) (hA p) (hB p) R hR
      (w p) (N p) (H p) ε hε (hN0 p) (hH0 p)
    change ‖T p 0‖ ≤ _ at hzero
    linarith [hsmall p]
  have hi : ∀ j : ℕ,
      (∀ p, ‖(T p)^[j] 0‖ ≤ ρ) ∧
      (∀ n, Continuous (fun p => ((T p)^[j] 0).1 n)) ∧
      (∀ n, Continuous (fun p => ((T p)^[j] 0).2 n)) := by
    intro j
    induction j with
    | zero =>
        simp only [Function.iterate_zero_apply]
        exact ⟨fun _ => by simpa using hρ, fun _ => continuous_const, fun _ => continuous_const⟩
    | succ j ih =>
        refine ⟨fun p => ?_, fun n => ?_, fun n => ?_⟩
        · rw [Function.iterate_succ_apply']
          exact hmap p _ (ih.1 p)
        · simp only [Function.iterate_succ_apply']
          exact continuous_stableForward_coordinate A B (1 / 8) (1 / 16)
            (by norm_num) (by norm_num) hA hB w
            (fun p => ((T p)^[j] 0).1) (fun p => ((T p)^[j] 0).2)
            (fun p => N p ((T p)^[j] 0)) hw
            (fun n => (hAc n).comp (continuous_id.prodMk (ih.2.1 n)))
            (fun n => (hBc n).comp (continuous_id.prodMk (ih.2.2 n)))
            (hNc _ ih.1 ih.2.1 ih.2.2) n
        · simp only [Function.iterate_succ_apply']
          exact continuous_stableBackward_coordinate R hR (fun p => H p ((T p)^[j] 0))
            (ρ / 16 + ε) (hHc _ ih.1 ih.2.1 ih.2.2)
            (fun p => by
              have hh := hH p ((T p)^[j] 0) 0 (ih.1 p) (by simpa using hρ)
              have ht := norm_add_le (H p ((T p)^[j] 0) - H p 0) (H p 0)
              rw [sub_add_cancel] at ht
              rw [dist_zero_right, dist_eq_norm] at hh
              linarith [ih.1 p, hH0 p]) n
  refine ⟨z, hfix, hz, hbound, ?_, fun n => ?_⟩
  · intro p
    have h := congrArg (fun x : X => x.1 0) (hfix p)
    exact h.symm
  · apply continuous_contraction_observation T z (fun x : X => (x.1 n, x.2 n)) ρ hρ hmap
      hcontract hfix hz
    · intro x y
      exact max_le
        ((BoundedContinuousFunction.dist_coe_le_dist n).trans (le_max_left _ _))
        ((BoundedContinuousFunction.dist_coe_le_dist n).trans (le_max_right _ _))
    · intro j
      exact (hi j).2.1 n |>.prodMk ((hi j).2.2 n)

end DefocusingNLS

end OAI
