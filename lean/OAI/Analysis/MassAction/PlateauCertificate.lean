import OAI.Analysis.MassAction.Model

namespace OAI

universe uLambda

noncomputable section

namespace Problem326

/-- Pairwise comparison formulation of activity in a finite affine family. -/
def AffineActive {d : ℕ} {Λ : Type uLambda}
    (r : Λ → Fin d → ℝ) (c : Λ → ℝ) (x : Fin d → ℝ) (j : Λ) : Prop :=
  ∀ k, dot (r j) x + c j ≤ dot (r k) x + c k

/-- Every finite nonempty affine family has an active label, including at ties. -/
theorem exists_affineActive {d : ℕ} {Λ : Type uLambda} [Fintype Λ] [Nonempty Λ]
    (r : Λ → Fin d → ℝ) (c : Λ → ℝ) (x : Fin d → ℝ) :
    ∃ j, AffineActive r c x j := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ
    (fun k => dot (r k) x + c k) Finset.univ_nonempty
  exact ⟨j, fun k => hj k (Finset.mem_univ k)⟩

/-- Coordinate sign gaps force any initially active slope to vanish. -/
theorem affineActive_slope_eq_zero {d : ℕ} {Λ : Type uLambda}
    (r : Λ → Fin d → ℝ) (c : Λ → ℝ) (x p : Fin d → ℝ) {H : ℝ}
    (hp : ∀ i, |p i| < H)
    (hgap : ∀ j, AffineActive r c x j → ∀ i, r j i ≠ 0 → H ≤ |p i|)
    {j : Λ} (hj : AffineActive r c x j) : r j = 0 := by
  funext i
  by_contra hi
  exact (not_le_of_gt (hp i)) (hgap j hj i hi)

/-- The plateau cut out by a constant active branch contains the initial point.
This also records that plateau membership is exactly activity of that branch. -/
theorem constant_branch_plateau {d : ℕ} {Λ : Type uLambda}
    (r : Λ → Fin d → ℝ) (c : Λ → ℝ) (x₀ : Fin d → ℝ)
    {j : Λ} (hr : r j = 0) (hj : AffineActive r c x₀ j) :
    x₀ ∈ {x | ∀ k, c j ≤ dot (r k) x + c k} ∧
      ∀ x, (∀ k, c j ≤ dot (r k) x + c k) ↔ AffineActive r c x j := by
  have hz : ∀ x : Fin d → ℝ, dot (r j) x = 0 := by
    intro x
    simp [hr, dot]
  constructor
  · intro k
    simpa [hz] using hj k
  · intro x
    simp only [AffineActive, hz, zero_add]

/-- A zero-slope branch cannot be active at an exponent-box boundary point
when the active-label approximation has radius strictly below one there. -/
theorem constant_branch_not_active_on_boundary {d : ℕ} {Λ : Type uLambda}
    (r : Λ → Fin d → ℝ) (c : Λ → ℝ) (X : (Fin d → ℝ) → (Fin d → ℝ))
    (E : (Fin d → ℝ) → ℝ) (hE : E 0 ≤ 1 / 2)
    {j : Λ} (hr : r j = 0) {p : Fin d → ℝ}
    (hboundary : ∃ i, |p i| = 1)
    (happrox : AffineActive r c (X p) j → ∀ i, |p i - r j i| < E (r j)) :
    ¬ AffineActive r c (X p) j := by
  intro hj
  obtain ⟨i, hi⟩ := hboundary
  have h := happrox hj i
  simp only [hr, Pi.zero_apply, sub_zero] at h
  linarith

/-- Combined algebraic certificate used before the geometric trapping step. -/
theorem exists_constant_plateau_certificate {d : ℕ} {Λ : Type uLambda}
    [Fintype Λ] [Nonempty Λ]
    (r : Λ → Fin d → ℝ) (c : Λ → ℝ) (x₀ p₀ : Fin d → ℝ) {H : ℝ}
    (hp₀ : ∀ i, |p₀ i| < H)
    (hgap : ∀ j, AffineActive r c x₀ j → ∀ i, r j i ≠ 0 → H ≤ |p₀ i|) :
    ∃ j : Λ, r j = 0 ∧
      x₀ ∈ {x | ∀ k, c j ≤ dot (r k) x + c k} ∧
      ∀ x, (∀ k, c j ≤ dot (r k) x + c k) ↔ AffineActive r c x j := by
  obtain ⟨j, hj⟩ := exists_affineActive r c x₀
  have hr := affineActive_slope_eq_zero r c x₀ p₀ hp₀ hgap hj
  exact ⟨j, hr, constant_branch_plateau r c x₀ hr hj⟩

end Problem326

end

end OAI
