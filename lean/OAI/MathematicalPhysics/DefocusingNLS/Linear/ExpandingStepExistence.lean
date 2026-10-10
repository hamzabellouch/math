import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPerturbationExistence

namespace OAI

/-! # A uniform small-data radius for a fixed nonlinear step

Both the initial perturbation and the profile forcing may be chosen in a
single ball independent of the expanding torus radius. The resulting path
bound is linear in their sizes.
-/

open Set

namespace DefocusingNLS

theorem exists_expandingPerturbation_step_radius (a b k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hM : 0 ≤ M)
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧ A * δ ≤ 1 / 4 ∧
      ∀ (L : ℝ) (hL : 1 ≤ L) (q g : C(Icc (0 : ℝ) M, FourierL2)) (G : ℝ),
      0 ≤ G → G ≤ δ → (∀ t, ‖q t‖ ≤ R) → (∀ t, ‖g t‖ ≤ G) →
      ∀ v₀ : FourierL2, ‖v₀‖ ≤ δ →
      ∃ v : C(Icc (0 : ℝ) M, FourierL2),
        v = expandingPicard a b k L M ha hk hL hM
          (expandingPerturbationReaction a k L M ha ha1 hk hL m q g) v₀ v ∧
        ‖v‖ ≤ A * (‖v₀‖ + G) ∧ ‖v‖ ≤ 1 / 2 := by
  obtain ⟨K, hK, hexists⟩ := exists_expandingPerturbation_finiteSlab a b k ha ha1 hk m R hR
  let η := K + 1
  have hη : 0 < η := by dsimp [η]; linarith
  have hη1 : 1 ≤ η := by dsimp [η]; linarith
  let E := Real.exp (η * M)
  have hE : 0 < E := Real.exp_pos _
  let δ := Real.exp (-η * M) / (4 * η)
  let A := E * η
  have hδ : 0 < δ := div_pos (Real.exp_pos _) (by positivity)
  have hA : 0 < A := mul_pos hE hη
  have hcancel : E * Real.exp (-η * M) = 1 := by
    dsimp [E]
    rw [← Real.exp_add, show η * M + -η * M = 0 by ring, Real.exp_zero]
  have hAδ : A * δ = 1 / 4 := by
    dsimp [A, δ]
    calc
      E * η * (Real.exp (-η * M) / (4 * η)) =
          (E * Real.exp (-η * M)) / 4 := by field_simp [hη.ne']
      _ = 1 / 4 := by rw [hcancel]
  have hδid : 2 * η * δ = Real.exp (-η * M) / 2 := by
    dsimp [δ]
    field_simp [hη.ne']
    ring
  refine ⟨δ, A, hδ, hA, hAδ.le, ?_⟩
  intro L hL q g G hG hGδ hq hg v₀ hv₀
  have hsmall : η * ‖v₀‖ + G ≤ Real.exp (-η * M) := by
    calc
      η * ‖v₀‖ + G ≤ η * δ + δ := add_le_add
        (mul_le_mul_of_nonneg_left hv₀ hη.le) hGδ
      _ ≤ 2 * η * δ := by nlinarith [mul_le_mul_of_nonneg_right hη1 hδ.le]
      _ = Real.exp (-η * M) / 2 := hδid
      _ ≤ Real.exp (-η * M) := by linarith [Real.exp_pos (-η * M)]
  obtain ⟨v, hv, hvbound, _⟩ := hexists L M hL hM q g v₀ G hG hq hg hsmall
  have hlinear : ‖v‖ ≤ A * (‖v₀‖ + G) := by
    apply hvbound.trans
    change E * (η * ‖v₀‖ + G) ≤ E * η * (‖v₀‖ + G)
    nlinarith [mul_nonneg (mul_nonneg hE.le (sub_nonneg.mpr hη1)) hG]
  have hhalf : ‖v‖ ≤ 1 / 2 := by
    calc
      ‖v‖ ≤ A * (‖v₀‖ + G) := hlinear
      _ ≤ A * (δ + δ) := mul_le_mul_of_nonneg_left (add_le_add hv₀ hGδ) hA.le
      _ = 1 / 2 := by nlinarith [hAδ]
  exact ⟨v, hv, hlinear, hhalf⟩

end DefocusingNLS

end OAI
