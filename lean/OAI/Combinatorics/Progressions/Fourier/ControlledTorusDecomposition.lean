import OAI.Combinatorics.Progressions.Estimates.UniformCommutingCircleDecomposition

namespace OAI

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X : Type*} [PseudoMetricSpace X] {d : ℕ}
  [AddAction (Fin d → Circle) X] [ContinuousVAdd (Fin d → Circle) X]

theorem exists_controlled_torus_decomposition
    (hact : ∀ t : Fin d → Circle, Isometry (fun x : X => t +ᵥ x))
    (f : X → ℂ) (L B D : ℝ≥0) (hf : LipschitzWith L f) (hb : ∀ x, ‖f x‖ ≤ B)
    (horbit : ∀ (i : Fin d) (t : Circle) (x : X),
      dist ((Pi.single i t : Fin d → Circle) +ᵥ x) x ≤ D * ‖t‖)
    (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hLp : (L : ℝ) ≤ Real.exp p) (hDp : (D : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (ν : J → Fin d → ℤ) (v : J → X → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ j i, (|ν j i| : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      (∀ j, LipschitzWith L (v j) ∧ (∀ x, ‖v j x‖ ≤ B)) ∧
      (∀ j (t : Fin d → Circle) x,
        v j (t +ᵥ x) = (∏ i, character (ν j i • t i)) * v j x) ∧
      (∀ (a : Fin d → Circle) (z : ℂ), (∀ x, f (a +ᵥ x) = z * f x) →
        ∀ j x, v j (a +ᵥ x) = z * v j x) ∧
      ∀ x, ‖(∑ j, v j x) - f x‖ ≤ δ := by
  classical
  let A : Fin d → IsometricCircleAction X := torusCoordinateAction hact
  let is := List.finRange d
  have hd' : (is.length : ℝ) ≤ p := by simpa [is] using hd
  obtain ⟨N, _, _, hcard, hprops, herr⟩ := exists_controlled_finite_circle_decomposition A is
    (fun i _ j _ => torusCoordinateAction_commutes hact i j) f L B D hf hb
    (fun i _ t x => horbit i t x) δ p hδ hp hd' hLp hDp hδp
  have hcover : ∀ i : Fin d, ∃ r : Fin is.length, is.get r = i := by
    intro i
    apply List.mem_iff_get.mp
    simp [is]
  choose index hindex using hcover
  let J := Fin is.length → FejerChoice N
  let ν : J → Fin d → ℤ := fun k i => -(k (index i) : ℤ)
  let v : J → X → ℂ := fun k => iteratedCircleComponent N A is (fun r => (k r : ℤ)) f
  refine ⟨J, inferInstance, ν, v, hcard, ?_, ?_, ?_, ?_, herr⟩
  · intro k i
    simpa only [ν, Int.cast_neg, abs_neg] using (hprops k).1 (index i)
  · intro k
    exact ⟨(hprops k).2.1, (hprops k).2.2.1⟩
  · intro k t x
    apply torus_character_of_coordinate_characters (v k) (ν k) ?_ t x
    intro i u y
    have hi := (hprops k).2.2.2 (index i) u y
    rw [hindex i] at hi
    exact hi
  · intro a z ha k x
    apply iteratedCircleComponent_equivariant N A is (fun r => (k r : ℤ))
      (fun y => a +ᵥ y) z ?_ ha x
    intro i _ t y
    change (Pi.single i t : Fin d → Circle) +ᵥ (a +ᵥ y) =
      a +ᵥ ((Pi.single i t : Fin d → Circle) +ᵥ y)
    rw [← add_vadd, ← add_vadd, add_comm]

end Erdos3.CircleFourier

end

end OAI
