import OAI.Probability.ClassicalON.PeriodicPartition

namespace OAI

noncomputable section
namespace ClassicalON.LatticeGraph

def thetaPotential (G : LatticeGraph) (k : ℕ) (x : G.vertices) : ℝ :=
  squareTheta (scaledSite k x.val)

def rotatedBoundaryPins (G : LatticeGraph) (k : ℕ) (P : G.vertices → Option (Spin 3))
    (t : ℝ) : G.vertices → Option (Spin 3) :=
  fun x => (P x).map (spinRotation (SpinSystem.potentialRotation (G.thetaPotential k) t x))

theorem thetaPotential_binary_pins (G : LatticeGraph) (k : ℕ)
    (P : G.vertices → Option (Spin 3)) (hP : G.BoundaryPins k 3 P) :
    ∀ x s, P x=some s → G.thetaPotential k x=0 ∨ G.thetaPotential k x=1 := by
  intro x s hs
  rcases hP x s hs with h | h
  · exact Or.inr (squareTheta_one _ h.1 h.2)
  · exact Or.inl (squareTheta_zero _ h)

theorem rotatedBoundaryPins_boundary (G : LatticeGraph) (k : ℕ)
    (P : G.vertices → Option (Spin 3)) (hP : G.BoundaryPins k 3 P) (t : ℝ) :
    G.BoundaryPins k 3 (G.rotatedBoundaryPins k P t) := by
  intro x s hs
  cases hp : P x with
  | none => simp [rotatedBoundaryPins,hp] at hs
  | some u => exact hP x u hp

theorem rotatePotential_spinSystem (G : LatticeGraph) (k : ℕ) (b : G.edges → ℝ)
    (P : G.vertices → Option (Spin 3)) (t : ℝ) :
    (G.spinSystem 3 b P).rotatePotential (G.thetaPotential k) t =
      G.spinSystem 3 b (G.rotatedBoundaryPins k P t) := rfl

theorem annulus_partition_ratio (β : ℝ) (hβ : 0 ≤ β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ, 4 ≤ k ∧ ∀ (G : LatticeGraph), G.WithinDyadicBox k →
      ∀ (b : G.edges → ℝ), (∀ e,0 ≤ b e ∧ b e ≤ β) →
      ∀ (P : G.vertices → Option (Spin 3)), G.BoundaryPins k 3 P → ∀ x y : ℝ,
      1-ε ≤ (G.spinSystem 3 b (G.rotatedBoundaryPins k P x)).Z (fun _ => 1) /
        (G.spinSystem 3 b (G.rotatedBoundaryPins k P y)).Z (fun _ => 1) := by
  let δ := 2*ε/(2*Real.pi)^2
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨k,hk,hR⟩ := annulus_response_small β hβ δ hδ
  refine ⟨k,hk,?_⟩
  intro G hG b hb P hP x y
  have hp := G.thetaPotential_binary_pins k P hP
  have hr (t : ℝ) : -((G.spinSystem 3 b P).rotatePotential (G.thetaPotential k) t).secondAxisResponse
      ((G.spinSystem 3 b P).differential (G.thetaPotential k))
      ((G.spinSystem 3 b P).differential (G.thetaPotential k)) ≤ δ := by
    exact hR G hG b hb (G.rotatedBoundaryPins k P t) (G.rotatedBoundaryPins_boundary k P hP t)
  have h := (G.spinSystem 3 b P).potential_partition_ratio (G.thetaPotential k) δ hδ.le hp hr x y
  have he : δ*(2*Real.pi)^2/2=ε := by dsimp [δ]; field_simp
  rw [he] at h
  exact h

end ClassicalON.LatticeGraph

end

end OAI
