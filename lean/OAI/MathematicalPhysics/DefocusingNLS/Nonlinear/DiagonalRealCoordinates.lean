import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteSymmetryBackward
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteInvariantInverse

namespace OAI

/-! # Real coordinate images inside the diagonal symmetry coordinates -/

namespace DefocusingNLS

variable {H V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def diagonalRealCoordinates (π : H →L[ℝ] V) (G : V →L[ℂ] V)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2) : H →L[ℝ] SymmetryCoordinates G :=
  ((symmetryCoordinateEquiv G hspan hspec).symm.toContinuousLinearMap.restrictScalars ℝ).comp π

theorem diagonalRealCoordinates_zero_iff (π : H →L[ℝ] V) (G : V →L[ℂ] V)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2) (u : H) :
    diagonalRealCoordinates π G hspan hspec u = 0 ↔ π u = 0 := by
  change (symmetryCoordinateEquiv G hspan hspec).symm (π u) = 0 ↔ π u = 0
  exact (symmetryCoordinateEquiv G hspan hspec).symm.map_eq_zero_iff

theorem diagonalRealCoordinates_step (π : H →L[ℝ] V) (G : V →L[ℂ] V)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2)
    (S : H →L[ℝ] H) (t : ℝ)
    (hπ : ∀ u, π (S u) = NormedSpace.exp (t • G) (π u)) (u : H) :
    diagonalRealCoordinates π G hspan hspec (S u) =
      symmetryCoordinateEvolution G t (diagonalRealCoordinates π G hspan hspec u) := by
  let e := symmetryCoordinateEquiv G hspan hspec
  apply e.injective
  change e (e.symm (π (S u))) = e (symmetryCoordinateEvolution G t (e.symm (π u)))
  rw [e.apply_symm_apply, hπ u]
  have he := symmetryCoordinateEvolution_intertwines G t (e.symm (π u))
  change NormedSpace.exp (t • G) (e (e.symm (π u))) =
    e (symmetryCoordinateEvolution G t (e.symm (π u))) at he
  simpa only [e.apply_symm_apply] using he

theorem diagonalRealCoordinates_range_inverse (π : H →L[ℝ] V) (G : V →L[ℂ] V)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2)
    (S : H →L[ℝ] H) (t : ℝ) (ht : 0 ≤ t)
    (hπ : ∀ u, π (S u) = NormedSpace.exp (t • G) (π u)) :
    let c := diagonalRealCoordinates π G hspan hspec
    ∃ D R : c.range →L[ℝ] c.range,
      (∀ v : c.range, (D v : SymmetryCoordinates G) = symmetryCoordinateEvolution G t v) ∧
      (∀ v : c.range, (R v : SymmetryCoordinates G) = symmetryCoordinateEvolution G (-t) v) ∧
      (∀ v, D (R v) = v) ∧ ‖R‖ ≤ 1 ∧
      (∀ u, D (c.rangeRestrict u) = c.rangeRestrict (S u)) := by
  intro c
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  have hd : ∀ v ∈ c.range, symmetryCoordinateEvolution G t v ∈ c.range := by
    rintro v ⟨u, rfl⟩
    exact ⟨S u, diagonalRealCoordinates_step π G hspan hspec S t hπ u⟩
  obtain ⟨D, R, hD, hR, hDR, hRn⟩ := finite_subspace_contracting_inverse c.range
    ((symmetryCoordinateEvolution G t).restrictScalars ℝ)
    ((symmetryCoordinateEvolution G (-t)).restrictScalars ℝ)
    (fun v => by
      change symmetryCoordinateEvolution G (-t) (symmetryCoordinateEvolution G t v) = v
      simpa only [neg_neg] using symmetryCoordinateEvolution_inverse G (-t) v)
    (symmetryCoordinateEvolution_inverse G t) hd
    (by simpa only [ContinuousLinearMap.norm_restrictScalars] using
      symmetryCoordinateEvolution_backward_norm G t ht)
  refine ⟨D, R, hD, hR, hDR, hRn, fun u => Subtype.ext ?_⟩
  rw [hD]
  exact (diagonalRealCoordinates_step π G hspan hspec S t hπ u).symm

theorem diagonalRealCoordinates_has_inverse (π : H →L[ℝ] V) (G : V →L[ℂ] V)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v →
      lam = 0 ∨ lam = 1 ∨ lam = 1 / 2)
    (S : H →L[ℝ] H) (t : ℝ) (ht : 0 ≤ t)
    (hπ : ∀ u, π (S u) = NormedSpace.exp (t • G) (π u)) :
    HasContractingCoordinateInverse (diagonalRealCoordinates π G hspan hspec) S := by
  obtain ⟨D, R, _, _, hDR, hR, hD⟩ :=
    diagonalRealCoordinates_range_inverse π G hspan hspec S t ht hπ
  exact ⟨D, R, hDR, hR, fun u => (hD u).symm⟩

end DefocusingNLS

end OAI
