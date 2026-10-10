import OAI.Geometry.EinsteinFour.DirichletVectorSequence

namespace OAI

/-! Positive discrete Dirichlet forms have nonsingular Jacobi endpoints. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem jacobi_endpoint_isUnit_of_dirichlet_posDef
    (D Y : ℕ → NormalMatrix) (N : ℕ)
    (h0 : Y 0 = 0) (h1 : Y 1 = 1)
    (hrec : ∀ i, Y (i + 2) = D i * Y (i + 1) - Y i)
    (hpos : (dirichletMatrix (fun i : Fin N => D i.val)).PosDef) :
    IsUnit (Y (N + 1)) := by
  have hker (v : Fin 3 → ℝ) (hv : Y (N + 1) *ᵥ v = 0) : v = 0 := by
    by_cases hN : N = 0
    · simpa [hN, h1] using hv
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let z : ℕ → Fin 3 → ℝ := fun i => Y i *ᵥ v
    let x : Fin 3 × Fin N → ℝ := fun p => z (p.2.val + 1) p.1
    have hz0 : z 0 = 0 := by simp [z,h0]
    have hzN : z (N + 1) = 0 := hv
    have hxzero : dirichletMatrix (fun i : Fin N => D i.val) *ᵥ x = 0 := by
      ext ⟨a,i⟩
      rw [show x = (fun p => z (p.2.val + 1) p.1) from rfl,
        dirichlet_mulVec_sequence _ z hz0 hzN]
      dsimp [z]
      rw [hrec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Pi.sub_apply]
      ring
    have hx : x = 0 := by
      by_contra hx
      have h := hpos.dotProduct_mulVec_pos hx
      rw [hxzero, dotProduct_zero] at h
      exact (lt_irrefl 0) h
    funext a
    have h := congrFun hx (a,⟨0,hNpos⟩)
    simpa [x,z,h1] using h
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have h : Y (N + 1) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hker (v - w) h)

end
end PositiveEinsteinFour.Jacobi

end OAI
