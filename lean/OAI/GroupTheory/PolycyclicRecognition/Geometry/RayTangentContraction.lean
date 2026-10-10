import OAI.GroupTheory.PolycyclicRecognition.Geometry.RayGroupContraction

namespace OAI

/-! # Ray contraction in the actual tangent coordinate basis -/
noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold

section Coordinates
variable {V E G J : Type*} [LieRing V] [LieAlgebra ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [Fintype J]

theorem mapped_basis_exponentialLog
    (e : V ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    (b : Basis J ℝ V) (g : G) :
    (b.map e.toLinearEquiv).equivFun (chart.symm g) =
      b.equivFun (exponentialLog e Exp hbij g) := by
  rw [Basis.map_equivFun]
  change b.equivFun (e.symm (chart.symm g)) = _
  congr 1
  apply e.injective
  apply hbij.injective
  change Exp (e (e.symm (chart.symm g))) = Exp (e (exponentialLog e Exp hbij g))
  rw [e.apply_symm_apply]
  exact ((hchart _).symm.trans (chart.apply_symm_apply g)).trans
    (exp_exponentialLog e Exp hbij g).symm
end Coordinates

/-- Pull back a compact-set contraction estimate along actual factor
coordinates. The coordinate identity is retained pointwise. -/
theorem exists_compact_contraction_pullback
    {V D Q E J : Type*} [TopologicalSpace Q]
    [AddCommGroup E] [Module ℝ E] [Fintype J]
    (log : D → V) (size height : V → ℝ) (coords : Q → E)
    (action : V → Q → Q) (actual : D → Q → Q)
    (he : ∀ d q, actual d q = action (log d) q)
    (hb : ∃ (b : Basis J ℝ E) (p : ℕ) (rate : ℝ), 0 < rate ∧
      ∀ K : Set Q, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
        ∀ v, height v ≤ 0 → ∀ q ∈ K, ‖b.equivFun (coords (action v q))‖ ≤
          A * (1 + size v) ^ p * Real.exp (rate * height v)) :
    ∃ (b : Basis J ℝ E) (p : ℕ) (rate : ℝ), 0 < rate ∧
      ∀ K : Set Q, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
        ∀ d, height (log d) ≤ 0 → ∀ q ∈ K, ‖b.equivFun (coords (actual d q))‖ ≤
          A * (1 + size (log d)) ^ p * Real.exp (rate * height (log d)) := by
  obtain ⟨b, p, rate, hr, hbound⟩ := hb
  refine ⟨b, p, rate, hr, ?_⟩
  intro K hK
  obtain ⟨A, hA, hh⟩ := hbound K hK
  refine ⟨A, hA, ?_⟩
  intro d hd q hq
  rw [he]
  exact hh (log d) hd q hq

namespace CartanWordModel
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)

theorem coneAdjoint_projection
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (h : H) (x : cartanRootIdeal H) :
    M.coneAdjointAutomorphism T C hadd h (M.coneProjection C x) =
      M.coneProjection C (cartanIdealAdjointAutomorphism T H h x) := rfl

theorem exists_ray_tangent_compact_contraction
    (α : H →ₗ[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
    (Exp : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hbij : Function.Bijective Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchart : ∀ v, chart v = Exp v) :
    ∃ (b : Basis
        (Fin (finrank ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α))))
        ℝ (GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier)) (p : ℕ) (rate : ℝ),
      0 < rate ∧ ∀ K : Set Q.carrier, IsCompact K → ∃ A : ℝ, 0 ≤ A ∧
        ∀ h : H, α h ≤ 0 → ∀ q ∈ K,
          ‖b.equivFun (chart.symm (exponentialConjugate Q.equiv Exp hbij
            (M.coneAdjointAutomorphism T (positiveWeightRay α)
              (positiveWeightRay_add α) h) q))‖ ≤
            A * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ p * Real.exp (rate * α h) := by
  obtain ⟨b, p, rate, hrate, hb⟩ := M.exists_ray_group_compact_contraction
    T α Q Exp hbij chart hchart
  refine ⟨b.map Q.equiv.toLinearEquiv, p, rate, hrate, ?_⟩
  intro K hK
  obtain ⟨A, hA, hbound⟩ := hb K hK
  refine ⟨A, hA, ?_⟩
  intro h hh q hq
  rw [mapped_basis_exponentialLog Q.equiv Exp hbij chart hchart b]
  exact hbound h hh q hq
end CartanWordModel
end PolycyclicRecognition

end

end OAI
