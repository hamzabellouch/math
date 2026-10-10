import OAI.Analysis.KadisonKastler.FiniteGroupAverage
import OAI.Analysis.KadisonKastler.BoundaryIntertwiner

namespace OAI

/-! # Correcting finite-group unitary representations

The normalized counting mean removes the averaging premise from the bounded
quadratic iteration. The constants are independent of the group's order.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G B : Type*} [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [CStarAlgebra B]

/-- A uniformly approximate finite-group representation is uniformly close to
an exact unitary representation in the same C-star algebra. -/
theorem exists_finiteGroup_representation (V : G → unitary B) {δ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / 64)
    (hV : ∀ g h, ‖(V g : B) * V h - V (g * h)‖ ≤ δ) :
    ∃ W : G →* unitary B, ∀ g, ‖(W g : B) - V g‖ ≤ 2 * δ := by
  let α : G →* (B ≃⋆ₐ[ℂ] B) := 1
  let X := boundedUnitaryFamily V
  have hd : unitaryCocycleDefect α X ≤ δ := by
    apply (BoundedContinuousFunction.norm_le hδ).mpr
    rintro ⟨g, h⟩
    exact hV g h
  obtain ⟨Y, hY, hdist⟩ := exists_bounded_cocycle_of_equivariant_mean α
    finiteGroupBimoduleMean (fun g f => finiteGroupAverage_translate g f) X
    (hd.trans hsmall)
  have hlaw (g h : G) : Y.val g * Y.val h = Y.val (g * h) := hY g h
  let W : G →* unitary B :=
    { toFun := unitaryFamilyEval Y
      map_one' := by
        apply mul_left_cancel (a := unitaryFamilyEval Y 1)
        apply Subtype.ext
        change Y.val 1 * Y.val 1 = Y.val 1 * 1
        simpa only [one_mul, mul_one] using hlaw 1 1
      map_mul' g h := by
        apply Subtype.ext
        exact (hlaw g h).symm }
  refine ⟨W, fun g => ?_⟩
  have hn := (X.val - Y.val).norm_coe_le_norm g
  have hb : ‖X.val - Y.val‖ ≤ 2 * δ := by
    have he : ‖X.val - Y.val‖ ≤ 2 * unitaryCocycleDefect α X := by
      simpa only [Subtype.dist_eq, dist_eq_norm] using hdist
    exact he.trans (mul_le_mul_of_nonneg_left hd (by norm_num))
  change ‖Y.val g - X.val g‖ ≤ _
  rw [norm_sub_rev]
  exact hn.trans hb

/-- Nearby finite-group representations are conjugate by a near-identity
unitary, uniformly in the size of the group. -/
theorem exists_unitary_finiteGroup_intertwiner (U W : G →* unitary B)
    {δ : ℝ} (hsmall : δ < 1)
    (hclose : ∀ g, ‖(W g : B) - U g‖ ≤ δ) :
    ∃ u : unitary B, (∀ g, (u : B) * U g = (W g : B) * u) ∧
      ‖(u : B) - 1‖ ≤ 2 * δ := by
  let α : G →* (B ≃⋆ₐ[ℂ] B) := 1
  apply exists_unitary_boundary_intertwiner α finiteGroupBimoduleMean
    (fun g f => finiteGroupAverage_translate g f) (boundedUnitaryFamily W)
    (fun g h => ?_) U (fun _ _ => rfl) hsmall hclose
  change (W g : B) * (W h : B) = (W (g * h) : B)
  simp only [map_mul, Submonoid.coe_mul]

end

end KadisonKastler

end OAI
