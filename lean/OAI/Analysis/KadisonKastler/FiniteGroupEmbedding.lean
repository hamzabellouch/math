import OAI.Analysis.KadisonKastler.FiniteGroupCorrection
import OAI.Analysis.KadisonKastler.ClosedUnitaryApproximation

namespace OAI

/-! # Moving a finite unitary group into a nearby closed algebra

Correct the unitary approximants inside the target algebra, then average an
intertwiner. Both operations have bounds independent of the group's order.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G A : Type*} [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [CStarAlgebra A]

omit [Fintype G] in
/-- The uniform multiplicative error of a unitary family close to a
representation is at most three times the uniform error. -/
theorem unitary_family_defect_le_of_close (U : G →* unitary A)
    (V : G → unitary A) {e : ℝ} (he : 0 ≤ e)
    (hV : ∀ g, ‖(V g : A) - U g‖ ≤ e) :
    ∀ g h, ‖(V g : A) * V h - V (g * h)‖ ≤ 3 * e := by
  let α : G →* (A ≃⋆ₐ[ℂ] A) := 1
  let X := boundedUnitaryFamily V
  let Y := boundedUnitaryFamily U
  have hz : unitaryCocycleError α Y = 0 := by
    ext ⟨g, h⟩
    change (U g : A) * U h - U (g * h) = 0
    simp only [map_mul, Submonoid.coe_mul, sub_self]
  have hXY : ‖X.val - Y.val‖ ≤ e :=
    (BoundedContinuousFunction.norm_le he).mpr hV
  have hLip := (unitaryCocycleError_lipschitz α).dist_le_mul X Y
  rw [dist_eq_norm, hz, sub_zero, Subtype.dist_eq, dist_eq_norm] at hLip
  have hd : unitaryCocycleDefect α X ≤ 3 * e :=
    hLip.trans (mul_le_mul_of_nonneg_left hXY (by norm_num))
  intro g h
  exact (norm_unitaryCocycleError_le α X g h).trans hd

/-- Uniform unitary approximants in a closed subalgebra give a near-identity
unitary moving the whole finite group into that subalgebra. -/
theorem exists_unitary_finiteGroup_embedding (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (U : G →* unitary A) (V : G → unitary S)
    {e : ℝ} (he : 0 ≤ e) (hsmall : 3 * e ≤ 1 / 64)
    (hV : ∀ g, ‖(V g : A) - U g‖ ≤ e) :
    ∃ w : unitary A,
      (∀ g, (w : A) * U g * star (w : A) ∈ S) ∧ ‖(w : A) - 1‖ ≤ 14 * e := by
  let j := Unitary.map (StarMonoidHom.ofClass S.subtype)
  have hdef : ∀ g h, ‖(V g : S) * V h - V (g * h)‖ ≤ 3 * e :=
    unitary_family_defect_le_of_close U (fun g => j (V g)) he hV
  obtain ⟨W, hW⟩ := exists_finiteGroup_representation V (by positivity) hsmall hdef
  let W' : G →* unitary A := j.toMonoidHom.comp W
  have hclose (g : G) : ‖(W' g : A) - U g‖ ≤ 7 * e := by
    have h₁ := hW g
    change ‖(W' g : A) - V g‖ ≤ 2 * (3 * e) at h₁
    have ht := norm_sub_le_norm_sub_add_norm_sub (W' g : A) (V g : A) (U g : A)
    linarith [hV g]
  obtain ⟨w, hw, hn⟩ := exists_unitary_finiteGroup_intertwiner U W'
    (by linarith : 7 * e < 1) hclose
  refine ⟨w, fun g => ?_, by linarith⟩
  rw [hw g, mul_assoc, Unitary.mul_star_self_of_mem w.property, mul_one]
  exact (W g : S).property

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The one-sided finite-group embedding supplied by a strict near inclusion. -/
theorem exists_unitary_finiteGroup_embedding_of_nearInclusion
    {M N : VonNeumannAlgebra H} (U : G →* unitary (Algebra M)) {γ : ℝ}
    (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152) (hnear : NearInclusion M N γ) :
    ∃ w : unitary (H →L[ℂ] H),
      (∀ g, unitaryConj w (U g : H →L[ℂ] H) ∈ N) ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  let : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_algebra N
  choose V hV using fun g => exists_unitary_approx_of_nearInclusion
    (by linarith : 2 * γ ≤ 1) hnear (U g)
  let U' : G →* unitary (H →L[ℂ] H) :=
    (Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype)).toMonoidHom.comp U
  obtain ⟨w, hw, hn⟩ := exists_unitary_finiteGroup_embedding N.toStarSubalgebra U' V
    (by positivity : 0 ≤ 6 * γ) (by linarith : 3 * (6 * γ) ≤ 1 / 64)
    (fun g => (hV g).le)
  exact ⟨w, hw, by linarith⟩

end

end KadisonKastler

end OAI
