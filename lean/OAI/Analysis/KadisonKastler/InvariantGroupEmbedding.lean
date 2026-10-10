import OAI.Analysis.KadisonKastler.SubalgebraInvariantMean
import OAI.Analysis.KadisonKastler.IncreasingFiniteMean
import OAI.Analysis.KadisonKastler.FiniteGroupEmbedding
import OAI.Analysis.KadisonKastler.AmenableEmbedding

namespace OAI

/-! # Near inclusions and groups with an invariant mean

The scalar mean is first restricted to the target von Neumann algebra.
Quadratic correction and a single polar intertwiner then embed every member
of the represented group simultaneously, including for infinite groups.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [CStarAlgebra B]

/-- The existing cocycle iteration, specialized to representations and an
actual invariant bimodule mean. -/
theorem exists_group_representation_of_mean
    (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate (1 : G →* (B ≃⋆ₐ[ℂ] B)) g f) = m.toCLM f)
    (V : G → unitary B) {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / 64)
    (hV : ∀ g h, ‖(V g : B) * V h - V (g * h)‖ ≤ δ) :
    ∃ W : G →* unitary B, ∀ g, ‖(W g : B) - V g‖ ≤ 2 * δ := by
  let α : G →* (B ≃⋆ₐ[ℂ] B) := 1
  let X := boundedUnitaryFamily V
  have hd : unitaryCocycleDefect α X ≤ δ := by
    apply (BoundedContinuousFunction.norm_le hδ).mpr
    rintro ⟨g, h⟩
    exact hV g h
  obtain ⟨Y, hY, hdist⟩ := exists_bounded_cocycle_of_equivariant_mean α m hm X
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A single near-identity unitary embeds a group admitting the supplied
invariant mean into the neighboring von Neumann algebra. -/
theorem exists_unitary_invariantGroup_embedding_of_nearInclusion
    (m : ScalarInvariantMean G) {M N : VonNeumannAlgebra H}
    (U : G →* unitary (Algebra M)) {γ : ℝ}
    (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152) (hnear : NearInclusion M N γ) :
    ∃ w : unitary (H →L[ℂ] H),
      (∀ g, unitaryConj w (U g : H →L[ℂ] H) ∈ N) ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  choose V hV using fun g => exists_unitary_approx_of_nearInclusion
    (by linarith : 2 * γ ≤ 1) hnear (U g)
  let j := Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype)
  let U' : G →* unitary (H →L[ℂ] H) := j.toMonoidHom.comp U
  have hdef : ∀ g h, ‖(V g : Algebra N) * V h - V (g * h)‖ ≤ 18 * γ := by
    have hh := unitary_family_defect_le_of_close U' (fun g => ambientAlgebraUnitary (V g))
      (by positivity : 0 ≤ 6 * γ) (fun g => (hV g).le)
    intro g h
    exact (hh g h).trans_eq (by ring)
  obtain ⟨W, hW⟩ := exists_group_representation_of_mean (m.algebraBimoduleMean N)
    (m.algebraMean_translate N) V (by positivity : 0 ≤ 18 * γ)
    (by linarith : 18 * γ ≤ 1 / 64) hdef
  let jN := Unitary.map (StarMonoidHom.ofClass N.toStarSubalgebra.subtype)
  let W' : G →* unitary (H →L[ℂ] H) := jN.toMonoidHom.comp W
  have hclose (g : G) : ‖(W' g : H →L[ℂ] H) - U' g‖ ≤ 42 * γ := by
    have hh := hW g
    change ‖(W' g : H →L[ℂ] H) - V g‖ ≤ 2 * (18 * γ) at hh
    have ht := norm_sub_le_norm_sub_add_norm_sub (W' g : H →L[ℂ] H)
      (V g : H →L[ℂ] H) (U' g : H →L[ℂ] H)
    have hv := hV g
    change ‖(V g : H →L[ℂ] H) - U' g‖ < 6 * γ at hv
    linarith
  obtain ⟨w, hw, hn⟩ := exists_unitary_boundary_intertwiner
    (1 : G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))) m.bimoduleMean
    m.bimoduleMean_trivial_equivariant (boundedUnitaryFamily W')
    (by intro g h; change (W' g : H →L[ℂ] H) * W' h = W' (g * h)
        simp only [map_mul, Submonoid.coe_mul]) U' (fun _ _ => rfl)
    (by linarith : 42 * γ < 1) hclose
  refine ⟨w, fun g => ?_, by linarith⟩
  change (w : H →L[ℂ] H) * (U' g : H →L[ℂ] H) * star (w : H →L[ℂ] H) ∈ N
  have hi : (w : H →L[ℂ] H) * U' g = (W' g : H →L[ℂ] H) * w := hw g
  rw [hi, mul_assoc, Unitary.mul_star_self_of_mem w.property, mul_one]
  exact (W g : Algebra N).property

end

end KadisonKastler

end OAI
