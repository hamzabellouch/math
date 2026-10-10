import OAI.Analysis.KadisonKastler.InvariantGroupEmbedding

namespace OAI

/-! # Localized simultaneous group embeddings

Performing the final intertwining average and polar decomposition inside a
specified von Neumann algebra retains the location of the conjugating unitary.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The embedding unitary lies in any ambient von Neumann algebra containing
both the original and the target algebra. -/
theorem exists_unitary_invariantGroup_embedding_in_algebra
    (m : ScalarInvariantMean G) {M N J : VonNeumannAlgebra H}
    (hMJ : M ≤ J) (hNJ : N ≤ J)
    (U : G →* unitary (Algebra M)) {γ : ℝ}
    (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152) (hnear : NearInclusion M N γ) :
    ∃ w : unitary (H →L[ℂ] H), (w : H →L[ℂ] H) ∈ J ∧
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
  let jMJ := Unitary.map (StarMonoidHom.ofClass (StarSubalgebra.inclusion hMJ))
  let jNJ := Unitary.map (StarMonoidHom.ofClass (StarSubalgebra.inclusion hNJ))
  let UJ : G →* unitary (Algebra J) := jMJ.toMonoidHom.comp U
  let WJ : G →* unitary (Algebra J) := jNJ.toMonoidHom.comp W
  obtain ⟨wJ, hwJ, hn⟩ := exists_unitary_boundary_intertwiner
    (1 : G →* (Algebra J ≃⋆ₐ[ℂ] Algebra J)) (m.algebraBimoduleMean J)
    (m.algebraMean_translate J) (boundedUnitaryFamily WJ)
    (by intro g h; change (WJ g : Algebra J) * WJ h = WJ (g * h)
        simp only [map_mul, Submonoid.coe_mul]) UJ (fun _ _ => rfl)
    (by linarith : 42 * γ < 1) hclose
  let w := ambientAlgebraUnitary wJ
  have hnorm : ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
    change ‖(wJ : Algebra J) - 1‖ ≤ _
    linarith
  refine ⟨w, wJ.val.property, fun g => ?_, hnorm⟩
  change (w : H →L[ℂ] H) * (U' g : H →L[ℂ] H) * star (w : H →L[ℂ] H) ∈ N
  have hi : (w : H →L[ℂ] H) * U' g = (W' g : H →L[ℂ] H) * w :=
    congrArg (fun x : Algebra J => (x : H →L[ℂ] H)) (hwJ g)
  rw [hi, mul_assoc, Unitary.mul_star_self_of_mem w.property, mul_one]
  exact (W g : Algebra N).property

end

end KadisonKastler

end OAI
