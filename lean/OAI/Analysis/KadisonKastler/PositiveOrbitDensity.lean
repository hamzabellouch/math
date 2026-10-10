import OAI.Analysis.KadisonKastler.PositiveOrbitContraction

namespace OAI

/-! # Vanishing distance between positive unitary orbits

The uniform contraction forces the infimum of squared orbit distances to
vanish. Only the modular coisometries of the concrete product are used.
-/

namespace KadisonKastler
open Generator.Tracial
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance positiveOrbitDensityReal : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem positive_unitary_orbit_dense
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (Ω : H) (hΩ : J Ω=Ω)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ Ω (modularQuadratic J a Ω))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (x y : H) (hx : x ∈ modularPositiveCone (M := M) J Ω)
    (hy : y ∈ modularPositiveCone (M := M) J Ω)
    (hxn : ‖x‖=1) (hyn : ‖y‖=1)
    (hxs : Function.Injective (algebraVectorMap M x))
    (ε : ℝ) (hε : 0<ε) :
    ∃ u : unitary (Algebra M), ‖x-(modularUnitary J hJ u : H →L[ℂ] H) y‖<ε := by
  let S : Set ℝ := Set.range (fun u : unitary (Algebra M) =>
    ‖x-(modularUnitary J hJ u : H →L[ℂ] H) y‖^2)
  have hne : S.Nonempty := ⟨_,⟨1,rfl⟩⟩
  have hb : BddBelow S := ⟨0,by rintro _ ⟨u,rfl⟩; exact sq_nonneg _⟩
  have hn : 0 ≤ sInf S := le_csInf hne (by rintro _ ⟨u,rfl⟩; exact sq_nonneg _)
  have hstep (u : unitary (Algebra M)) :
      sInf S ≤ (1-1/16777216:ℝ)*‖x-(modularUnitary J hJ u : H →L[ℂ] H) y‖^2 := by
    have hp : (modularUnitary J hJ u : H →L[ℂ] H) y ∈
        modularPositiveCone (M := M) J Ω :=
      modularQuadratic_preserves_positiveCone J hJ hright Ω u.val hy
    obtain ⟨v,hv⟩ := positive_orbit_distance_contraction J hJ hright hleft Ω hΩ
      hpos hIII hremote x ((modularUnitary J hJ u : H →L[ℂ] H) y) hx hp hxn
      ((Unitary.norm_map _ _).trans hyn) hxs
    have he : (modularUnitary J hJ (v*u) : H →L[ℂ] H) y =
        (modularUnitary J hJ v : H →L[ℂ] H)
          ((modularUnitary J hJ u : H →L[ℂ] H) y) := by
      change modularQuadratic J (v.val*u.val) y =
        modularQuadratic J v.val (modularQuadratic J u.val y)
      rw [← modularQuadratic_mul J hJ hright]
      rfl
    apply (csInf_le hb (show _ ∈ S from ⟨v*u,rfl⟩)).trans
    change ‖x-(modularUnitary J hJ (v*u) : H →L[ℂ] H) y‖^2 ≤ _
    rw [he]
    exact hv
  have hi : sInf S ≤ (1-1/16777216:ℝ)*sInf S := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    obtain ⟨r,⟨u,rfl⟩,hu⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf S) hδ)
    have hs := hstep u
    linarith
  have hz : sInf S=0 := by linarith
  obtain ⟨r,⟨u,rfl⟩,hu⟩ := exists_lt_of_csInf_lt hne (show sInf S<ε^2 by rw [hz]; positivity)
  exact ⟨u,by nlinarith [norm_nonneg (x-(modularUnitary J hJ u : H →L[ℂ] H) y)]⟩

end
end KadisonKastler

end OAI
