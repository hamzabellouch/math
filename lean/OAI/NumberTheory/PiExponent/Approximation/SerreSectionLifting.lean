import OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing

namespace OAI

namespace PiExponent.GeometrySupport.SerreSectionLifting
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem globalSections_surjective_of_h1_zero
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hzero : ∀ x : cohomology S.X₁ 1, x = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  intro s
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS
    (Ext.mk₀ s) (n₁ := 1) rfl (hzero _)
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

theorem eventual_twist_globalSections_surjective
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L : LineBundle X) (hL : LineBundle.IsAmple X L)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) [S.X₁.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (fun s : GlobalSections X ((moduleTwistFunctor L n).obj S.X₂) =>
        s ≫ (moduleTwistFunctor L n).map S.g) := by
  obtain ⟨N, hN⟩ := NoetherianAmpleSerreVanishing.ample_serre_vanishing p L hL S.X₁
  refine ⟨N, fun n hn => ?_⟩
  exact globalSections_surjective_of_h1_zero (S.map (moduleTwistFunctor L n))
    (moduleTwistFunctor_shortExact L n S hS) (hN n hn 1 (by decide))

end
end PiExponent.GeometrySupport.SerreSectionLifting

end OAI
