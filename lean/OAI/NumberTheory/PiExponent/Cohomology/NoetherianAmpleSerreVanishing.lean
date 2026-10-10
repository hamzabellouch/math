import OAI.NumberTheory.PiExponent.Ampleness.NoetherianAmpleProjectiveSections
import OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSerreTransfer
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceSerre

namespace OAI

namespace PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem ample_serre_vanishing
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L : LineBundle X) (hL : LineBundle.IsAmple X L)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : CategoryTheory.Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  cases isEmpty_or_nonempty X with
  | inl hX =>
      let : IsEmpty X := hX
      refine ⟨0, fun n _ q hq => ?_⟩
      let : ((moduleTwistFunctor L n).obj M).IsFinitePresentation :=
        FiniteGlobalPresentation.moduleTwist_isFinitePresentation L n M
      let : ((moduleTwistFunctor L n).obj M).IsQuasicoherent :=
        (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
          ((moduleTwistFunctor L n).obj M)).choose.isQuasicoherent
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
      exact PiExponentSeshadri.AffineSchemeCohomology.affine_ext_zero X
        ((moduleTwistFunctor L n).obj M) r
  | inr hX =>
      obtain ⟨d, hd, σ, hσ, s, hs, hclosed⟩ := L.ample_projective_sections_noetherian p hL
      let : Fintype σ := hσ
      let : Nonempty σ := by
        obtain ⟨x⟩ := hX
        have hx : x ∈ (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
          rw [hs]
          trivial
        obtain ⟨i, _⟩ := Opens.mem_iSup.mp hx
        exact ⟨i⟩
      let k : R →+* Γ(X, ⊤) :=
        p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      let f : X ⟶ ProjectiveO1.projectiveSpace R σ := sectionsMorphism k s hs
      let : IsClosedImmersion f := hclosed
      let e := coordinateLineBundlePullbackIso (L.pow d) k s hs
      apply SerrePowerDescent.eventual_twist_ext_zero_of_power L d hd _ M
      intro A hA
      apply SerrePowerDescent.eventual_twist_ext_zero_of_lineIso e A
      apply ClosedImmersionSerreTransfer.eventual_twist_ext_zero_of_ambient f
        (ProjectiveO1.lineBundle (R := R) (σ := σ)) _ A
      intro N hN
      exact ProjectiveO1.serre_vanishing R σ N

theorem ample_serre_tensor_vanishing
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L : LineBundle X) (hL : LineBundle.IsAmple X L)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : cohomology (moduleTensor X M (modulePow X L.sheaf n)) q, x = 0 := by
  obtain ⟨N, hN⟩ := ample_serre_vanishing p L hL M
  refine ⟨N, fun n hn q hq => ?_⟩
  exact SerrePowerDescent.ext_zero_of_iso (moduleTwistPowerIso L M n) q (hN n hn q hq)

theorem ample_power_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L : LineBundle X) (hL : LineBundle.IsAmple X L) :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : cohomology (modulePow X L.sheaf n) q, x = 0 := by
  let : (structureSheaf X).IsFinitePresentation :=
    LineBundleCoherent.structureSheaf_isFinitePresentation
  obtain ⟨N, hN⟩ := ample_serre_vanishing p L hL (structureSheaf X)
  refine ⟨N, fun n hn q hq => ?_⟩
  exact SerrePowerDescent.ext_zero_of_iso (moduleTwistUnitIso L n) q (hN n hn q hq)

end
end PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing

end OAI
