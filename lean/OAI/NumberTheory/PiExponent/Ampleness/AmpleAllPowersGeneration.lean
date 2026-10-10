import OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration
import OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws
import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent

namespace OAI

namespace PiExponent.AmpleGlobalGeneration
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem ample_eventual_global_generators [NoetherianSpace X]
    (L : LineBundle X) (hL : L.IsAmple) (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor L n).obj M).GeneratingSections, G.IsFiniteType := by
  classical
  obtain ⟨d, hd, l, s, hcover, haffine, _⟩ := L.ample_common_degree_cover hL
  have hresidue (r : Fin d) : ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor (L.pow d) n).obj
        ((moduleTwistFunctor L r.val).obj M)).GeneratingSections, G.IsFiniteType := by
    let := PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation L r.val M
    exact eventual_global_generators_of_section_cover (L.pow d)
      ((moduleTwistFunctor L r.val).obj M) s hcover haffine
  choose N hN using hresidue
  let B := Finset.univ.sup N
  refine ⟨d * B, fun n hn => ?_⟩
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  have hB : B ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by
    simpa only [Nat.mul_comm] using hn)
  have hr : N r ≤ n / d := (Finset.le_sup (f := N) (Finset.mem_univ r)).trans hB
  obtain ⟨G, hG⟩ := hN r (n / d) hr
  let : G.IsFiniteType := hG
  let e : ((moduleTwistFunctor (L.pow d) (n / d)).obj
      ((moduleTwistFunctor L r.val).obj M)) ≅ (moduleTwistFunctor L n).obj M :=
    moduleTwistPowerMulIso L ((moduleTwistFunctor L r.val).obj M) d (n / d) ≪≫
      eqToIso (by
        change (moduleTwistFunctor L (n % d) ⋙
          moduleTwistFunctor L (d * (n / d))).obj M = _
        rw [← moduleTwistFunctor_add, Nat.mod_add_div])
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e G, ⟨hG.finite⟩⟩

theorem ample_eventual_power_global_generators [NoetherianSpace X]
    (L : LineBundle X) (hL : L.IsAmple) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : (modulePow X L.sheaf n).GeneratingSections, G.IsFiniteType := by
  let : (structureSheaf X).IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  obtain ⟨N, hN⟩ := ample_eventual_global_generators L hL (structureSheaf X)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨G, hG⟩ := hN n hn
  let : G.IsFiniteType := hG
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso (moduleTwistUnitIso L n) G,
    ⟨hG.finite⟩⟩

end
end PiExponent.AmpleGlobalGeneration

end OAI
