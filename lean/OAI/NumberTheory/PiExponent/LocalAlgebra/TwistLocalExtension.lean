import OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing
import OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponentSeshadri.Frames PiExponent.GlobalSectionClearing
variable {X : Scheme}

theorem local_twist_extension (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens) [NoetherianSpace U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent]
    (x : Γ(M.restrict U.ι, U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)))) :
    let a := coefficient e (restrictSection U.ι s)
    let D := U.toScheme.basicOpen a
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : Γ(((moduleTwistFunctor L n).obj M).restrict U.ι,⊤),
      (((moduleTwistFunctor L n).obj M).restrict U.ι).presheaf.map
        (homOfLE (U.toScheme.basicOpen_le a)).op y =
      ((moduleTwistRestrictFrame L U e n).app M).inv.app D
        ((restrictScalar U.toScheme D a)^n • x) := by
  dsimp only
  obtain ⟨N, hN⟩ := global_section_extends_native (M.restrict U.ι)
    (coefficient e (restrictSection U.ι s)) x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn
  let E := (moduleTwistRestrictFrame L U e n).app M
  refine ⟨E.inv.app ⊤ y, ?_⟩
  have h := CategoryTheory.congr_fun (E.inv.mapPresheaf.naturality
    (homOfLE (U.toScheme.basicOpen_le (coefficient e (restrictSection U.ι s)))).op) y
  exact h.symm.trans (congrArg (E.inv.app _) hy)

theorem local_twist_extension_section (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens) [NoetherianSpace U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent]
    (x : Γ(M.restrict U.ι, U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)))) :
    let a := coefficient e (restrictSection U.ι s)
    let D := U.toScheme.basicOpen a
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : Γ(((moduleTwistFunctor L n).obj M).restrict U.ι,⊤),
      (((moduleTwistFunctor L n).obj M).restrict U.ι).presheaf.map
        (homOfLE (U.toScheme.basicOpen_le a)).op y =
      ((moduleTwistSection L s n).app M).app (U.ι ''ᵁ D) x := by
  dsimp only
  obtain ⟨N, hN⟩ := local_twist_extension L s U e M x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn
  refine ⟨y, hy.trans ?_⟩
  let D := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
  let E := (moduleTwistRestrictFrame L U e n).app M
  have h := moduleTwistSection_frame L s U e M D n x
  calc
    _ = E.inv.app D (E.hom.app D (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ D) x)) :=
      congrArg (E.inv.app D) h.symm
    _ = _ := congrArg (fun q => q.app D
      (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ D) x)) E.hom_inv_id

end
end PiExponentSeshadri.Geometry

end OAI
