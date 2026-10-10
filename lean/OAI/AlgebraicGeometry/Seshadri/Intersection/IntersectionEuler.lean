import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.FiniteSupportCohomology
import OAI.AlgebraicGeometry.Seshadri.Sheaves.ClosedModuleExact
import OAI.AlgebraicGeometry.Seshadri.Intersection.EulerExact

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.FiniteSupport
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MaximalSeshadri.Geometry

variable {X Y : Scheme.{0}}

theorem finite_pushforward_finiteDimensional (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Finite X] (n : ℕ) :
    let M := (Scheme.Modules.pushforward f).obj (structureSheaf X)
    let _ := Module.compHom (cohomology M n) (baseScalars g)
    FiniteDimensional ℂ (cohomology M n) := by
  let M := (Scheme.Modules.pushforward f).obj (structureSheaf X)
  let := Module.compHom (cohomology M n) (baseScalars g)
  cases n with
  | zero =>
    let : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars g)
    let : Algebra ℂ Γ(X,⊤) := (baseScalars (f ≫ g)).toAlgebra
    let : FiniteDimensional ℂ Γ(X,⊤) := proper_finite_functions (f ≫ g)
    let e := (cohomologyZeroSections g M).trans (pushforwardUnitSections f g)
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  | succ n =>
    let : Subsingleton (cohomology M (n+1)) :=
      ⟨fun x y => (finite_pushforward_ext_zero (f ≫ g) f _ n x).trans
        (finite_pushforward_ext_zero (f ≫ g) f _ n y).symm⟩
    infer_instance

theorem closed_ideal_euler_difference (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsClosedImmersion f]
    [IsProper (f ≫ g)] [Finite X] (d : ℕ)
    (hfiniteI : ∀ n ≤ d,
      let _ := Module.compHom (cohomology (IdealModule.idealModule f) n) (baseScalars g)
      FiniteDimensional ℂ (cohomology (IdealModule.idealModule f) n))
    (hfiniteO : ∀ n ≤ d,
      let _ := Module.compHom (cohomology (structureSheaf Y) n) (baseScalars g)
      FiniteDimensional ℂ (cohomology (structureSheaf Y) n))
    [Subsingleton (cohomology (IdealModule.idealModule f) (d+1))] :
    eulerCharacteristic g d (structureSheaf Y) -
      eulerCharacteristic g d (IdealModule.idealModule f) =
      let _ : Algebra ℂ Γ(X,⊤) := (baseScalars (f ≫ g)).toAlgebra
      (Module.finrank ℂ Γ(X,⊤) : ℤ) := by
  have h := eulerCharacteristic_add g (IdealModule.closedSequence_exact f) d
    hfiniteI hfiniteO (fun n _ => finite_pushforward_finiteDimensional f g n)
  change eulerCharacteristic g d (structureSheaf Y) =
    eulerCharacteristic g d (IdealModule.idealModule f) +
      eulerCharacteristic g d ((Scheme.Modules.pushforward f).obj (structureSheaf X)) at h
  rw [h, add_sub_cancel_left, finite_pushforward_euler]

end
end MaximalSeshadri.FiniteSupport
end


end
end

end OAI
