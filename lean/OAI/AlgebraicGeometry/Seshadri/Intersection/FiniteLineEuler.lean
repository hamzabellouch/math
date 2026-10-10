import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.DiscreteLineBundle
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CohomologyIso
import OAI.AlgebraicGeometry.Seshadri.Intersection.IntersectionEuler
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.FiniteStalkSum

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.FiniteSupport
noncomputable section
open CategoryTheory AlgebraicGeometry MaximalSeshadri.Geometry

variable {X Y : Scheme.{0}}

theorem finite_line_pushforward_euler (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Finite X]
    (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic g d ((Scheme.Modules.pushforward f).obj L.sheaf) =
      let _ : Algebra ℂ Γ(X,⊤) := (baseScalars (f ≫ g)).toAlgebra
      (Module.finrank ℂ Γ(X,⊤) : ℤ) := by
  let : DiscreteTopology X := proper_finite_discrete (f ≫ g)
  obtain ⟨e⟩ := lineBundle_trivial L
  rw [eulerCharacteristic_iso g ((Scheme.Modules.pushforward f).mapIso e) d]
  exact finite_pushforward_euler f g d

theorem finite_line_pushforward_finiteDimensional (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Finite X]
    (L : LineBundle X) (n : ℕ) :
    let M := (Scheme.Modules.pushforward f).obj L.sheaf
    let _ := Module.compHom (cohomology M n) (baseScalars g)
    FiniteDimensional ℂ (cohomology M n) := by
  let : DiscreteTopology X := proper_finite_discrete (f ≫ g)
  obtain ⟨e⟩ := lineBundle_trivial L
  let M := (Scheme.Modules.pushforward f).obj L.sheaf
  let N := (Scheme.Modules.pushforward f).obj (structureSheaf X)
  let := Module.compHom (cohomology M n) (baseScalars g)
  let := Module.compHom (cohomology N n) (baseScalars g)
  let : FiniteDimensional ℂ (cohomology N n) := finite_pushforward_finiteDimensional f g n
  exact Module.Finite.of_surjective
    (cohomologyIso g ((Scheme.Modules.pushforward f).mapIso e) n).symm.toLinearMap
    (cohomologyIso g ((Scheme.Modules.pushforward f).mapIso e) n).symm.surjective

theorem finite_line_euler_eq_sum_stalks (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Fintype X]
    (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic g d ((Scheme.Modules.pushforward f).obj L.sheaf) =
      ∑ x : X, let _ := structuralStalkAlgebra (f ≫ g) x
        (Module.finrank ℂ (X.presheaf.stalk x) : ℤ) := by
  rw [finite_line_pushforward_euler]
  dsimp only
  have h := proper_finite_finrank_eq_sum_stalks (f ≫ g)
  dsimp only at h
  exact_mod_cast h

end
end MaximalSeshadri.FiniteSupport
end


end
end

end OAI
