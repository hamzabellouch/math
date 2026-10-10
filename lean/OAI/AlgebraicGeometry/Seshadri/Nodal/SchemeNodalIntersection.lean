import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.SmoothAffineRefinement
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalBranch

namespace OAI

section
noncomputable section
                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.NodalLocal
open scoped Topology

theorem affine_node_stalk_colength {X : Scheme} [IsLocallyNoetherian X]
    (g : X ⟶ Spec (CommRingCat.of ℂ)) (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (q : let _ : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra;
      (ℂ × ℂ) → (Γ(X,U.1) →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hp : RingHom.ker (q 0) = (U.2.isoSpec.hom ⟨x,hx⟩).asIdeal)
    (hjets : let _ : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra;
      ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
        (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
    (f t : Γ(X,U.1)) (u : (ℂ × ℂ) → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (ht : ∀ᶠ z in 𝓝 0, q z t = u z*z.1*z.2)
    (hfX : let _ : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra;
      restrictX ℂ (bivariateTaylor q hq f) ≠ 0)
    (hfZ : let _ : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra;
      restrictZ ℂ (bivariateTaylor q hq f) ≠ 0) :
    let _ : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra
    let _ : Algebra Γ(X,U.1) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hx⟩
    let _ : Algebra ℂ (X.presheaf.stalk x) :=
      ((algebraMap Γ(X,U.1) (X.presheaf.stalk x)).comp (openScalars g U.1)).toAlgebra
    FiniteDimensional ℂ ((X.presheaf.stalk x) ⧸ Ideal.span
      {X.presheaf.germ U.1 x hx f, X.presheaf.germ U.1 x hx t}) ∧
    Module.finrank ℂ ((X.presheaf.stalk x) ⧸ Ideal.span
      {X.presheaf.germ U.1 x hx f, X.presheaf.germ U.1 x hx t}) =
      (restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat := by
  dsimp only
  let : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra
  let : Algebra Γ(X,U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hx⟩
  let : Algebra ℂ (X.presheaf.stalk x) :=
    ((algebraMap Γ(X,U.1) (X.presheaf.stalk x)).comp (openScalars g U.1)).toAlgebra
  let : IsScalarTower ℂ Γ(X,U.1) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : (RingHom.ker (q 0)).IsPrime := RingHom.ker_isPrime _
  let : (U.2.isoSpec.hom ⟨x,hx⟩).asIdeal.IsPrime := hp ▸ RingHom.ker_isPrime (q 0)
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (RingHom.ker (q 0)) := by
    change IsLocalization (RingHom.ker (q 0)).primeCompl (X.presheaf.stalk x)
    have he : (RingHom.ker (q 0)).primeCompl =
        (U.2.isoSpec.hom ⟨x,hx⟩).asIdeal.primeCompl := by
      ext a
      change a ∉ RingHom.ker (q 0) ↔ a ∉ (U.2.isoSpec.hom ⟨x,hx⟩).asIdeal
      rw [hp]
    rw [he]
    exact U.2.isLocalization_stalk ⟨x,hx⟩
  exact local_nodal_colength q hq hjets (X.presheaf.stalk x) f t u hu hu0 ht hfX hfZ

theorem affine_integral_node_stalk_colength {X : Scheme} [IsLocallyNoetherian X] [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of ℂ)) (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (hne : Nonempty U.1) (hd : ringKrullDim Γ(X,U.1) ≤ 2)
    (q : let _ : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra;
      (ℂ × ℂ) → (Γ(X,U.1) →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hp : RingHom.ker (q 0) = (U.2.isoSpec.hom ⟨x,hx⟩).asIdeal)
    (hjets : let _ : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra;
      ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
        (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
    (f t : Γ(X,U.1)) (u : (ℂ × ℂ) → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (ht : ∀ᶠ z in 𝓝 0, q z t = u z*z.1*z.2)
    (ht0 : t ≠ 0) (htp : (Ideal.span {t}).IsPrime)
    (hf : f ∉ Ideal.span {t}) :
    let _ : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra
    let _ : Algebra Γ(X,U.1) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hx⟩
    let _ : Algebra ℂ (X.presheaf.stalk x) :=
      ((algebraMap Γ(X,U.1) (X.presheaf.stalk x)).comp (openScalars g U.1)).toAlgebra
    FiniteDimensional ℂ ((X.presheaf.stalk x) ⧸ Ideal.span
      {X.presheaf.germ U.1 x hx f, X.presheaf.germ U.1 x hx t}) ∧
    Module.finrank ℂ ((X.presheaf.stalk x) ⧸ Ideal.span
      {X.presheaf.germ U.1 x hx f, X.presheaf.germ U.1 x hx t}) =
      (restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat := by
  dsimp only
  let : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra
  let : Algebra Γ(X,U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hx⟩
  let : Algebra ℂ (X.presheaf.stalk x) :=
    ((algebraMap Γ(X,U.1) (X.presheaf.stalk x)).comp (openScalars g U.1)).toAlgebra
  let : IsScalarTower ℂ Γ(X,U.1) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : (RingHom.ker (q 0)).IsPrime := RingHom.ker_isPrime _
  let : (U.2.isoSpec.hom ⟨x,hx⟩).asIdeal.IsPrime := hp ▸ RingHom.ker_isPrime (q 0)
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (RingHom.ker (q 0)) := by
    change IsLocalization (RingHom.ker (q 0)).primeCompl (X.presheaf.stalk x)
    have he : (RingHom.ker (q 0)).primeCompl =
        (U.2.isoSpec.hom ⟨x,hx⟩).asIdeal.primeCompl := by
      ext a
      change a ∉ RingHom.ker (q 0) ↔ a ∉ (U.2.isoSpec.hom ⟨x,hx⟩).asIdeal
      rw [hp]
    rw [he]
    exact U.2.isLocalization_stalk ⟨x,hx⟩
  let := hne
  let := htp
  exact integral_nodal_colength hd q hq hjets (X.presheaf.stalk x) f t ht0 u hu hu0 ht hf

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
