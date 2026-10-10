import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalGlobalLength
import OAI.AlgebraicGeometry.Seshadri.Sheaves.CartierRestriction

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.AnalyticCoordinates
open MaximalSeshadri.NodalLocal
open scoped Topology

theorem nodal_branch_orders_le_ideal_euler {X : Scheme}
    [IsLocallyNoetherian X] [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper g]
    (I J : X.IdealSheafData) [IsIntegral I.subscheme] [IsNoetherian I.subscheme]
    (hdI : topologicalKrullDim I.subscheme = 1)
    {σ : Type} [Fintype σ] {M : I.subscheme.Modules}
    (s : σ → (Frames.O I.subscheme ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (Projective.sectionsMorphism
      ((I.subschemeι ≫ g).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs)]
    (hJ : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X,U.1),
      J.ideal U = Ideal.span {r})
    (U : X.affineOpens) (y : (I ⊔ J).subscheme)
    (hy : (I ⊔ J).subschemeι y ∈ U.1) (hd : ringKrullDim Γ(X,U.1) ≤ 2)
    (q : let _ : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra;
      (ℂ × ℂ) → (Γ(X,U.1) →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hp : RingHom.ker (q 0) = (U.2.isoSpec.hom ⟨(I ⊔ J).subschemeι y,hy⟩).asIdeal)
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
    (hf : f ∉ Ideal.span {t})
    (hI : I.ideal U = Ideal.span {t}) (hF : J.ideal U = Ideal.span {f}) :
    let _ : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra
    ((restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℤ) ≤
      eulerCharacteristic (I.subschemeι ≫ g) 1 (structureSheaf I.subscheme) -
        eulerCharacteristic (I.subschemeι ≫ g) 1
          (IdealModule.closedModule (J.comap I.subschemeι)) := by
  have hn : ¬ J ≤ I := by
    intro he
    apply hf
    rw [← hI]
    apply he U
    rw [hF]
    exact Ideal.subset_span (by simp)
  rw [projective_curve_intersection_ideal_euler g I J hdI s hs hn hJ]
  have hb := nodal_branch_orders_le_global_length g I J hdI.le U y hy hd q hq hp
    hjets f t u hu hu0 ht ht0 htp hf hI hF
  dsimp only at hb ⊢
  exact_mod_cast hb

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
