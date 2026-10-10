import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.FramedPullback
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalCurveDegree

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

variable {X Z : Scheme.{0}}

def structuralChartMap (p : Z ⟶ Spec (CommRingCat.of ℂ)) (j : X ⟶ Z) (U : Z.Opens) :
    letI : Algebra ℂ Γ(U.toScheme,⊤) := (baseScalars (U.ι ≫ p)).toAlgebra
    letI : Algebra ℂ Γ((j ⁻¹ᵁ U).toScheme,⊤) :=
      (baseScalars ((j ⁻¹ᵁ U).ι ≫ (j ≫ p))).toAlgebra
    Γ(U.toScheme,⊤) →ₐ[ℂ] Γ((j ⁻¹ᵁ U).toScheme,⊤) := by
  letI : Algebra ℂ Γ(U.toScheme,⊤) := (baseScalars (U.ι ≫ p)).toAlgebra
  letI : Algebra ℂ Γ((j ⁻¹ᵁ U).toScheme,⊤) :=
    (baseScalars ((j ⁻¹ᵁ U).ι ≫ (j ≫ p))).toAlgebra
  refine { (j ∣_ U).appTop.hom with commutes' := ?_ }
  intro c
  change (j ∣_ U).appTop (baseScalars (U.ι ≫ p) c) =
    baseScalars ((j ⁻¹ᵁ U).ι ≫ (j ≫ p)) c
  have hc : (j ∣_ U) ≫ (U.ι ≫ p) = (j ⁻¹ᵁ U).ι ≫ (j ≫ p) := by
    rw [← Category.assoc,morphismRestrict_ι j U,Category.assoc]
  rw [← hc,baseScalars_comp_actual]
  rfl

lemma structuralChartMap_surjective (p : Z ⟶ Spec (CommRingCat.of ℂ))
    (j : X ⟶ Z) [IsClosedImmersion j] (U : Z.affineOpens) :
    Function.Surjective (structuralChartMap p j U.1) := by
  exact (j ∣_ U.1).app_surjective ⊤ (isAffineOpen_top U.1.toScheme)

theorem actual_pullback_nodal_degree_bound [IsIntegral X] [IsNoetherian X]
    (p : Z ⟶ Spec (CommRingCat.of ℂ)) (j : X ⟶ Z) [IsClosedImmersion j]
    [IsProper (j ≫ p)] (hd : topologicalKrullDim X = 1)
    {σ : Type} [Fintype σ] {M : X.Modules}
    (a : σ → (O X ⟶ M)) (ha : (⨆ k, SectionOpens.isoOpen (a k)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars (j ≫ p)) a ha)]
    (L : LineBundle Z) (s : O Z ⟶ L.sheaf)
    (U : Z.affineOpens) [Nonempty (j ⁻¹ᵁ U.1).toScheme]
    [IsDomain Γ(U.1.toScheme,⊤)]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hR : ringKrullDim Γ(U.1.toScheme,⊤) ≤ 2)
    (q : letI : Algebra ℂ Γ(U.1.toScheme,⊤) := (baseScalars (U.1.ι ≫ p)).toAlgebra
      (ℂ × ℂ) → (Γ(U.1.toScheme,⊤) →ₐ[ℂ] ℂ))
    (hq : ∀ t, AnalyticAt ℂ (fun z => q z t) 0)
    (hjets : letI : Algebra ℂ Γ(U.1.toScheme,⊤) := (baseScalars (U.1.ι ≫ p)).toAlgebra
      ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
          (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
    (g : Γ(U.1.toScheme,⊤)) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
    (hker : RingHom.ker (j ∣_ U.1).appTop.hom = Ideal.span {g})
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2)
    (hf : coefficient e (restrictSection U.1.ι s) ∉ Ideal.span {g}) :
    letI : Algebra ℂ Γ(U.1.toScheme,⊤) := (baseScalars (U.1.ι ≫ p)).toAlgebra
    let f := coefficient e (restrictSection U.1.ι s)
    (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ) : ℤ) ≤
      eulerCharacteristic (j ≫ p) 1 ((Scheme.Modules.pullback j).obj L.sheaf) -
         eulerCharacteristic (j ≫ p) 1 (O X) := by
  let : Algebra ℂ Γ(U.1.toScheme,⊤) := (baseScalars (U.1.ι ≫ p)).toAlgebra
  let : IsAffine (j ⁻¹ᵁ U.1).toScheme := U.2.preimage j
  let : IsNoetherian (j ⁻¹ᵁ U.1).toScheme := {}
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame j U.1 e s
  have hs : pullbackSection j s ≠ 0 := by
    intro hz
    have hzero : coefficient eF
        (restrictSection (j ⁻¹ᵁ U.1).ι (pullbackSection j s)) = 0 := by
      rw [hz,restrictSection_zero,coefficient_zero]
    rw [he] at hzero
    apply hf
    rw [← hker]
    exact hzero
  exact projective_nodal_degree_bound (j ≫ p) hd a ha (L.pullback j)
    (pullbackSection j s) hs (j ⁻¹ᵁ U.1).ι eF hR q hq hjets
    (coefficient e (restrictSection U.1.ι s)) g hg0 u hu hu0 hg hf
    (structuralChartMap p j U.1) (structuralChartMap_surjective p j U) hker he.symm
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
