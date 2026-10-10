import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Configurations.AffinePointParameters
import OAI.AlgebraicGeometry.Seshadri.Jets.JetOpenness

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.AlgebraicJets

theorem exists_open_jet_configuration (S : Surface) (r : ℕ)
    (U : S.scheme.affineOpens) (t : Fin 2 → Γ(S.scheme,U.1))
    (het : (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale)
    {A : Type} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ℓ : letI := (openScalars S.structureMap U.1).toAlgebra;
      A →ₗ[ℂ] Γ(S.scheme,U.1))
    (m : ℕ) (hm : 0 < m)
    (p : letI := (openScalars S.structureMap U.1).toAlgebra;
      Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
    (hp : ∀ a, (∀ i, ℓ a ∈ (RingHom.ker (p i))^m) → a = 0) :
    ∃ W : (surfacePower S r).left.Opens,
      tupleImage S r (fun i => affineComplexPoint S.structureMap U (p i)) ∈ W ∧
      ∀ q : Fin r → ComplexPoint S, tupleImage S r q ∈ W →
        ∃ ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
          Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
          (∀ i, affineComplexPoint S.structureMap U (ρ i) = q i) ∧
          ∀ a, (∀ i, ℓ a ∈ (RingHom.ker (ρ i))^m) → a = 0 := by
  classical
  let := (openScalars S.structureMap U.1).toAlgebra
  let φt := MvPolynomial.aeval (R := ℂ) t
  let := φt.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) :=
    IsScalarTower.of_algebraMap_eq fun c => (φt.commutes c).symm
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) :=
    RingHom.etale_algebraMap.mp het
  let Q := surfacePower S r
  let pr (i : Fin r) : Q.left ⟶ S.scheme := (Pi.π (fun _ : Fin r => Over.mk S.structureMap) i).left
  have hpr (i : Fin r) : pr i ≫ S.structureMap = Q.hom := Over.w _
  let pp : Fin r → ComplexPoint S := fun i => affineComplexPoint S.structureMap U (p i)
  let x := tupleImage S r pp
  let B : Q.left.Opens := ⟨⋂ i, pr i ⁻¹' (U.1 : Set S.scheme),
    isOpen_iInter_of_finite fun i => U.1.isOpen.preimage (pr i).continuous⟩
  have hxB : x ∈ B := by
    change x ∈ ⋂ i, pr i ⁻¹' (U.1 : Set S.scheme)
    simp only [Set.mem_iInter, Set.mem_preimage]
    intro i
    change ((Pi.lift pp) ≫ Pi.π (fun _ : Fin r => Over.mk S.structureMap) i).left (fieldPoint ℂ) ∈ U.1
    rw [Pi.lift_comp_π]
    change U.2.fromSpec _ ∈ (U.1 : Set S.scheme)
    rw [← U.2.range_fromSpec]
    exact Set.mem_range_self _
  obtain ⟨V,hV,hxV,hVB⟩ := exists_isAffineOpen_mem_and_subset hxB
  let V' : Q.left.affineOpens := ⟨V,hV⟩
  let := (openScalars Q.hom V).toAlgebra
  have hVU (i : Fin r) : V ≤ pr i ⁻¹ᵁ U.1 := fun z hz =>
    Set.mem_iInter.mp (hVB hz) i
  let φ (i : Fin r) := affineMapAlgHom Q.hom S.structureMap (pr i) (hpr i) U V' (hVU i)
  obtain ⟨a,ha⟩ := affineComplexPoint_factor Q.hom V' (Pi.lift pp) hxV
  have hap (i : Fin r) : a.comp (φ i) = p i := by
    apply affineComplexPoint_image_injective S.structureMap U
    have H := affineMapAlgHom_point Q.hom S.structureMap (pr i) (hpr i) U V' (hVU i) a
    rw [ha] at H
    have Hp : (Pi.lift pp).left ≫ pr i = (pp i).left :=
      congrArg Over.Hom.left (Pi.lift_comp_π pp i)
    exact congrArg (fun k : complexBase ⟶ S.scheme => k (fieldPoint ℂ)) (H.trans Hp)
  have hop := isOpen_multipoint_jet_separation (σ := Fin 2)
    (fun _ : Fin r => Γ(S.scheme,U.1)) φ (fun _ => ℓ) m hm
  obtain ⟨D,hD,hDeq⟩ := isOpen_induced_iff.mp hop
  have haD : kernelPoint ℂ Γ(Q.left,V) a ∈ D := by
    change a ∈ (kernelPoint ℂ Γ(Q.left,V)) ⁻¹' D
    rw [hDeq]
    simpa only [Set.mem_ofPred_eq,hap] using hp
  let W : Q.left.Opens := ⟨hV.fromSpec '' D,hV.fromSpec.isOpenEmbedding.isOpenMap D hD⟩
  refine ⟨W,?_,?_⟩
  · refine ⟨kernelPoint ℂ Γ(Q.left,V) a,haD,?_⟩
    exact congrArg (fun k : Over.mk (𝟙 complexBase) ⟶ Over.mk Q.hom =>
      k.left (fieldPoint ℂ)) ha
  · intro q hqW
    obtain ⟨z,hzD,hzq⟩ := hqW
    have hqV : tupleImage S r q ∈ V := by
      rw [← hzq]
      change hV.fromSpec z ∈ (V : Set Q.left)
      rw [← hV.range_fromSpec]
      exact Set.mem_range_self z
    obtain ⟨b,hb⟩ := affineComplexPoint_factor Q.hom V' (Pi.lift q) hqV
    have hbz : kernelPoint ℂ Γ(Q.left,V) b = z := by
      apply hV.fromSpec.isOpenEmbedding.injective
      exact (congrArg (fun k : Over.mk (𝟙 complexBase) ⟶ Over.mk Q.hom =>
        k.left (fieldPoint ℂ)) hb).trans hzq.symm
    have hbD : b ∈ (kernelPoint ℂ Γ(Q.left,V)) ⁻¹' D := by
      change kernelPoint ℂ Γ(Q.left,V) b ∈ D
      rw [hbz]; exact hzD
    rw [hDeq] at hbD
    refine ⟨fun i => b.comp (φ i),?_,hbD⟩
    intro i
    apply Over.OverMorphism.ext
    have H := affineMapAlgHom_point Q.hom S.structureMap (pr i) (hpr i) U V' (hVU i) b
    rw [hb] at H
    exact H.trans (congrArg Over.Hom.left (Pi.lift_comp_π q i))
end
end MaximalSeshadri.Geometry

end

end OAI
