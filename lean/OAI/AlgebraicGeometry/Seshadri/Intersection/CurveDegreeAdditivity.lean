import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.FiniteSupportTwist

namespace OAI

section
noncomputable section
                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

def tensorCokernelComplexEquiv (p : X ⟶ Spec (CommRingCat.of ℂ))
    (hd : topologicalKrullDim X ≤ 1) (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    letI := Module.compHom Γ(cokernel (sectionMultiply L M s),⊤) (baseScalars p)
    letI := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
    Γ(cokernel (sectionMultiply L M s),⊤) ≃ₗ[ℂ] Γ(cokernel s,⊤) := by
  letI := Module.compHom Γ(cokernel (sectionMultiply L M s),⊤) (baseScalars p)
  letI := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
  let e := tensorCokernelGlobalEquiv hd L M s hs
  let f : Γ(cokernel (sectionMultiply L M s),⊤) →ₗ[ℂ] Γ(cokernel s,⊤) :=
    { toFun := fun x => e x
      map_add' := e.map_add
      map_smul' := by
        intro r x
        change e (baseScalars p r • x) = baseScalars p r • e x
        exact e.map_smul _ _ }
  exact LinearEquiv.ofBijective f e.bijective

theorem projective_section_tensor_euler_add {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L M : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) := by
  let := Module.compHom Γ(cokernel (sectionMultiply L M s),⊤) (baseScalars p)
  let := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
  rw [projective_tensor_euler_difference p hd a ha L M s hs,
    projective_section_euler_difference p hd a ha L s hs]
  exact_mod_cast (tensorCokernelComplexEquiv p hd.le L M s hs).finrank_eq

theorem projective_section_power_euler {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    eulerCharacteristic p 1 (L.pow n).sheaf - eulerCharacteristic p 1 (O X) =
      (n : ℤ) * (eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X)) := by
  induction n with
  | zero => simp [LineBundle.pow,modulePow,O]
  | succ n ih =>
    have he := projective_section_tensor_euler_add p hd a ha L (L.pow n) s hs
    change eulerCharacteristic p 1 (L.pow (n+1)).sheaf -
      eulerCharacteristic p 1 (L.pow n).sheaf = _ at he
    push_cast
    nlinarith

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
