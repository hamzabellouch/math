import Mathlib

namespace OAI

section
noncomputable section
                                     
section

namespace MaximalSeshadri.ExtCokernel
noncomputable section
open CategoryTheory CategoryTheory.Abelian
universe w v u t
variable {K : Type t} [CommRing K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C] {S : ShortComplex C}

def quotientEquiv (hS : S.ShortExact) (M : C)
    (hvan : ∀ x : Ext S.X₂ M 1, x = 0) :
    ((S.X₁ ⟶ M) ⧸ (LinearMap.range
      (Linear.leftComp K M S.f))) ≃ₗ[K] Ext S.X₃ M 1 := by
  let d : (S.X₁ ⟶ M) →ₗ[K] Ext S.X₃ M 1 :=
    (hS.extClass.precompOfLinear K M (add_zero 1)).comp Ext.linearEquiv₀.symm.toLinearMap
  have hd : Function.Surjective d := by
    intro x
    obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ hS M x (hvan _) (n₀ := 0) rfl
    refine ⟨Ext.linearEquiv₀ (R := K) y, ?_⟩
    change hS.extClass.comp (Ext.mk₀ (Ext.linearEquiv₀ (R := K) y)) (add_zero 1) = x
    rwa [Ext.mk₀_linearEquiv₀_apply]
  have hk : LinearMap.range (Linear.leftComp K M S.f) = d.ker := by
    ext f
    constructor
    · rintro ⟨g,rfl⟩
      change hS.extClass.comp (Ext.mk₀ (S.f ≫ g)) (add_zero 1) = 0
      rw [← Ext.mk₀_comp_mk₀]
      exact ShortComplex.ShortExact.extClass_comp_assoc hS _
    · intro hf
      change hS.extClass.comp (Ext.mk₀ f) (add_zero 1) = 0 at hf
      obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₁ hS M (Ext.mk₀ f) rfl hf
      refine ⟨Ext.linearEquiv₀ (R := K) y, ?_⟩
      apply (Ext.linearEquiv₀ (R := K)).symm.injective
      change Ext.mk₀ (S.f ≫ Ext.linearEquiv₀ (R := K) y) = Ext.mk₀ f
      simpa only [← Ext.mk₀_comp_mk₀,
        Ext.mk₀_linearEquiv₀_apply] using hy
  exact (Submodule.quotEquivOfEq _ _ hk).trans (d.quotKerEquivOfSurjective hd)

end
end MaximalSeshadri.ExtCokernel
end


end
end

end OAI
