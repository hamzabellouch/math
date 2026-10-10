import OAI.Algebra.AuslanderReiten.Cones.ConeEnd
import OAI.Algebra.AuslanderReiten.Cones.ConeExactness

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex CochainComplex.mappingCone

universe u

variable {R : Type u} [Ring R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

def coneTermEquiv (i : ℤ) : (mappingCone φ).X i ≃ₗ[R] G.X i × F.X (i + 1) where
  toLinearMap := ((snd φ).v i i (add_zero i)).hom.prod ((fst φ).1.v i (i + 1) rfl).hom
  invFun x := ((inr φ).f i).hom x.1 + ((inl φ).v (i + 1) i (by omega)).hom x.2
  left_inv x := by
    have h := congrArg (fun f : (mappingCone φ).X i ⟶ (mappingCone φ).X i => f.hom x)
      (id_X φ i (i + 1) rfl)
    simpa [add_comm] using h
  right_inv x := by
    apply Prod.ext
    · change ((snd φ).v i i (add_zero i)).hom
        (((inr φ).f i).hom x.1 + ((inl φ).v (i + 1) i (by omega)).hom x.2) = x.1
      rw [map_add]
      change (((inr φ).f i ≫ (snd φ).v i i (add_zero i)).hom x.1) +
        (((inl φ).v (i + 1) i (by omega) ≫ (snd φ).v i i (add_zero i)).hom x.2) = x.1
      simp
    · change ((fst φ).1.v i (i + 1) rfl).hom
        (((inr φ).f i).hom x.1 + ((inl φ).v (i + 1) i (by omega)).hom x.2) = x.2
      rw [map_add]
      change (((inr φ).f i ≫ (fst φ).1.v i (i + 1) rfl).hom x.1) +
        (((inl φ).v (i + 1) i (by omega) ≫ (fst φ).1.v i (i + 1) rfl).hom x.2) = x.2
      simp

@[simp] theorem coneTermEquiv_fst (i : ℤ) (x : (mappingCone φ).X i) :
    (coneTermEquiv φ i x).1 = ((snd φ).v i i (add_zero i)).hom x := rfl

@[simp] theorem coneTermEquiv_snd (i : ℤ) (x : (mappingCone φ).X i) :
    (coneTermEquiv φ i x).2 = ((fst φ).1.v i (i + 1) rfl).hom x := rfl

theorem coneTermEquiv_differential (i : ℤ) :
    (coneTermEquiv φ (i + 1)).toLinearMap.comp ((mappingCone φ).d i (i + 1)).hom =
      (coneBlock (G.d i (i + 1)).hom (F.d (i + 1) ((i + 1) + 1)).hom
        (φ.f (i + 1)).hom).comp (coneTermEquiv φ i).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change (((mappingCone φ).d i (i + 1) ≫ (snd φ).v (i + 1) (i + 1) (add_zero _)).hom x) =
      (G.d i (i + 1)).hom (((snd φ).v i i (add_zero _)).hom x) +
        (φ.f (i + 1)).hom (((fst φ).1.v i (i + 1) rfl).hom x)
    rw [d_snd_v φ i (i + 1) rfl]
    exact add_comm _ _
  · change (((mappingCone φ).d i (i + 1) ≫ (fst φ).1.v (i + 1) ((i + 1) + 1) rfl).hom x) =
      -(F.d (i + 1) ((i + 1) + 1)).hom (((fst φ).1.v i (i + 1) rfl).hom x)
    rw [d_fst_v φ i (i + 1) ((i + 1) + 1) rfl rfl]
    rfl

end ArExplicit

end

end OAI
