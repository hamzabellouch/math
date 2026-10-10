import OAI.Algebra.AuslanderReiten.Complete.CompleteShiftDual
import OAI.Algebra.AuslanderReiten.Cones.CokernelLinearCongr

namespace OAI

open CategoryTheory HomologicalComplex

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

abbrev CochainCokernel := K.X 0 ⧸ LinearMap.range (K.d (-1) 0).hom

noncomputable def cochainCokernelLinearEquiv :
    Cokernel (chainOfCochain K) 0 ≃ₗ[R] CochainCokernel K :=
  cokernelLinearCongr _ _
    (K.extendXIso negIndexEmbedding (i := -1) (i' := 1) (by rfl)).toLinearEquiv
    (K.extendXIso negIndexEmbedding (i := 0) (i' := 0) (by rfl)).toLinearEquiv (by
      exact (congrArg ModuleCat.Hom.hom
        (reverseShortComplexIso K (-1) 0 1 1 0 (-1) rfl rfl rfl).hom.comm₁₂).symm)

variable {K}
variable {L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)

def cochainCokernelMap : CochainCokernel K →ₗ[R] CochainCokernel L :=
  (LinearMap.range (K.d (-1) 0).hom).liftQ
    ((LinearMap.range (L.d (-1) 0).hom).mkQ.comp (f.f 0).hom) (by
      rintro _ ⟨x, rfl⟩
      change (LinearMap.range (L.d (-1) 0).hom).mkQ ((f.f 0).hom ((K.d (-1) 0).hom x)) = 0
      have h := congrArg (fun g : K.X (-1) ⟶ L.X 0 => g.hom x) (f.comm (-1) 0)
      change (L.d (-1) 0).hom ((f.f (-1)).hom x) = (f.f 0).hom ((K.d (-1) 0).hom x) at h
      rw [← h]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩)

@[simp]
theorem cochainCokernelMap_mk (x : K.X 0) :
    cochainCokernelMap f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((f.f 0).hom x) := rfl

theorem cochainCokernelLinearEquiv_natural :
    (cochainCokernelLinearEquiv L).toLinearMap.comp
      (cokernelMap (extendMap f negIndexEmbedding) 0) =
    (cochainCokernelMap f).comp (cochainCokernelLinearEquiv K).toLinearMap := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range ((chainOfCochain K).d 1 0).hom).mkQ_surjective z
  change (LinearMap.range (L.d (-1) 0).hom).mkQ
    ((L.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom
      (((extendMap f negIndexEmbedding).f 0).hom x)) =
    (LinearMap.range (L.d (-1) 0).hom).mkQ
      ((f.f 0).hom ((K.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom x))
  congr 1
  have h := extendMap_f f negIndexEmbedding (i := 0) (i' := 0) rfl
  rw [h]
  simp

theorem cochainCokernelMap_surjective
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    Function.Surjective (fun f : K ⟶ L => cochainCokernelMap f) := by
  intro u
  let v := (cochainCokernelLinearEquiv L).symm.toLinearMap.comp
    (u.comp (cochainCokernelLinearEquiv K).toLinearMap)
  obtain ⟨F, hF⟩ := cokernelMap_surjective hK hL v
  obtain ⟨φ, rfl⟩ := Functor.map_surjective (negIndexEmbedding.extendFunctor (ModuleCat.{u} R)) F
  refine ⟨φ, ?_⟩
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun (cochainCokernelLinearEquiv_natural φ)
    ((cochainCokernelLinearEquiv K).symm x)
  change (cochainCokernelLinearEquiv L)
    (cokernelMap (extendMap φ negIndexEmbedding) 0 ((cochainCokernelLinearEquiv K).symm x)) =
    cochainCokernelMap φ ((cochainCokernelLinearEquiv K) ((cochainCokernelLinearEquiv K).symm x)) at h
  change cokernelMap (extendMap φ negIndexEmbedding) 0 = v at hF
  rw [hF] at h
  simpa [v] using h.symm

end ArExplicit.CompleteComparison

end OAI
