import OAI.Algebra.AuslanderReiten.Cones.CochainCokernel
import OAI.Algebra.AuslanderReiten.Complete.CompleteNullhomotopy

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex

namespace ArExplicit.CompleteComparison

universe u
variable {R : Type u} [Ring R]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

@[simp]
theorem cochainCokernelMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    cochainCokernelMap (f ≫ g) = (cochainCokernelMap g).comp (cochainCokernelMap f) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range (K.d (-1) 0).hom).mkQ_surjective x
  rfl

@[simp]
theorem cochainCokernelMap_sub (f g : K ⟶ L) :
    cochainCokernelMap (f - g) = cochainCokernelMap f - cochainCokernelMap g := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range (K.d (-1) 0).hom).mkQ_surjective x
  change Submodule.Quotient.mk ((f.f 0).hom x - (g.f 0).hom x) = _
  exact Submodule.Quotient.mk_sub _

theorem cochain_nullhomotopy_of_cokernel_zero
    (hK : TotallyAcyclicCochain K) (hL : ExactProjectiveCochain L)
    (f : K ⟶ L) (hf : cochainCokernelMap f = 0) :
    ∃ H : Homotopy f 0, H.hom 1 0 = 0 := by
  have hz : cokernelMap (extendMap f negIndexEmbedding) 0 = 0 := by
    apply LinearMap.ext
    intro x
    apply (cochainCokernelLinearEquiv L).injective
    have hh := DFunLike.congr_fun (cochainCokernelLinearEquiv_natural f) x
    rw [hf] at hh
    simpa using hh
  obtain ⟨H, hH⟩ := nullhomotopy_of_cokernel_zero hK.to_chain hL.to_chain
    (extendMap f negIndexEmbedding) hz
  let H' : Homotopy (extendMap f negIndexEmbedding) (extendMap (0 : K ⟶ L) negIndexEmbedding) :=
    H.trans (Homotopy.ofEq (extendMap_zero K L negIndexEmbedding).symm)
  refine ⟨H'.ofExtend, ?_⟩
  change (K.extendXIso negIndexEmbedding (i := 1) (i' := -1) rfl).inv ≫ H'.hom (-1) 0 ≫
    (L.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom = 0
  have hs : H'.hom (-1) 0 = 0 := by
    simp [H', Homotopy.trans_hom, hH]
  simp [hs]

theorem cochain_homotopy_of_cokernel_eq
    (hK : TotallyAcyclicCochain K) (hL : ExactProjectiveCochain L)
    (f g : K ⟶ L) (hfg : cochainCokernelMap f = cochainCokernelMap g) :
    ∃ H : Homotopy f g, H.hom 1 0 = 0 := by
  obtain ⟨H, hH⟩ := cochain_nullhomotopy_of_cokernel_zero hK hL (f - g) (by
    rw [cochainCokernelMap_sub, hfg, sub_self])
  exact ⟨Homotopy.equivSubZero.symm H, hH⟩

end ArExplicit.CompleteComparison

end

end OAI
