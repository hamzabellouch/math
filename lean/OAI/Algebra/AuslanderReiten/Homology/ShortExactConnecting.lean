import OAI.Algebra.AuslanderReiten.Cones.ShortExactConeRaw
import OAI.Algebra.AuslanderReiten.Stable.RawSourceStable
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShiftedHomotopy

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Injective R R]
variable {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (p : CochainCokernel G →ₗ[R] CochainCokernel H)
variable (he : Function.Exact (cochainCokernelMap φ) p)
variable (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G) (hH : TotallyAcyclicCochain H)
variable (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p)
variable (κ : H ⟶ mappingCone φ)
variable (hκ : (HomotopyCategory.quotient _ _).map κ =
  (shortExactConeIso φ p he hF hG hH hi hp).inv)

include hκ in

theorem shortExactConeKernel_stable
    (A : H.X 0 →ₗ[R] CochainCokernel G) (t : RawSyzygy H →ₗ[R] CochainCokernel F)
    (hA : p.comp A = (LinearMap.range (H.d (-1) 0).hom).mkQ)
    (ht : (cochainCokernelMap φ).comp t = A.comp (rawSyzygyInclusion H)) :
    StableHom.classOf R _ _ (coneLiftKernel φ κ hi) = StableHom.classOf R _ _ t := by
  let := hH.finite 0
  let := hH.projective 0
  apply stable_connecting_congr (rawSyzygyInclusion H)
    (LinearMap.range (H.d (-1) 0).hom).mkQ (rawSyzygyInclusion_cover H)
    (cochainCokernelMap φ) p hi hp (LinearMap.exact_iff.mp he).symm
    ((rawConeQuotient φ p he).comp (cochainCokernelMap κ)) LinearMap.id
    (coneLiftMiddle φ κ) A (coneLiftKernel φ κ hi) t
  · exact coneLiftMiddle_square φ κ p he
  · simpa only [LinearMap.id_comp] using hA
  · exact coneLiftKernel_square φ κ hi
  · exact ht
  · exact shortExactConeInverse_stable_identity φ p he hF hG hH hi hp κ hκ

omit [Module.Injective R R] in
theorem coneProjectionCocycle_hom :
    Cocycle.equivHomShift.symm (cocycleProduct (Cocycle.ofHom κ) (mappingCone.fst φ)) =
      κ ≫ Cocycle.equivHomShift.symm (mappingCone.fst φ) := by
  apply HomologicalComplex.Hom.ext
  funext i
  rw [cocycleHom_component]
  change ((Cochain.ofHom κ).comp (mappingCone.fst φ).val rfl).v i (i+1) rfl = _
  rw [Cochain.comp_v _ _ rfl i i (i+1) (by omega) rfl, Cochain.ofHom_v]
  simp only [HomologicalComplex.comp_f, cocycleHom_component]

include hκ in

theorem shortExactConnecting_cone_class :
    fullHomShiftedHomotopyEquiv k H F 1
      (CohomologyClass.mk (cocycleProduct (Cocycle.ofHom κ) (mappingCone.fst φ))) =
      (shortExactTriangle φ p he hF hG hH hi hp).mor₃ := by
  have hn : -(mappingCone.fst φ) = mappingCone.fst φ := by
    apply neg_eq_iff_add_eq_zero.mpr
    rw [← two_smul k, show (2:k)=0 from CharP.cast_eq_zero k 2, zero_smul]
  rw [fullHomShiftedHomotopyEquiv_mk, coneProjectionCocycle_hom,
    Functor.map_comp, Category.assoc, hκ]
  change _ = (shortExactConeIso φ p he hF hG hH hi hp).inv ≫
    ((HomotopyCategory.quotient _ _).map
      (Cocycle.equivHomShift.symm (-(mappingCone.fst φ))) ≫
      ((HomotopyCategory.quotient _ _).commShiftIso (1:ℤ)).hom.app F)
  rw [hn]
  rfl

include k hκ in

theorem shortExactConnecting_source
    (A : H.X 0 →ₗ[R] CochainCokernel G) (t : RawSyzygy H →ₗ[R] CochainCokernel F)
    (hA : p.comp A = (LinearMap.range (H.d (-1) 0).hom).mkQ)
    (ht : (cochainCokernelMap φ).comp t = A.comp (rawSyzygyInclusion H)) :
    StableHom.classOf R _ _
      (rawSourceCocycleMap (cocycleProduct (Cocycle.ofHom κ) (mappingCone.fst φ))) =
        StableHom.classOf R _ _ t := by
  rw [rawSourceCocycleMap_cone (k := k) φ κ hi]
  exact shortExactConeKernel_stable φ p he hF hG hH hi hp κ hκ A t hA ht

theorem shortExactConnecting_source_equiv
    (A : H.X 0 →ₗ[R] CochainCokernel G) (t : RawSyzygy H →ₗ[R] CochainCokernel F)
    (hA : p.comp A = (LinearMap.range (H.d (-1) 0).hom).mkQ)
    (ht : (cochainCokernelMap φ).comp t = A.comp (rawSyzygyInclusion H)) :
    rawSourceStableEquiv (k := k) H F hH.to_chain hF.to_chain.toExactProjectiveComplex
      ((fullHomShiftedHomotopyEquiv k H F 1).symm
        (shortExactTriangle φ p he hF hG hH hi hp).mor₃) = StableHom.classOf R _ _ t := by
  obtain ⟨κ, hκ⟩ := Functor.map_surjective (HomotopyCategory.quotient _ _)
    (shortExactConeIso φ p he hF hG hH hi hp).inv
  rw [← shortExactConnecting_cone_class (k := k) φ p he hF hG hH hi hp κ hκ,
    LinearEquiv.symm_apply_apply, rawSourceStableEquiv_mk]
  exact shortExactConnecting_source (k := k) φ p he hF hG hH hi hp κ hκ A t hA ht

end ArExplicit

end

end OAI
