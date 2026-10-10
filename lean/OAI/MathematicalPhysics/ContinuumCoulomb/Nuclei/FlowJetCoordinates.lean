import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowPathEquation

namespace OAI

/-! Finite coordinates for spatial jets in dimension three. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb

abbrev SpatialJet (n : ℕ) := Position [×n]→L[ℝ] Position

def spatialJetCoordinates (n : ℕ) :
    SpatialJet n →ₗ[ℝ] ((Fin n → Fin 3) → Position) where
  toFun A e := A (fun i => NeutralAtom.axis (e i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem spatialJetCoordinates_injective (n : ℕ) :
    Function.Injective (spatialJetCoordinates n) := by
  intro A B h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear
    (fun _i : Fin n => (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
  intro e
  have he := congrFun h e
  change A (fun i => (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (e i)) =
    B (fun i => (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (e i))
  simpa only [spatialJetCoordinates,LinearMap.coe_mk,AddHom.coe_mk,
    OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,NeutralAtom.axis] using he

instance spatialJetFiniteDimensional (n : ℕ) : FiniteDimensional ℝ (SpatialJet n) :=
  FiniteDimensional.of_injective (spatialJetCoordinates n) (spatialJetCoordinates_injective n)

theorem spatialJet_hasDerivWithinAt (n : ℕ) (J : ℝ → SpatialJet n)
    (D : SpatialJet n) (s : Set ℝ) (t : ℝ) (ht : t ∈ s)
    (h : ∀ e : Fin n → Position, HasDerivWithinAt (fun u => J u e) (D e) s t) :
    HasDerivWithinAt J D s t := by
  let L := (spatialJetCoordinates n).toContinuousLinearMap
  have hL : Topology.IsEmbedding L :=
    ((spatialJetCoordinates n).isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr (spatialJetCoordinates_injective n))).isEmbedding
  have hd : HasDerivWithinAt (fun u => L (J u)) (L D) s t :=
    hasDerivWithinAt_pi.mpr (fun e => h (fun i => NeutralAtom.axis (e i)))
  have hc : ContinuousWithinAt J s t :=
    hL.isInducing.continuousWithinAt_iff.mpr hd.continuousWithinAt
  have hd' : HasFDerivWithinAt (fun u => L (J u))
      (L.comp ((1:ℝ →L[ℝ] ℝ).smulRight D)) s t := by
    convert hd.hasFDerivWithinAt using 1
    ext r
    simp
  simpa using (HasFDerivWithinAt.of_comp_of_isEmbedding
    (t := univ) (by rw [nhdsWithin_univ]; exact hc.tendsto)
    L.hasFDerivAt.hasFDerivWithinAt hL hd' (Eventually.of_forall (fun _ => rfl)) ht).hasDerivWithinAt

end ContinuumCoulomb

end

end OAI
