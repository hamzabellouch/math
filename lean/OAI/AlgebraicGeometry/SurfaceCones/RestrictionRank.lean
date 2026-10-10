import OAI.AlgebraicGeometry.SurfaceCones.ScalarPullback

namespace OAI

/-! The K₀ lattice identity identifies the rank of the restricted pushforward with the free lattice rank. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace ActualCartier
open CoherentGlobal ActualSheafTensor CartierImageFiltration
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f] [CompactSpace Y]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsClosedImmersion f] [CompactSpace Y] in
lemma coherentPower_obj (n : ℕ) (B : Coh Y) :
    ((power (coherentTensorLine (idealSheaf f) d) n).obj B).obj =
      (power (tensorLeft Y.sheaf (idealSheaf f)) n).obj B.obj := by
  induction n generalizing B with
  | zero => rfl
  | succ n ih => exact ih ((coherentTensorLine (idealSheaf f) d).obj B)

def clearedCoherentPowerIso (n : ℕ) (B : Coh Y) :
    letI := B.property
    clearedLattice f d n B.obj ≅ (power (coherentTensorLine (idealSheaf f) d) n).obj B :=
  ObjectProperty.isoMk _ (eqToIso (coherentPower_obj f d n B).symm)
end ActualCartier

namespace SourceConeMorphism
open KummerSourceModel SourcePullbackChart SourceZeroSections CoherentGlobal ActualCartier
  ActualSheafTensor CartierImageFiltration CoherentK0
attribute [local instance] originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra
  planeChart_noetherian ExplicitCone.projectiveNormalization_finite

lemma plane_rankHom_conormal (i : Fin 3) (B : Coh ExplicitCone.plane) :
    CoherentChartRank.rankHom (planeIota i)
      (cls (conormalTensor completedPlaneZero planeIdealLine B) - cls B) = 0 := by
  rw [map_sub, CoherentChartRank.rankHom_cls, CoherentChartRank.rankHom_cls]
  change (planeChartRank ((conormalFunctor completedPlaneZero planeIdealLine).obj B) i : ℤ) -
    (planeChartRank B i : ℤ) = 0
  rw [planeConormal_rank, sub_self]

lemma restriction_cleared_rank (B : Coh V) (n : ℕ) (i : Fin 3) :
    let := B.property
    planeChartRank ((restriction completedPlaneZero planeIdealLine).obj
      (clearedLattice completedPlaneZero planeIdealLine n B.obj)) i =
      planeChartRank ((restriction completedPlaneZero planeIdealLine).obj B) i := by
  let := B.property
  let e := (restriction completedPlaneZero planeIdealLine).mapIso
    (clearedCoherentPowerIso completedPlaneZero planeIdealLine n B) ≪≫
      restriction_powerIso completedPlaneZero planeIdealLine n B
  exact (CoherentChartRank.chart_iso_rank (planeIota i) e).trans
    (planeConormalPower_rank _ i n)

namespace ExtensionState
variable {M : ModuleCat.{0} ExplicitCone.completedRing}
  [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
  (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3)

lemma restriction_pushforward_rank (B : ExtensionState M) (i : Fin 3) :
    planeChartRank ((restriction completedPlaneZero planeIdealLine).obj B.pushforward) i =
      sourceFreeRank M hdepth := by
  obtain ⟨k, hk⟩ := B.exists_free_lattice hdepth
  obtain ⟨a, _, _, _, hc, _⟩ := hk k le_rfl
  have H := congrArg (CoherentChartRank.rankHom (planeIota i)) hc
  simp only [map_add, map_list_sum, List.map_map] at H
  have Hz : ((idealLayers completedPlaneZero planeIdealLine (k + k) (cokernel a)).map
      (fun Q => CoherentChartRank.rankHom (planeIota i)
        (cls (conormalTensor completedPlaneZero planeIdealLine Q) - cls Q))).sum = 0 := by
    simp only [plane_rankHom_conormal, List.map_const', List.sum_replicate, nsmul_zero]
  change _ = _ + ((idealLayers completedPlaneZero planeIdealLine (k + k) (cokernel a)).map
      (fun Q => CoherentChartRank.rankHom (planeIota i)
        (cls (conormalTensor completedPlaneZero planeIdealLine Q) - cls Q))).sum at H
  rw [Hz, add_zero, CoherentChartRank.rankHom_cls, CoherentChartRank.rankHom_cls] at H
  change (planeChartRank _ i : ℤ) = (planeChartRank (coherentFree ExplicitCone.plane
    (Fin (sourceFreeRank M hdepth))) i : ℤ) at H
  rw [restriction_cleared_rank, planeFree_rank] at H
  exact_mod_cast H

lemma finite_pushforward_rank (B : ExtensionState M) (i : Fin 3) :
    planeChartRank ((cohPushforward ExplicitCone.projectiveNormalization).obj
      (sourceRestriction.obj B.sheaf)) i = sourceFreeRank M hdepth := by
  exact (CoherentChartRank.chart_iso_rank (planeIota i) B.restrictionPushforwardIso).symm.trans
    (B.restriction_pushforward_rank hdepth i)
end ExtensionState
end SourceConeMorphism

end

end OAI
