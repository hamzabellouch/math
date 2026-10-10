import OAI.Analysis.CircleDomains.Selection.AppendingPairData

namespace OAI

/-! Finite test families and the actual appending transition. The two new
coordinates occupy positions zero and one; every previous coordinate is
retained after the proved small flattening. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

structure FiniteCompactTests (G : Set Sphere) where
  count : ℕ
  test : Fin count → EuclideanPlane → ℝ
  continuous : ∀ i, Continuous (test i)
  compact : ∀ i, HasCompactSupport (test i)
  witness : ∀ i, DeGiorgi.MemW1pWitness 2 (test i) (physicalPlaneDomain G)
  pair_null : ∀ i j, i ≠ j → volume ((fun x =>
    (sphereFromPlaneFunction (test i) x,sphereFromPlaneFunction (test j) x)) '' Gᶜ) = 0

 def AppendingPairData.toTestFamily
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {a δ η : ℝ} (D : AppendingPairData G u Wold a δ η) : FiniteCompactTests G where
  count := m+2
  test := appendScalarPair D.old D.p D.q
  continuous := Fin.cases D.q_continuous (Fin.cases D.p_continuous D.old_continuous)
  compact := Fin.cases D.q_compact (Fin.cases D.p_compact D.old_compact)
  witness := Fin.cases D.q_witness (Fin.cases D.p_witness D.old_witness)
  pair_null := D.pair_null

 theorem AppendingPairData.retains_old
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {a δ η : ℝ} (D : AppendingPairData G u Wold a δ η) (i : Fin m) :
    (∀ x, |D.toTestFamily.test i.succ.succ x-u i x| < δ) ∧
      (eLpNorm (fun x => (D.toTestFamily.witness i.succ.succ).weakGrad x-(Wold i).weakGrad x) 2
        (volume.restrict (physicalPlaneDomain G))).toReal < δ :=
  ⟨D.old_close i,D.old_error i⟩

 def FiniteCompactTests.singleton {G : Set Sphere} (u : EuclideanPlane → ℝ)
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u (physicalPlaneDomain G)) : FiniteCompactTests G where
  count := 1
  test := fun _ => u
  continuous := fun _ => hu
  compact := fun _ => hs
  witness := fun _ => W
  pair_null := fun i j hij => (hij (Subsingleton.elim i j)).elim

/-- This finite appending supply is a derived theorem of the published
inputs, never introduced as an additional published assumption. -/
 def FiniteAppendingSupply (G : Set Sphere) (a : ℝ) : Prop :=
  ∀ T : FiniteCompactTests G, ∀ δ η : ℝ, 0 < δ → 0 < η →
    Nonempty (AppendingPairData G T.test T.witness a δ η)

end CircleDomainRigidity

end

end OAI
