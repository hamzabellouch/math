import OAI.NumberTheory.Ostmann.Tree.CycleFiberProjection
import OAI.NumberTheory.Ostmann.Tree.CycleLocalMajorantsFrames
import OAI.NumberTheory.Ostmann.Tree.HorizontalProjectionBound
import OAI.NumberTheory.Ostmann.Tree.TensorActionMajorization
import OAI.NumberTheory.Ostmann.Tree.TreeMajorant

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators
open Ostmann.FiniteField QuartetFactorization CycleQuartet Density
variable {p : ℕ} [Fact p.Prime] {k b : ℕ}
local instance treeFiberMajorizationFintype : Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _
local instance treeFiberMajorizationDecEq : DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _
local instance treeFiberProductFintype {m : (ZMod p)ˣ} : Fintype (ProductFiber m) := Fintype.ofFinite _

theorem treeProjection_fiber_bound (P : LeafPartition (k+2) b)
    (c : BalancedSelection P.label (quartetCut k).label)
    (T : Diagram (ZMod p) (k+2)) (g : ZMod p → ℂ) (hg0 : g 0=0)
    (M : Leaves (k+2) → (ZMod p)ˣ) :
    realFiberAverage (bottomCut k).project (fun N => ‖c.projection (T.value g) N‖^2)
      ((bottomCut k).project M) ≤
      integrate (treeMajorant P c T g) (diagramLevelArguments (bottomCut k) T M) := by
  classical
  rw [diagramLevelArguments_eq_frameArguments]
  cases h : ancestorFrames T M with
  | none =>
    change realFiberAverage (bottomCut k).project _ ((bottomCut k).project M)≤0
    have hz := CycleFiberProjection.projection_energy_zero_of_invalid P c T g
      ((bottomCut k).project M) h
    exact le_of_eq hz
  | some fs =>
    let totals := (bottomCut k).project M
    let Ts : Leaves k → Diagram (ZMod p) 2 := fun v => frameDiagram T M fs h v
    let : ∀v,MulAction (ZMod p)ˣ (ProductFiber (totals v)) :=
      fun v => fiberMulAction P c v (totals v)
    have hb (v : Leaves k) (ρ : MulChar (ZMod p) ℂ) :
        average (fun x : ProductFiber (totals v) =>
          ‖actionCoefficient (fiberValues Ts g totals) v ρ x‖^2) ≤
        localMajorant P c (bottomParameters k T.parameters) g v ρ
          ((fs v).argument T.denominator (totals v)) := by
      have hv := frame_actionCoefficient_bound P c T M fs h g hg0 v ρ
      simpa only [real_average_fintype_congr _
        (inferInstance : Fintype (ProductFiber (totals v)))] using hv
    have hm := actionProjection_energy_le (fiberValues Ts g totals)
      (fun v ρ => localMajorant P c (bottomParameters k T.parameters) g v ρ
        ((fs v).argument T.denominator (totals v))) hb
    have he := CycleFiberProjection.projection_energy_on_fiber P c T g totals fs h
    change realFiberAverage (bottomCut k).project _ totals ≤
      treeMajorant P c T g (fun v => (fs v).argument T.denominator (totals v))
    have he' : realFiberAverage (bottomCut k).project
        (fun N => ‖c.projection (T.value g) N‖^2) totals =
        average (fun m : ∀ v, ProductFiber (totals v) =>
          ‖CycleFiberProjection.fiberProjection P c totals fs g T.denominator m‖^2) := by
      simpa only [realFiberAverage, real_average_fintype_congr _
        (inferInstance : Fintype {N : Leaves (k+2) → (ZMod p)ˣ // (bottomCut k).project N=totals}),
        real_average_fintype_congr _ (inferInstance : Fintype (∀ v, ProductFiber (totals v)))] using he
    rw [he']
    convert hm using 1
    · congr 1
    · unfold treeMajorant constrainedMajorant
      simp only [Equiv.refl_apply]
      congr 1
      funext ρ
      split_ifs <;> congr 1

end
end Ostmann.Tree

end OAI
