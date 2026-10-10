import OAI.NumberTheory.Ostmann.Tree.CycleLocalMajorantsBasic
import OAI.NumberTheory.Ostmann.Tree.TensorActionProjection

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.FiniteField
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance cycleCoefficientCharDecEq : DecidableEq (MulChar F ℂ) := Classical.decEq _

theorem mellin_const_value (c : ℂ) (ρ : MulChar F ℂ) :
    mellin (fun _ : Fˣ => c) ρ = if ρ=1 then c else 0 := by
  classical
  unfold mellin
  rw [← Finset.mul_sum, ← map_sum, sum_units_mulChar]
  by_cases hρ : ρ=1 <;> simp [hρ]
  have hN : (Fintype.card Fˣ:ℂ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

end Ostmann.FiniteField
namespace Ostmann.Tree.CycleQuartet
open Quartet Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime]

theorem kind_fiber_bound (T : Diagram (ZMod p) 2) (g : ZMod p → ℂ) (hg0 : g 0=0)
    (κ : Kind) (m : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    Density.average (fun M : ProductFiber m =>
      ‖mellin (fun z : (ZMod p)ˣ => T.value g (κ.act z M.val)) ρ‖^2) ≤
      selectedMajorant T.parameters g κ ρ (T.localNode.familyRoot m) := by
  cases κ with
  | same side inverse =>
    have hm : selectedMajorant T.parameters g (.same side inverse) ρ (T.localNode.familyRoot m) =
        T.localNode.sameLocalMajorant g side (orientedCharacter inverse ρ) (T.localNode.familyRoot m) := by
      rw [← T.localNode_parameters, selectedMajorant_same_node]
    rw [hm]
    cases inverse
    · exact T.sameAction_fiber_bound g hg0 side m ρ
    · exact T.sameAction_inverse_fiber_bound g hg0 side m ρ
  | cross a b inverse =>
    have hm : selectedMajorant T.parameters g (.cross a b inverse) ρ (T.localNode.familyRoot m) =
        T.localNode.crossLocalMajorant g a b (orientedCharacter inverse ρ) (T.localNode.familyRoot m) := by
      rw [← T.localNode_parameters, selectedMajorant_cross_node]
    rw [hm]
    cases inverse
    · exact T.crossAction_fiber_bound g hg0 a b m ρ
    · exact T.crossAction_inverse_fiber_bound g hg0 a b m ρ

variable {k b : ℕ} (P : LeafPartition (k+2) b)
  (c : BalancedSelection P.label (quartetCut k).label)

def localMajorant (Qs : Leaves k → Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (v : Leaves k) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ := by
  classical
  exact if hv : v∈cycleQuartets P c then selectedMajorant (Qs v) g (kind P c ⟨v,hv⟩) ρ y
    else unselectedMajorant (Qs v) g ρ y

theorem localMajorant_selected (Qs : Leaves k → Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (v : Leaves k) (hv : v∈cycleQuartets P c) :
    localMajorant P c Qs g v = selectedMajorant (Qs v) g (kind P c ⟨v,hv⟩) := by
  funext ρ y
  simp only [localMajorant,hv,↓reduceDIte]

theorem localMajorant_unselected (Qs : Leaves k → Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (v : Leaves k) (hv : v∉cycleQuartets P c) :
    localMajorant P c Qs g v = unselectedMajorant (Qs v) g := by
  funext ρ y
  simp only [localMajorant,hv,↓reduceDIte]

theorem localMajorant_nonneg (Qs : Leaves k → Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (v : Leaves k) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    0≤ localMajorant P c Qs g v ρ y := by
  classical
  unfold localMajorant
  split_ifs
  · exact selectedMajorant_nonneg _ _ _ _ _
  · exact unselectedMajorant_nonneg _ _ _ _

theorem localMajorant_mean_small (Qs : Leaves k → Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (v : Leaves k) (hv : v∈cycleQuartets P c) (ρ : MulChar (ZMod p) ℂ)
    (hg0 : g 0=0) (hg : l2Sq g≤1) :
    unitMean (localMajorant P c Qs g v ρ)≤25600*treeError g := by
  classical
  rw [localMajorant_selected P c Qs g v hv]
  exact selectedMajorant_mean_small _ _ _ _ hg0 hg

theorem localMajorant_mean_total (Qs : Leaves k → Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (v : Leaves k) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    (∑ ρ : MulChar (ZMod p) ℂ,unitMean (localMajorant P c Qs g v ρ))≤256 := by
  classical
  by_cases hv : v∈cycleQuartets P c
  · rw [localMajorant_selected P c Qs g v hv]
    exact selectedMajorant_mean_total _ _ _ hg0 hg
  · rw [localMajorant_unselected P c Qs g v hv]
    exact unselectedMajorant_mean_total _ _ hg0 hg

theorem localAct_fiber_bound (Qs : Leaves k → Parameters (ZMod p) 2)
    (T : Diagram (ZMod p) 2) (v : Leaves k) (hparams : T.parameters=Qs v)
    (g : ZMod p → ℂ) (hg0 : g 0=0) (m : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    Density.average (fun M : ProductFiber m =>
      ‖mellin (fun z : (ZMod p)ˣ => T.value g (localAct P c v z M.val)) ρ‖^2) ≤
      localMajorant P c Qs g v ρ (T.localNode.familyRoot m) := by
  classical
  by_cases hv : v∈cycleQuartets P c
  · simp only [localMajorant,hv,↓reduceDIte,← hparams]
    have ha (z : (ZMod p)ˣ) (M : Leaves 2 → (ZMod p)ˣ) :
        localAct P c v z M=(kind P c ⟨v,hv⟩).act z M := localAct_eq_kind P c ⟨v,hv⟩ z M
    simp_rw [ha]
    exact kind_fiber_bound T g hg0 _ m ρ
  · simp only [localMajorant,hv,↓reduceDIte,← hparams]
    simp_rw [localAct_untouched P c hv, mellin_const_value]
    have hm := unselectedMajorant_node T.localNode g ρ (T.localNode.familyRoot m)
    rw [T.localNode_parameters] at hm
    rw [hm]
    by_cases hρ : ρ=1
    · simp only [hρ,ite_true]
      exact T.untouched_fiber_bound g hg0 m
    · simp [hρ,Density.average]

def fiberValues (Ts : Leaves k → Diagram (ZMod p) 2) (g : ZMod p → ℂ)
    (totals : Leaves k → (ZMod p)ˣ) : (v : Leaves k) → ProductFiber (totals v) → ℂ :=
  fun v M => (Ts v).value g M.val

theorem actionCoefficient_fiber_bound (Qs : Leaves k → Parameters (ZMod p) 2)
    (Ts : Leaves k → Diagram (ZMod p) 2) (hparams : ∀v,(Ts v).parameters=Qs v)
    (g : ZMod p → ℂ) (hg0 : g 0=0) (totals : Leaves k → (ZMod p)ˣ)
    (v : Leaves k) (ρ : MulChar (ZMod p) ℂ) :
    letI : ∀v,MulAction (ZMod p)ˣ (ProductFiber (totals v)) := fun v => fiberMulAction P c v (totals v)
    Density.average (fun M : ProductFiber (totals v) =>
      ‖actionCoefficient (fiberValues Ts g totals) v ρ M‖^2) ≤
      localMajorant P c Qs g v ρ ((Ts v).localNode.familyRoot (totals v)) := by
  let : ∀v,MulAction (ZMod p)ˣ (ProductFiber (totals v)) := fun v => fiberMulAction P c v (totals v)
  change Density.average (fun M : ProductFiber (totals v) =>
    ‖mellin (fun z : (ZMod p)ˣ => (Ts v).value g (localAct P c v z M.val)) ρ‖^2) ≤ _
  exact localAct_fiber_bound P c Qs (Ts v) v (hparams v) g hg0 (totals v) ρ

end Ostmann.Tree.CycleQuartet
end

end OAI
