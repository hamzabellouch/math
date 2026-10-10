import Mathlib
import OAI.Combinatorics.UniformKServer.LevelMap
import OAI.Combinatorics.UniformKServer.CausalTier
import OAI.Combinatorics.UniformKServer.CausalHeavy

namespace OAI

                                  
section

/-! Causal dependence of the actual level keys and all their occupied anchors. -/
noncomputable section
namespace UniformKServer.CausalRosters
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

lemma tier_anchor (a : X) (r : ℝ) (K : ℕ) (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i)
    (l : TierLabeledKeys.Slot X K) :
    TierLabeledKeys.anchor a r K q c t l=TierLabeledKeys.anchor a r K v d t l := by
  unfold TierLabeledKeys.anchor
  simp only [reserved r K q v c d t hq hc,labels r K q v c d t hq hc]
  split_ifs with he
  · exact hc _ (TierSchedule.index_lt r K v d t _ (mem_filter.mp (Classical.choose_spec he).1).1)
  · rfl

end UniformKServer.CausalRosters
namespace UniformKServer.LevelMap.Data
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

def inputs (D : LevelMap.Data X N H) (c : Fin N → X) (h : Fin N → Prop)
    (q : Fin H → Fin N → Prop) : LevelMap.Data X N H :=
  { D with center := c, heavy := h, qualify := q }

lemma point_inputs (D : LevelMap.Data X N H) (c d : Fin N → X)
    (h v : Fin N → Prop) (q u : Fin H → Fin N → Prop) (t : ℕ)
    (hc : ∀ i : Fin N, i.val<t → c i=d i) (j : ℕ) (hj : j<t) :
    (D.inputs c h q).point j=(D.inputs d v u).point j := by
  unfold point inputs
  split_ifs with hn
  · exact hc ⟨j,hn⟩ hj
  · rfl

lemma heavy_inputs (D : LevelMap.Data X N H) (c d : Fin N → X)
    (h v : Fin N → Prop) (q u : Fin H → Fin N → Prop) (t : ℕ)
    (hc : ∀ i : Fin N, i.val<t → c i=d i) (hh : ∀ i : Fin N, i.val<t → (h i ↔ v i))
    (ω : LevelMap.HeavyTape D) :
    (D.inputs c h q).heavyState ω t=(D.inputs d v u).heavyState ω t := by
  apply HeavyProcess.run_inputs
  · intro j hj
    simp only [heavyFlag,inputs]
    apply exists_congr
    intro hjN
    exact hh ⟨j,hjN⟩ hj
  · exact fun j hj => point_inputs D c d h v q u t hc j hj

lemma key_inputs (D : LevelMap.Data X N H) (c d : Fin N → X)
    (h v : Fin N → Prop) (q u : Fin H → Fin N → Prop) (t : ℕ)
    (hc : ∀ i : Fin N, i.val<t → c i=d i) (hh : ∀ i : Fin N, i.val<t → (h i ↔ v i))
    (hq : ∀ a (i : Fin N), i.val<t → (q a i ↔ u a i))
    (is : List (Fin H)) (ω : LevelMap.Tape D) (p : X) :
    (D.inputs c h q).key is ω t p=(D.inputs d v u).key is ω t p := by
  unfold key heavyKey
  rw [heavy_inputs D c d h v q u t hc hh ω.1]
  have ht : (fun i => (D.inputs c h q).tierKey ω t i p)=
      (fun i => (D.inputs d v u).tierKey ω t i p) := by
    funext i
    unfold tierKey inputs
    rw [CausalRosters.labeled_inputs D.r (D.K i) (q i) (u i) c d t (hq i) hc]
  rw [ht]
  rfl

lemma anchor_inputs (D : LevelMap.Data X N H) (c d : Fin N → X)
    (h v : Fin N → Prop) (q u : Fin H → Fin N → Prop) (t : ℕ)
    (hc : ∀ i : Fin N, i.val<t → c i=d i) (hh : ∀ i : Fin N, i.val<t → (h i ↔ v i))
    (hq : ∀ a (i : Fin N), i.val<t → (q a i ↔ u a i))
    (ω : LevelMap.Tape D) (l : LevelMap.Label D) :
    (D.inputs c h q).anchor ω t l=(D.inputs d v u).anchor ω t l := by
  rcases l with l|⟨i,l⟩|p
  · change ((D.inputs c h q).heavyState ω.1 t).center l=_
    rw [heavy_inputs D c d h v q u t hc hh ω.1]
    rfl
  · exact CausalRosters.tier_anchor D.base D.r (D.K i) (q i) (u i) c d t (hq i) hc l
  · rfl

end UniformKServer.LevelMap.Data

end


end

end OAI
