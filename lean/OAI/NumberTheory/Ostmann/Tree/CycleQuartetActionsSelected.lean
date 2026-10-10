import OAI.NumberTheory.Ostmann.Tree.CycleQuartetActions

namespace OAI

noncomputable section
namespace Ostmann.Tree.CycleQuartet
open Finset
variable {k b : ℕ} (P : LeafPartition (k+2) b)
  (c : BalancedSelection P.label (quartetCut k).label)

instance selectedQuartets_nonempty : Nonempty (cycleQuartets P c) :=
  (cycleQuartets_nonempty P c).coe_sort

theorem positive_fiber_card {v : Leaves k} (hv : v∈cycleQuartets P c) :
    (c.positive.filter (fun e => (quartetCut k).label e=v)).card=1 := by
  obtain ⟨e,he,hv'⟩ := mem_image.mp hv
  apply Nat.le_antisymm (c.right_bound v)
  exact Nat.succ_le_of_lt (card_pos.mpr ⟨e,mem_filter.mpr ⟨he,hv'⟩⟩)

theorem negative_fiber_card {v : Leaves k} (hv : v∈cycleQuartets P c) :
    (c.negative.filter (fun e => (quartetCut k).label e=v)).card=1 := by
  rw [←c.right_balance,positive_fiber_card P c hv]

theorem local_positive_existsUnique {v : Leaves k} (hv : v∈cycleQuartets P c) :
    ∃! w : Leaves 2,leaf k v w∈c.positive := by
  obtain ⟨e,he,huniq⟩ := card_eq_one_iff_existsUnique.mp (positive_fiber_card P c hv)
  obtain ⟨hep,hev⟩ := mem_filter.mp he
  have hleaf : leaf k v (tail k e)=e := by rw [←hev,leaf_quartetCut_label_tail]
  refine ⟨tail k e,by simpa only [hleaf] using hep,?_⟩
  intro w hw
  have heq := huniq (leaf k v w) (mem_filter.mpr ⟨hw,quartetCut_label_leaf k v w⟩)
  simpa only [tail_leaf] using congrArg (tail k) heq

theorem local_negative_existsUnique {v : Leaves k} (hv : v∈cycleQuartets P c) :
    ∃! w : Leaves 2,leaf k v w∈c.negative := by
  obtain ⟨e,he,huniq⟩ := card_eq_one_iff_existsUnique.mp (negative_fiber_card P c hv)
  obtain ⟨hep,hev⟩ := mem_filter.mp he
  have hleaf : leaf k v (tail k e)=e := by rw [←hev,leaf_quartetCut_label_tail]
  refine ⟨tail k e,by simpa only [hleaf] using hep,?_⟩
  intro w hw
  have heq := huniq (leaf k v w) (mem_filter.mpr ⟨hw,quartetCut_label_leaf k v w⟩)
  simpa only [tail_leaf] using congrArg (tail k) heq

def positivePosition (v : cycleQuartets P c) : Leaves 2 :=
  Classical.choose (local_positive_existsUnique P c v.property)

def negativePosition (v : cycleQuartets P c) : Leaves 2 :=
  Classical.choose (local_negative_existsUnique P c v.property)

theorem positive_mem_iff (v : cycleQuartets P c) (w : Leaves 2) :
    leaf k v.val w∈c.positive ↔ w=positivePosition P c v := by
  have h := Classical.choose_spec (local_positive_existsUnique P c v.property)
  exact ⟨fun hw => h.2 w hw,fun hw => hw ▸ h.1⟩

theorem negative_mem_iff (v : cycleQuartets P c) (w : Leaves 2) :
    leaf k v.val w∈c.negative ↔ w=negativePosition P c v := by
  have h := Classical.choose_spec (local_negative_existsUnique P c v.property)
  exact ⟨fun hw => h.2 w hw,fun hw => hw ▸ h.1⟩

theorem positions_distinct (v : cycleQuartets P c) :
    positivePosition P c v≠negativePosition P c v := by
  intro h
  have hp := (positive_mem_iff P c v (positivePosition P c v)).mpr rfl
  have hn := (negative_mem_iff P c v (negativePosition P c v)).mpr rfl
  rw [h] at hp
  exact disjoint_left.mp c.disjoint hp hn

def twoLeafAct {U : Type*} [CommGroup U] (u v : Leaves 2) (z : U)
    (M : Leaves 2 → U) : Leaves 2 → U := fun w =>
  (if w=u then z else 1)*(if w=v then z⁻¹ else 1)*M w

theorem localAct_eq_twoLeafAct {U : Type*} [CommGroup U]
    (v : cycleQuartets P c) (z : U) (M : Leaves 2 → U) :
    localAct P c v.val z M=twoLeafAct (positivePosition P c v) (negativePosition P c v) z M := by
  funext w
  simp only [localAct,twoLeafAct,BalancedSelection.twist,positive_mem_iff,negative_mem_iff]

theorem negative_label_mem {e : Leaves (k+2)} (he : e∈c.negative) :
    (quartetCut k).label e∈cycleQuartets P c := by
  have hn : 0<(c.negative.filter (fun x => (quartetCut k).label x=(quartetCut k).label e)).card :=
    card_pos.mpr ⟨e,mem_filter.mpr ⟨he,rfl⟩⟩
  rw [←c.right_balance] at hn
  obtain ⟨f,hf⟩ := card_pos.mp hn
  exact mem_image.mpr ⟨f,(mem_filter.mp hf).1,(mem_filter.mp hf).2⟩

theorem localAct_untouched {U : Type*} [CommGroup U] {v : Leaves k}
    (hv : v∉cycleQuartets P c) (z : U) (M : Leaves 2 → U) : localAct P c v z M=M := by
  funext w
  have hp : leaf k v w∉c.positive := by
    intro he
    apply hv
    exact mem_image.mpr ⟨leaf k v w,he,quartetCut_label_leaf k v w⟩
  have hn : leaf k v w∉c.negative := by
    intro he
    have hh := negative_label_mem P c he
    simp only [quartetCut_label_leaf] at hh
    exact hv hh
  simp [localAct,BalancedSelection.twist,hp,hn]

end Ostmann.Tree.CycleQuartet

end

end OAI
