import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingRootProductBoxes
import OAI.NumberTheory.DukePrimeDegree.Geometry.ExtremalRemainingEntries

namespace OAI

/-! # The pivot domain contains whole remaining-group fibers -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates n q.processed T) (g : G n) (k : Fin n)

lemma factorBase_pivot_column (s : UpperRootTransverse n × T)
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    (C.factorBase q g (s,w)).val k q.root.1 =
      ((g * s.1.val) * C.base s.2).val k q.root.1 := by
  let v : positiveRootGeneratedGroup q.remaining :=
    ⟨w.val,positiveRootGeneratedGroup_mono (Finset.erase_subset _ _) w.prop⟩
  have hw : ∀ j, w.val.val j q.root.1 = if j = q.root.1 then 1 else 0 :=
    q.remaining_standard_column v
  change (g * (s.1.val * (C.base s.2 * w.val))).val k q.root.1 = _
  simp only [←mul_assoc]
  change ∑ j, ((g * s.1.val) * C.base s.2).val k j * w.val.val j q.root.1 = _
  simp [hw]

lemma factorPivotDomain_cylinder (s : UpperRootTransverse n × T)
    (hs : ((g * s.1.val) * C.base s.2).val k q.root.1 ≠ 0) :
    {s} ×ˢ (univ : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) ⊆
      C.factorPivotDomain q g k := by
  rintro ⟨u,w⟩ ⟨hu,_⟩
  have hu' : u = s := hu
  subst u
  change (C.factorBase q g (s,w)).val k q.root.1 ≠ 0
  rw [C.factorBase_pivot_column q g k]
  exact hs

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
