import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedRawPacking
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedThirdSites
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedYYReduction

namespace OAI

/-! Ordered sparse site/letter arrays.  Every word carries the already
proved support list; the bounded gadget operations inspect at most six
letters, and retain the original order even for identity letters. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open scoped BigOperators Classical

abbrev Letter := QuantumOrderedRawPacking.Letter

def tag {ι : Type} (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) : List Letter :=
  xs.map (fun i => (index i,(w i).val))

def partition (xs : List Letter) : List Letter × List Letter :=
  match xs with
  | [a,b,c] => if a.2=2 then
      if b.2=2 then ([a,b],[c]) else ([a,c],[b])
    else ([b,c],[a])
  | _ => (xs,[])

def yCount (xs : List Letter) : ℕ := (xs.filter (fun a => a.2=2)).length

def axis (xs : List Letter) : ℕ := if Odd (yCount xs) then 2 else 1

theorem tag_length {ι : Type} (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    (tag index xs w).length=xs.length := List.length_map _

theorem tag_take {ι : Type} (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) (d : ℕ) :
    tag index (xs.take d) w = (tag index xs w).take d := by
  simp only [tag,List.map_take]

theorem tag_drop {ι : Type} (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) (d : ℕ) :
    tag index (xs.drop d) w = (tag index xs w).drop d := by
  simp only [tag,List.map_drop]

theorem partition_tag {ι : Type} (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4) :
    partition (tag index xs w) =
      (tag index (QuantumOrderedTriple.partition xs w).1 w,
        tag index (QuantumOrderedTriple.partition xs w).2 w) := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      cases xs with
      | nil => rfl
      | cons c xs =>
        cases xs with
        | cons d xs => rfl
        | nil =>
          have ha : (w a).val=2 ↔ w a=2 := by
            constructor
            · intro h; exact Fin.ext h
            · intro h; exact congrArg Fin.val h
          have hb : (w b).val=2 ↔ w b=2 := by
            constructor
            · intro h; exact Fin.ext h
            · intro h; exact congrArg Fin.val h
          simp only [tag,List.map_cons,List.map_nil,partition,ha,hb,
            QuantumOrderedTriple.partition]
          split_ifs <;> rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem yCount_tag (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4)
    (hx : xs.Nodup) (hw : qmaPauliSupport w ⊆ xs.toFinset) :
    yCount (tag index xs w)=qmaPauliYCount w := by
  have hfilter : (xs.filter (fun i => w i=2)).toFinset =
      Finset.univ.filter (fun i => w i=2) := by
    ext i
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_filter,
      Finset.mem_univ,true_and,decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨List.mem_toFinset.mp (hw (by simp [qmaPauliSupport,h])),h⟩
  have hcount := List.toFinset_card_of_nodup (hx.filter (fun i => w i=2))
  rw [hfilter] at hcount
  unfold yCount tag
  rw [List.filter_map]
  have hv : (fun i : ι => decide ((w i).val=2)) = (fun i => decide (w i=2)) := by
    funext i
    congr 1
    exact propext ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  simp only [Function.comp_def,hv,List.length_map]
  exact hcount.symm

omit [Fintype ι] in
theorem tag_restrict (index : ι → ℕ) (xs : List ι) (w : ι → Fin 4)
    (ys : List ι) (hys : ∀ i ∈ xs, i ∈ ys) :
    tag index xs (qmaPauliRestrict ys.toFinset w)=tag index xs w := by
  apply List.map_congr_left
  intro i hi
  simp only [qmaPauliRestrict,List.mem_toFinset.mpr (hys i hi),ite_true]

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
