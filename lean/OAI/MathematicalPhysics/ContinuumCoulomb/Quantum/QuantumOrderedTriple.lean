import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSplit
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliTripleSplit

namespace OAI

/-! A deterministic three-site partition for the third-order gadget.
For three sites the last factor is the first available non-Y letter;
shorter lists give an empty last factor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedTriple
open scoped Classical
variable {ι : Type}

def partition (xs : List ι) (w : ι → Fin 4) : List ι × List ι :=
  match xs with
  | [a,b,c] => if w a = 2 then
      if w b = 2 then ([a,b],[c]) else ([a,c],[b])
    else ([b,c],[a])
  | _ => (xs,[])

theorem partition_spec (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3) :
    ((partition xs w).1++(partition xs w).2).Perm xs ∧
      (partition xs w).1.length ≤ 2 ∧ (partition xs w).2.length ≤ 1 := by
  cases xs with
  | nil => simp [partition]
  | cons a xs =>
    cases xs with
    | nil => simp [partition]
    | cons b xs =>
      cases xs with
      | nil => simp [partition]
      | cons c xs =>
        cases xs with
        | nil =>
          by_cases ha : w a = 2
          · by_cases hb : w b = 2
            · simp [partition,ha,hb]
            · refine ⟨?_,by simp [partition,ha,hb]⟩
              simpa [partition,ha,hb] using
                (List.Perm.cons a (List.perm_append_comm (l₁ := [c]) (l₂ := [b])))
          · refine ⟨?_,by simp [partition,ha]⟩
            simpa [partition,ha] using (List.perm_append_comm (l₁ := [b,c]) (l₂ := [a]))
        | cons d xs => simp at hlen; omega

theorem partition_nodup (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) : ((partition xs w).1++(partition xs w).2).Nodup :=
  (partition_spec xs w hlen).1.nodup_iff.mpr hx

theorem pair_nodup (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) : (partition xs w).1.Nodup :=
  (partition_nodup xs w hlen hx).of_append_left

variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem partition_cover (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3) :
    (partition xs w).1.toFinset ∪ (partition xs w).2.toFinset = xs.toFinset := by
  rw [← List.toFinset_append]
  ext i
  simp only [List.mem_toFinset]
  exact (partition_spec xs w hlen).1.mem_iff

omit [Fintype ι] in
theorem partition_disjoint (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) :
    Disjoint (partition xs w).1.toFinset (partition xs w).2.toFinset :=
  List.disjoint_toFinset_iff_disjoint.mpr
    (List.disjoint_of_nodup_append (partition_nodup xs w hlen hx))

private theorem not_three_y (a b c : ι) (w : ι → Fin 4)
    (hx : [a,b,c].Nodup) (hcover : qmaPauliSupport w ⊆ [a,b,c].toFinset)
    (he : Even (qmaPauliYCount w)) : ¬(w a = 2 ∧ w b = 2 ∧ w c = 2) := by
  rintro ⟨ha,hb,hc⟩
  have hs : Finset.univ.filter (fun i => w i = 2) = [a,b,c].toFinset := by
    ext i
    constructor
    · intro hi
      have hy := (Finset.mem_filter.mp hi).2
      exact hcover (by simp [qmaPauliSupport,hy])
    · intro hi
      have hi' : i = a ∨ i = b ∨ i = c := by simpa using hi
      rcases hi' with rfl | rfl | rfl <;> simp [ha,hb,hc]
  have hcount : qmaPauliYCount w = 3 := by
    rw [qmaPauliYCount,hs,List.toFinset_card_of_nodup hx]
    rfl
  rw [hcount] at he
  norm_num at he

theorem real_part (xs : List ι) (w : ι → Fin 4) (hlen : xs.length ≤ 3)
    (hx : xs.Nodup) (hcover : qmaPauliSupport w ⊆ xs.toFinset)
    (he : Even (qmaPauliYCount w)) : ∀ i ∈ (partition xs w).2, w i ≠ 2 := by
  cases xs with
  | nil => simp [partition]
  | cons a xs =>
    cases xs with
    | nil => simp [partition]
    | cons b xs =>
      cases xs with
      | nil => simp [partition]
      | cons c xs =>
        cases xs with
        | nil =>
          by_cases ha : w a = 2
          · by_cases hb : w b = 2
            · have hc : w c ≠ 2 := fun hc => not_three_y a b c w hx hcover he ⟨ha,hb,hc⟩
              simp [partition,ha,hb,hc]
            · simp [partition,ha,hb]
          · simp [partition,ha]
        | cons d xs => simp at hlen; omega

end ContinuumCoulomb.QuantumOrderedTriple

end

end OAI
