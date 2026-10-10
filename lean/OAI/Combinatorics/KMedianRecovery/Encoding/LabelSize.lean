import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FiniteContext

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList
lemma member_length {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) : w.length≤(encode ws).length := by
  induction ws with
  | nil=>exact False.elim (List.not_mem_nil hw)
  | cons v vs ih=>
    rw [encode,length_cons]
    rcases List.mem_cons.mp hw with rfl|hw
    · omega
    · have h:=ih hw
      omega
end MetricKMedianRecovery.BitMachine.WordList
namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordList RationalLeaves
lemma length_labels_le {pointCount : ℕ} (xs : List (Label (Fin pointCount))) : xs.length≤(labels xs).length := by
  simpa only [List.length_map,labels] using length_le_encode (xs.map BinaryLabel.encode)
lemma member_labels_length {pointCount : ℕ} {xs : List (Label (Fin pointCount))} {x : Label (Fin pointCount)} (hx : x∈xs) :
    (BinaryLabel.encode x).length≤(labels xs).length :=
  member_length (List.mem_map.mpr ⟨x,hx,rfl⟩)
lemma card_setBits_le {pointCount : ℕ} (S : Finset (Label (Fin pointCount))) : S.card≤(setBits S).length := by
  simpa only [setBits,BinaryLabel.orderedSort,Finset.length_sort] using length_labels_le (BinaryLabel.orderedSort S)
lemma member_setBits_length {pointCount : ℕ} {S : Finset (Label (Fin pointCount))} {x : Label (Fin pointCount)} (hx : x∈S) :
    (BinaryLabel.encode x).length≤(setBits S).length :=
  member_labels_length ((Finset.mem_sort _).mpr hx)
lemma labels_length_bounded {m r B : ℕ} (xs : List (Label (Fin m))) (hn : xs.length≤r)
    (hB : ∀ x∈xs,(BinaryLabel.encode x).length≤B) :
    (labels xs).length≤r*(2*B+2) := by
  have h:=encode_le_bound (xs.map BinaryLabel.encode) B (by
    intro w hw
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hw
    exact hB x hx)
  simp only [List.length_map] at h
  exact h.trans (Nat.mul_le_mul_right _ hn)
lemma pack_F_bound {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    (setBits F).length≤(pack distance loc F Q v z lam).length :=
  member_length (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
