import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelMember

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open Classical
open WordOperations WordList BinaryOpeningPayment RationalLeaves
open BinaryLabel (orderedSort)

def labels {m : ℕ} (xs : List (Label (Fin m))) : List Bool := encode (xs.map BinaryLabel.encode)
def setBits {m : ℕ} (S : Finset (Label (Fin m))) : List Bool := labels (orderedSort S)
def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,setBits F,setBits Q,
    labels (List.ofFn loc),BinaryRational.encode v,BinaryRational.encode z,BinaryRational.encode lam]
noncomputable def alphabet (x : List Bool) : List Bool :=
  BinaryLabel.sort (field 2 x++field 3 x++field 4 x)
noncomputable def alphabet_computes : PolyComputes alphabet :=
  (((field_computes 2).append (field_computes 3)).append (field_computes 4)).comp BinaryLabel.sort_computes
lemma alphabet_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    alphabet (pack distance loc F Q v z lam)=labels (FiniteLabelContinuation.alphabet loc F Q) := by
  simp only [alphabet,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [setBits,labels,←encode_append,←List.map_append,BinaryLabel.sort_encode]
  have hloc : (List.ofFn loc).toFinset = Finset.univ.image loc := by
    ext x
    simp only [List.mem_toFinset,List.mem_ofFn,Finset.mem_image,Finset.mem_univ,true_and]
  congr 2
  simp only [List.toFinset_append,orderedSort,Finset.sort_toFinset,hloc,FiniteLabelContinuation.alphabet]

noncomputable def selected (k : ℕ) (x : List Bool) : List Bool :=
  BinaryLabelSelect.run (pairBits (alphabet x,field k x))
noncomputable def selected_computes (k : ℕ) : PolyComputes (selected k) :=
  (alphabet_computes.pair (field_computes k)).comp BinaryLabelSelect.run_computes
lemma selected_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q S : Finset (Label (Fin m))) (v z lam : ℚ) (k : ℕ)
    (hk : field k (pack distance loc F Q v z lam)=setBits S) :
    selected k (pack distance loc F Q v z lam)=BinaryOpeningActivity.indices
      ((EffectiveOpenability.subtypeList (FiniteLabelContinuation.select loc F Q S)).map Subtype.val) := by
  rw [selected,alphabet_pack,hk]
  simp only [setBits,labels]
  rw [BinaryLabelSelect.run_pack]
  have hs : Finset.univ.filter (fun i : Fin (FiniteLabelContinuation.alphabet loc F Q).length =>
      (FiniteLabelContinuation.alphabet loc F Q).get i ∈ orderedSort S) = FiniteLabelContinuation.select loc F Q S := by
    ext i
    rw [Finset.mem_filter,FiniteLabelContinuation.mem_select]
    simp only [Finset.mem_univ,true_and,orderedSort,Finset.mem_sort]
    rfl
  rw [hs]

noncomputable def matrix (x : List Bool) : List Bool :=
  BinaryLabelMatrix.run (pairBits (pairBits (field 0 x,field 1 x),alphabet x))
attribute [local irreducible] BinaryLabelMatrix.run
noncomputable def matrix_computes : PolyComputes matrix :=
  (((field_computes 0).pair (field_computes 1)).pair alphabet_computes).comp BinaryLabelMatrix.run_computes
lemma matrix_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    matrix (pack distance loc F Q v z lam)=Rectangular.encode (FiniteLabelContinuation.rows loc F Q (rows distance)) := by
  rw [matrix,alphabet_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [labels,BinaryLabelMatrix.run_pack]
  rfl

noncomputable def run (x : List Bool) : List Bool := encode
  [matrix x,selected 3 x,field 5 x,field 6 x,field 7 x,BinaryRational.encode 0,[],field 1 x,selected 2 x]
attribute [local irreducible] matrix selected
noncomputable def run_computes : PolyComputes run :=
  list_computes [matrix,selected 3,field 5,field 6,field 7,(fun _=>BinaryRational.encode 0),(fun _=>[]),field 1,selected 2] (by
    intro f hf
    refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨matrix_computes⟩ | exact ⟨selected_computes _⟩ | exact ⟨field_computes _⟩ | exact ⟨const_computes _⟩)
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    run (pack distance loc F Q v z lam)=BinaryPhaseFirst.context
      (FiniteLabelContinuation.rows loc F Q (rows distance)) (FiniteLabelContinuation.select loc F Q F)
      (FiniteLabelContinuation.select loc F Q Q) v z lam := by
  rw [run,matrix_pack,selected_pack distance loc F Q Q v z lam 3 (by simp [pack,field_encode]),
    selected_pack distance loc F Q F v z lam 2 (by simp [pack,field_encode])]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryPhaseFirst.context]
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
