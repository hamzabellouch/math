import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.MetricAnchor
import OAI.Combinatorics.KMedianRecovery.Strictness.SurplusPostprocess

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricSurplus
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ h L : ℕ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryFinSet.encode D,BinaryFinSet.encode F,Δ.bits,h.bits,L.bits]
noncomputable def anchorInput (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 2 x,field 3 x,field 5 x]
noncomputable def anchorInput_computes : PolyComputes anchorInput := list_computes
  [field 0,field 1,field 2,field 3,field 5] (by
    intro f hf; refine Classical.choice ?_; simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl <;> exact ⟨field_computes _⟩)
noncomputable def rectangle : List Bool→List Bool := BinaryMetricAnchor.rectangle ∘ anchorInput
noncomputable def rectangle_computes : PolyComputes rectangle := anchorInput_computes.comp BinaryMetricAnchor.rectangle_computes
noncomputable def initial (x : List Bool) : List Bool := encode [rectangle x,Count.run (field 2 x),field 3 x,field 2 x,
  BinaryRational.natWords (field 4 x),field 5 x]
noncomputable def initial_computes : PolyComputes initial :=
  cons_computes rectangle_computes (cons_computes ((field_computes 2).comp Count.run_computes)
    (cons_computes (field_computes 3) (cons_computes (field_computes 2)
      (cons_computes ((field_computes 4).comp BinaryRational.natWords_computes)
        (cons_computes (field_computes 5) (const_computes []))))))
noncomputable def total (x : List Bool) : List Bool := (BinaryArithmetic.value (field 5 x)+BinaryArithmetic.value (field 6 x)).bits
noncomputable def total_computes : PolyComputes total := MetricKMedianRecovery.BitMachine.NatOps.add (field_computes 5) (field_computes 6)
noncomputable def runInput (x : List Bool) : List Bool := pairBits (initial x,total x)
noncomputable def runInput_computes : PolyComputes runInput := initial_computes.pair total_computes
noncomputable def run (v : ℚ) (C : ℕ) : List Bool→List Bool := BinaryCanonicalSurplus.run v C ∘ runInput
noncomputable def run_computes (v : ℚ) (C : ℕ) : PolyComputes (run v C) :=
  runInput_computes.comp (BinaryCanonicalSurplus.run_computes v C)
lemma anchorInput_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ h L : ℕ) :
    anchorInput (pack δ D F Δ h L)=BinaryMetricAnchor.pack δ D F h := by
  simp only [anchorInput,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryMetricAnchor.pack]
lemma rectangle_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ h L : ℕ) :
    rectangle (pack δ D F Δ h L)=Rectangular.encode (fun i j=>δ i (SortedIndex.enum D j)) := by
  rw [rectangle,Function.comp_apply,anchorInput_pack,BinaryMetricAnchor.rectangle_pack]
lemma runInput_pack (δ : Fin n→Fin n→ℕ) (D F : Finset (Fin n)) (Δ h L : ℕ) :
    runInput (pack (fun i j=>(δ i j:ℚ)) D F Δ h L)=BinaryCanonicalSurplus.pack (fun i j=>δ j i) F D Δ h L := by
  rw [runInput,initial,rectangle_pack]
  simp only [total,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryArithmetic.value_bits,BinaryRational.natWords_bits,BinaryFinSet.encode_eq,Count.run_encode,List.length_map,
    Finset.length_sort,BinaryCanonicalSurplus.pack,BinaryInitialAuto.pack]
  rw [←SortedIndex.map_enum D (fun i : Fin n=>i.val.bits)]
lemma run_pack (v : ℚ) (C : ℕ) (δ : Fin n→Fin n→ℕ) (D F : Finset (Fin n)) (Δ h L : ℕ) :
    run v C (pack (fun i j=>(δ i j:ℚ)) D F Δ h L)=
      BinaryCanonicalSurplus.run v C (BinaryCanonicalSurplus.pack (fun i j=>δ j i) F D Δ h L) := by
  rw [run,Function.comp_apply,runInput_pack]
end MetricKMedianRecovery.BitMachine.BinaryMetricSurplus

end OAI
