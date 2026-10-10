import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.SortedDual
import OAI.Combinatorics.KMedianRecovery.Geometry.LocalFuel
import OAI.Combinatorics.KMedianRecovery.Machines.ProjectionMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricAnchor
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryLocalAnchor.run BinaryProjection.run BinaryMetricArrays.run
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (r : ℕ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryFinSet.encode D,BinaryFinSet.encode F,r.bits]
noncomputable def rectInput (x : List Bool) : List Bool := encode
  [field 0 x,BinaryEllipsoidInitial.indices (field 1 x),field 2 x]
noncomputable def rectInput_computes : PolyComputes rectInput :=
  cons_computes (field_computes 0) (cons_computes ((field_computes 1).comp BinaryEllipsoidInitial.indices_computes)
    (cons_computes (field_computes 2) (const_computes [])))
noncomputable def rectangle : List Bool→List Bool := BinaryMetricArrays.run ∘ rectInput
noncomputable def rectangle_computes : PolyComputes rectangle := rectInput_computes.comp BinaryMetricArrays.run_computes
noncomputable def anchorInput (x : List Bool) : List Bool := encode [rectangle x,Count.run (field 2 x),
  map BinaryProjection.originalWord (field 3 x),field 4 x]
attribute [local irreducible] WordList.map
noncomputable def anchorInput_computes : PolyComputes anchorInput :=
  cons_computes rectangle_computes (cons_computes ((field_computes 2).comp Count.run_computes)
    (cons_computes (PolyComputes.comp (f := field 3) (g := map BinaryProjection.originalWord)
      (field_computes 3) (map_computes BinaryProjection.originalWord_computes))
      (cons_computes (field_computes 4) (const_computes []))))
noncomputable def run : List Bool→List Bool := BinaryProjection.run ∘ BinaryLocalAnchor.run ∘ anchorInput
noncomputable def run_computes : PolyComputes run :=
  anchorInput_computes.comp (BinaryLocalAnchor.run_computes.comp BinaryProjection.run_computes)
attribute [local semireducible] WordList.map
lemma rectInput_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (r : ℕ) :
    rectInput (pack δ D F r)=BinaryMetricArrays.pack δ id (SortedIndex.enum D) := by
  simp only [rectInput,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryEllipsoidInitial.indices_replicate,BinaryMetricArrays.pack,BinaryFinSet.table_enum]
  rfl
lemma rectangle_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (r : ℕ) :
    rectangle (pack δ D F r)=Rectangular.encode (fun i j=>δ i (SortedIndex.enum D j)) := by
  rw [rectangle,Function.comp_apply,rectInput_pack,BinaryMetricArrays.run_pack]
  rfl
lemma anchorInput_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (r : ℕ) :
    anchorInput (pack δ D F r)=BinaryLocalAnchor.pack (fun i j=>δ i (SortedIndex.enum D j)) (F.sort (·≤·)) r := by
  rw [anchorInput,rectangle_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFinSet.encode_eq,Count.run_encode,List.length_map,Finset.length_sort,map_encode,List.map_map,
    BinaryLocalAnchor.pack,BinaryFiniteContext.labels,List.map_map]
  rfl
lemma produce [MetricSpace (Fin n)] (δ : Fin n→Fin n→ℕ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F : Finset (Fin n)) (r : ℕ) (hr : 0<r) (hrF : r≤F.card)
    (hcap : ∀ p∈D,∀ i∈F,δ p i≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    ∃ S : Finset (Fin n),run (pack (fun i j=>(δ i j:ℚ)) D F r)=BinaryFinSet.encode S ∧
      S⊆F ∧ S.Nonempty ∧ S.card=r ∧ LocalSearch.WidthLocalMin F D S 5 ∧
      ∀ O : Finset (Fin n),O.Nonempty→O⊆F→O.card≤r→LocalSearch.cost D S≤5*LocalSearch.cost D O := by
  have hsymm (i j : Fin n) : δ i j=δ j i := by
    exact_mod_cast ((hδ i j).trans ((dist_comm i j).trans (hδ j i).symm))
  obtain ⟨S,he,hSF,hS,hcard,hlocal,hcost⟩:=BinaryLocalAnchor.integral_spec (fun i j=>δ j i) (SortedIndex.enum D)
    (SortedIndex.enum_injective D) (F.sort (·≤·)) r (Finset.sort_nodup _ _) hr
    (by simpa only [Finset.length_sort] using hrF)
    (fun j i _=>(hδ i (SortedIndex.enum D j)).trans (dist_comm _ _))
    (fun j i hi=>by rw [hsymm i (SortedIndex.enum D j)]; exact hcap _ (SortedIndex.enum_mem D j) i (by simpa only [Finset.sort_toFinset] using hi))
  rw [SortedIndex.image_enum] at hlocal hcost
  refine ⟨S,?_,by simpa only [Finset.sort_toFinset] using hSF,hS,hcard,
    by simpa only [Finset.sort_toFinset] using hlocal,?_⟩
  · rw [run,Function.comp_apply,Function.comp_apply,anchorInput_pack,he,BinaryProjection.run_setBits]
    congr 1
    simp only [project,Finset.image_image]
    change S.image id=S
    exact Finset.image_id
  · intro O hO hOF hOr
    exact hcost O hO (by simpa only [Finset.sort_toFinset] using hOF) hOr
end MetricKMedianRecovery.BitMachine.BinaryMetricAnchor

end OAI
