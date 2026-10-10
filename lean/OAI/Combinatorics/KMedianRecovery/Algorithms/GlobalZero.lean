import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.GlobalCall

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalZero
open WordOperations WordList LocalSearch
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) : List Bool :=
  BinaryMetricArrays.pack δ (SortedIndex.enum D) (SortedIndex.enum F)
noncomputable def one (x : List Bool) : List Bool :=
  rowRun (pairBits (BinaryMetricArrays.row x,field 2 (extractPrefix x)))
noncomputable def one_computes : PolyComputes one :=
  (BinaryMetricArrays.row_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp rowRun_computes
lemma one_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (hF : F.Nonempty) (p : Fin n) :
    one (pairBits (pack δ D F,p.val.bits))=(pick F hF (δ p)).val.bits := by
  rw [one,pack,BinaryMetricArrays.row_pair]
  simp only [extractPrefix_pairBits,BinaryMetricArrays.pack,field_encode,List.getElem?_cons_succ,
    List.getElem?_cons_zero,Option.getD_some,BinaryFinSet.table_enum]
  exact rowRun_pack F hF (δ p)
noncomputable def values (x : List Bool) : List Bool := mapWith one (pairBits (x,field 1 x))
noncomputable def values_computes : PolyComputes values := by
  unfold values
  simpa only [Function.comp_def,id_eq] using
    (id_computes.pair (field_computes 1)).comp (mapWith_computes one_computes)
noncomputable def run : List Bool→List Bool := BinaryNatSet.sort ∘ values
noncomputable def run_computes : PolyComputes run := values_computes.comp BinaryNatSet.sort_computes
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (hF : F.Nonempty) : Finset (Fin n) :=
  D.image (fun p=>pick F hF (δ p))
lemma run_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (hF : F.Nonempty) :
    run (pack δ D F)=BinaryFinSet.encode (output δ D F hF) := by
  rw [run,Function.comp_apply,values]
  have hf : field 1 (pack δ D F)=BinaryFinSet.encode D := by
    simp only [pack,BinaryMetricArrays.pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,
      Option.getD_some,BinaryFinSet.table_enum]
  rw [hf,BinaryFinSet.encode_eq,mapWith_encode]
  simp only [List.map_map,Function.comp_def,one_pack δ D F hF]
  have hh:=BinaryNatSet.sort_pack ((D.sort (·≤·)).map (fun p=>(pick F hF (δ p)).val))
  simp only [BinaryNatSet.pack,List.map_map,Function.comp_def] at hh
  rw [hh,BinaryFinSet.encode]
  congr 1
  ext j
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,BinaryFinSet.values,Finset.mem_image,output]
  exact ⟨fun ⟨p,hp,he⟩=>⟨pick F hF (δ p),⟨p,hp,rfl⟩,he⟩,
    fun ⟨f,⟨p,hp,he⟩,hj⟩=>⟨p,hp,by simpa only [he] using hj⟩⟩
lemma output_subset (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (hF : F.Nonempty) :
    output δ D F hF⊆F := by
  intro f hf
  obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp hf
  exact pick_mem F hF (δ p)
lemma output_nonempty (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (hF : F.Nonempty) (hD : D.Nonempty) :
    (output δ D F hF).Nonempty := hD.image _
variable [PseudoMetricSpace (Fin n)]
lemma rows_eq (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (p q : Fin n) (h : dist p q=0) : δ p=δ q := by
  funext f
  apply Rat.cast_injective (α:=ℝ)
  rw [hδ,hδ,dist_comm p f,dist_comm q f]
  exact PseudoMetricSpace.dist_eq_of_dist_zero f h

lemma zero_cost_spec (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F O : Finset (Fin n)) (hF : F.Nonempty) (hO : O.Nonempty) (hOF : O⊆F)
    (hzero : cost D O=0) :
    (output δ D F hF).card≤O.card ∧ cost D (output δ D F hF)=0 := by
  have hz (p:Fin n) (hp:p∈D) : dist p (nearest O hO p)=0 := by
    rw [nearest_distance]
    exact zero_cost_connection D O hzero p hp
  have hrows (p:Fin n) (hp:p∈D) : δ p=δ (nearest O hO p) := rows_eq δ hδ p _ (hz p hp)
  constructor
  · have hh : output δ D F hF⊆O.image (fun p=>pick F hF (δ p)) := by
      intro f hf
      obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hf
      exact Finset.mem_image.mpr ⟨nearest O hO p,nearest_mem O hO p,by rw [←hrows p hp]⟩
    exact (Finset.card_le_card hh).trans Finset.card_image_le
  · apply le_antisymm _ (cost_nonneg _ _)
    apply Finset.sum_nonpos
    intro p hp
    have hm:=pick_min F hF (δ p) (nearest O hO p) (hOF (nearest_mem O hO p))
    have hmR : dist p (pick F hF (δ p))≤0 := by
      have hh : (δ p (pick F hF (δ p)):ℝ)≤(δ p (nearest O hO p):ℝ) := by exact_mod_cast hm
      simpa only [hδ,hz p hp] using hh
    exact (connection_le (Finset.mem_image.mpr ⟨p,hp,rfl⟩)).trans hmR
lemma optimum_zero_spec (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F : Finset (Fin n)) (hF : F.Nonempty) (k : ℕ) (hk : 0<k) (hz : optimum F D k=0) :
    (output δ D F hF).card≤k ∧ cost D (output δ D F hF)=0 := by
  obtain ⟨O,hOF,hO,hOk,hOcost⟩:=optimum_attained F D hF k hk
  have hh:=zero_cost_spec δ hδ D F O hF hO hOF (hOcost.trans hz)
  exact ⟨hh.1.trans hOk,hh.2⟩
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

end OAI
