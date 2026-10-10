import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.SuffixProjection
import OAI.Combinatorics.TriangleRemoval.Process.IndexedPatternEdges

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

abbrev IndexedWitnessCode {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) :=
  Σ ab : Fin K × Fin K,
    Σ F : {F : PathForest s // ∀ i, F.OnPath (mark ab.1) i ∨ F.OnPath (mark ab.2) i},
      {f // f ∈ indexedAttachmentFamily E birth F.val}

noncomputable instance {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) : Fintype (IndexedWitnessCode E birth mark) := by
  classical
  unfold IndexedWitnessCode
  infer_instance

def decodeWitnessPattern {K s : ℕ} {E : Graph K} {birth : Fin s → Fin K}
    {mark : Fin K → Option (Fin s)} (w : IndexedWitnessCode E birth mark) :
    (Fin K × Fin K) × Graph K :=
  (w.1,insert {w.1.1,w.1.2} (indexedPatternEdges E birth w.2.2.val))

noncomputable def decodedWitnessPatterns {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) : Finset ((Fin K × Fin K) × Graph K) := by
  classical
  exact Finset.univ.image (decodeWitnessPattern (E := E) (birth := birth) (mark := mark))

lemma decodedWitnessPatterns_card {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (hE : E.card ≤ 2) (mark : Fin K → Option (Fin s)) :
    (decodedWitnessPatterns E birth mark).card ≤ K^2*6^s := by
  classical
  apply (Finset.card_image_le).trans
  rw [Finset.card_univ]
  simpa only [Fintype.card_fin] using
    all_marked_indexed_attachment_pattern_count E birth hE mark

def rootEdgeUniverse (K R : ℕ) : Graph K := (initialVertices K R).powersetCard 2

def seedPatternChoices (K R : ℕ) : Finset (Graph K) :=
  (rootEdgeUniverse K R).powerset.filter (fun E => E.card ≤ 2)

lemma seedPatternChoices_card {K R : ℕ} (hR : R ≤ K) (h4 : R ≤ 4) :
    (seedPatternChoices K R).card ≤ 64 := by
  have hc : (initialVertices K R).card = R := by
    simp only [initialVertices,Fin.card_filter_val_lt,Nat.min_eq_right hR]
  calc
    _ ≤ ((rootEdgeUniverse K R).powerset).card := Finset.card_filter_le _ _
    _ = 2^(R.choose 2) := by rw [Finset.card_powerset,rootEdgeUniverse,Finset.card_powersetCard,hc]
    _ ≤ 2^((4 : ℕ).choose 2) := Nat.pow_le_pow_right (by norm_num) (Nat.choose_le_choose 2 h4)
    _ = 64 := by decide

noncomputable def allDecodedWitnessPatterns {K s : ℕ} (R : ℕ) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) : Finset ((Fin K × Fin K) × Graph K) :=
  (seedPatternChoices K R).biUnion (fun E => decodedWitnessPatterns E birth mark)

lemma allDecodedWitnessPatterns_card {K s R : ℕ} (hR : R ≤ K) (h4 : R ≤ 4)
    (birth : Fin s → Fin K) (mark : Fin K → Option (Fin s)) :
    (allDecodedWitnessPatterns R birth mark).card ≤ 64*(K^2*6^s) := by
  classical
  apply (Finset.card_biUnion_le).trans
  calc
    _ ≤ ∑ _E ∈ seedPatternChoices K R, K^2*6^s := by
      apply Finset.sum_le_sum
      intro E hE
      exact decodedWitnessPatterns_card E birth (Finset.mem_filter.mp hE).2 mark
    _ = (seedPatternChoices K R).card * (K^2*6^s) := by simp only [Finset.sum_const,smul_eq_mul]
    _ ≤ 64*(K^2*6^s) := Nat.mul_le_mul_right _ (seedPatternChoices_card hR h4)

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

lemma pathRootEdges_mem_seedPatternChoices (a b : Fin N) (hR : R ≤ N)
    (hE : (A.seed.backEdges A.roots).card ≤ 2) :
    A.pathRootEdges a b ∈ seedPatternChoices (A.pathUnion a b).card R := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_,(A.pathRootEdges_count a b).trans hE⟩
  intro edge hedge
  obtain ⟨seedEdge,hseedEdge,rfl⟩ := Finset.mem_image.mp hedge
  obtain ⟨later,hlater,earlier,hearlier,rfl⟩ := A.seed.backEdges_mem_pair hseedEdge
  have hlaterRoot := (A.mem_roots later).mp hlater
  have hearlierRoot := A.seed_root later earlier hearlier hlaterRoot
  have hroot : ∀ vertex : Fin N, vertex.val < R → vertex ∈ A.pathUnion a b :=
    fun vertex hvertex => (A.mem_pathUnion a b vertex).mpr (Or.inl hvertex)
  have hsubset : ({earlier,later} : Finset (Fin N)) ⊆ A.pathUnion a b := by
    intro vertex hvertex
    simp only [Finset.mem_insert,Finset.mem_singleton] at hvertex
    rcases hvertex with rfl | rfl
    · exact hroot _ hearlierRoot
    · exact hroot _ hlaterRoot
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_,(reindexSet_card hsubset).trans
    (Finset.card_pair (ne_of_lt (A.seed.older_lt later earlier hearlier)))⟩
  intro vertex hvertex
  apply (mem_initialVertices _ _ _).mpr
  have hembedded := (mem_reindexSet _ _ _).mp hvertex
  have hembeddedRoot : ((A.pathUnion a b).orderEmbOfFin rfl vertex).val < R := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hembedded
    rcases hembedded with hearlierEq | hlaterEq
    · simpa only [hearlierEq] using hearlierRoot
    · simpa only [hlaterEq] using hlaterRoot
  let rootIndex : Fin (A.pathUnion a b).card :=
    ⟨((A.pathUnion a b).orderEmbOfFin rfl vertex).val,
      hembeddedRoot.trans_le (roots_le_card _ hR hroot)⟩
  have hequal : rootIndex = vertex := by
    apply ((A.pathUnion a b).orderEmbOfFin rfl).injective
    exact Fin.ext (orderEmb_initial _ hR hroot rootIndex hembeddedRoot)
  rw [← hequal]
  exact hembeddedRoot

lemma actual_decoded_pattern_mem (a b : Fin N) (hR : R ≤ N)
    (hE : (A.seed.backEdges A.roots).card ≤ 2) :
    ((A.pathIndex a b a (A.left_mem_pathUnion a b),A.pathIndex a b b (A.right_mem_pathUnion a b)),
      insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
        A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _) ((A.pathPattern a b).backEdges Finset.univ)) ∈
        allDecodedWitnessPatterns R (A.pathBirthIndex a b hR) (suffixProjection (A.path_card_split a b hR)) := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨A.pathRootEdges a b,A.pathRootEdges_mem_seedPatternChoices a b hR hE,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨A.pathWitnessCode a b hR,Finset.mem_univ _,?_⟩
  apply Prod.ext
  · rfl
  · change insert _ (indexedPatternEdges _ _ _) = insert _ _
    rw [A.pathPattern_edges a b hR]
    rfl

end TriangleGrowth
end SharpTerminalLeave

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

end

end OAI
