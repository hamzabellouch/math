import OAI.Combinatorics.Sidorenko.Dilution

namespace OAI


section

namespace SidorenkoCounterexample
open scoped BigOperators
def refineLeft0 : Fin 13 → Fin 35 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def refineRight0 : Fin 22 → Fin 35 := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def refineLeft1 : Fin 13 → Fin 35 := ![0, 2, 0, 2, 1, 0, 1, 1, 1, 2, 1, 2, 1]
def refineRight1 : Fin 22 → Fin 35 := ![3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]
def refineLeft2 : Fin 13 → Fin 35 := ![0, 2, 0, 2, 1, 0, 1, 1, 1, 2, 1, 2, 1]
def refineRight2 : Fin 22 → Fin 35 := ![6, 6, 9, 9, 3, 4, 4, 3, 7, 7, 3, 3, 4, 4, 8, 7, 8, 7, 5, 4, 5, 4]
def refineLeft3 : Fin 13 → Fin 35 := ![2, 11, 0, 12, 6, 1, 3, 4, 5, 9, 8, 10, 7]
def refineRight3 : Fin 22 → Fin 35 := ![16, 16, 19, 19, 13, 14, 14, 13, 17, 17, 13, 13, 14, 14, 18, 17, 18, 17, 15, 14, 15, 14]
def refineLeft4 : Fin 13 → Fin 35 := ![2, 11, 0, 12, 6, 1, 3, 4, 5, 9, 8, 10, 7]
def refineRight4 : Fin 22 → Fin 35 := ![25, 26, 33, 34, 13, 20, 21, 15, 29, 30, 16, 14, 19, 18, 32, 28, 31, 27, 24, 22, 23, 17]
def histLeft0 : Fin 13 → Fin 35 → ℕ := ![![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histLeft0_0 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 0 c=histLeft0 0 c := by decide +kernel
lemma histLeft0_1 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 1 c=histLeft0 1 c := by decide +kernel
lemma histLeft0_2 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 2 c=histLeft0 2 c := by decide +kernel
lemma histLeft0_3 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 3 c=histLeft0 3 c := by decide +kernel
lemma histLeft0_4 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 4 c=histLeft0 4 c := by decide +kernel
lemma histLeft0_5 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 5 c=histLeft0 5 c := by decide +kernel
lemma histLeft0_6 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 6 c=histLeft0 6 c := by decide +kernel
lemma histLeft0_7 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 7 c=histLeft0 7 c := by decide +kernel
lemma histLeft0_8 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 8 c=histLeft0 8 c := by decide +kernel
lemma histLeft0_9 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 9 c=histLeft0 9 c := by decide +kernel
lemma histLeft0_10 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 10 c=histLeft0 10 c := by decide +kernel
lemma histLeft0_11 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 11 c=histLeft0 11 c := by decide +kernel
lemma histLeft0_12 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 12 c=histLeft0 12 c := by decide +kernel
lemma histLeft0_correct : ∀ v c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) v c=histLeft0 v c := by
  intro v; fin_cases v
  · exact histLeft0_0
  · exact histLeft0_1
  · exact histLeft0_2
  · exact histLeft0_3
  · exact histLeft0_4
  · exact histLeft0_5
  · exact histLeft0_6
  · exact histLeft0_7
  · exact histLeft0_8
  · exact histLeft0_9
  · exact histLeft0_10
  · exact histLeft0_11
  · exact histLeft0_12
lemma refineLeft0_iff_0 : ∀ w, refineLeft1 0=refineLeft1 w ↔ refineLeft0 0=refineLeft0 w ∧ histLeft0 0=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_1 : ∀ w, refineLeft1 1=refineLeft1 w ↔ refineLeft0 1=refineLeft0 w ∧ histLeft0 1=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_2 : ∀ w, refineLeft1 2=refineLeft1 w ↔ refineLeft0 2=refineLeft0 w ∧ histLeft0 2=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_3 : ∀ w, refineLeft1 3=refineLeft1 w ↔ refineLeft0 3=refineLeft0 w ∧ histLeft0 3=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_4 : ∀ w, refineLeft1 4=refineLeft1 w ↔ refineLeft0 4=refineLeft0 w ∧ histLeft0 4=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_5 : ∀ w, refineLeft1 5=refineLeft1 w ↔ refineLeft0 5=refineLeft0 w ∧ histLeft0 5=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_6 : ∀ w, refineLeft1 6=refineLeft1 w ↔ refineLeft0 6=refineLeft0 w ∧ histLeft0 6=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_7 : ∀ w, refineLeft1 7=refineLeft1 w ↔ refineLeft0 7=refineLeft0 w ∧ histLeft0 7=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_8 : ∀ w, refineLeft1 8=refineLeft1 w ↔ refineLeft0 8=refineLeft0 w ∧ histLeft0 8=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_9 : ∀ w, refineLeft1 9=refineLeft1 w ↔ refineLeft0 9=refineLeft0 w ∧ histLeft0 9=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_10 : ∀ w, refineLeft1 10=refineLeft1 w ↔ refineLeft0 10=refineLeft0 w ∧ histLeft0 10=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_11 : ∀ w, refineLeft1 11=refineLeft1 w ↔ refineLeft0 11=refineLeft0 w ∧ histLeft0 11=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_12 : ∀ w, refineLeft1 12=refineLeft1 w ↔ refineLeft0 12=refineLeft0 w ∧ histLeft0 12=histLeft0 w := by decide +kernel
lemma refineLeft0_iff : ∀ v w, refineLeft1 v=refineLeft1 w ↔ refineLeft0 v=refineLeft0 w ∧ histLeft0 v=histLeft0 w := by
  intro v; fin_cases v
  · exact refineLeft0_iff_0
  · exact refineLeft0_iff_1
  · exact refineLeft0_iff_2
  · exact refineLeft0_iff_3
  · exact refineLeft0_iff_4
  · exact refineLeft0_iff_5
  · exact refineLeft0_iff_6
  · exact refineLeft0_iff_7
  · exact refineLeft0_iff_8
  · exact refineLeft0_iff_9
  · exact refineLeft0_iff_10
  · exact refineLeft0_iff_11
  · exact refineLeft0_iff_12
def histRight0 : Fin 22 → Fin 35 → ℕ := ![![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histRight0_0 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 0 c=histRight0 0 c := by decide +kernel
lemma histRight0_1 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 1 c=histRight0 1 c := by decide +kernel
lemma histRight0_2 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 2 c=histRight0 2 c := by decide +kernel
lemma histRight0_3 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 3 c=histRight0 3 c := by decide +kernel
lemma histRight0_4 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 4 c=histRight0 4 c := by decide +kernel
lemma histRight0_5 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 5 c=histRight0 5 c := by decide +kernel
lemma histRight0_6 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 6 c=histRight0 6 c := by decide +kernel
lemma histRight0_7 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 7 c=histRight0 7 c := by decide +kernel
lemma histRight0_8 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 8 c=histRight0 8 c := by decide +kernel
lemma histRight0_9 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 9 c=histRight0 9 c := by decide +kernel
lemma histRight0_10 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 10 c=histRight0 10 c := by decide +kernel
lemma histRight0_11 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 11 c=histRight0 11 c := by decide +kernel
lemma histRight0_12 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 12 c=histRight0 12 c := by decide +kernel
lemma histRight0_13 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 13 c=histRight0 13 c := by decide +kernel
lemma histRight0_14 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 14 c=histRight0 14 c := by decide +kernel
lemma histRight0_15 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 15 c=histRight0 15 c := by decide +kernel
lemma histRight0_16 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 16 c=histRight0 16 c := by decide +kernel
lemma histRight0_17 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 17 c=histRight0 17 c := by decide +kernel
lemma histRight0_18 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 18 c=histRight0 18 c := by decide +kernel
lemma histRight0_19 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 19 c=histRight0 19 c := by decide +kernel
lemma histRight0_20 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 20 c=histRight0 20 c := by decide +kernel
lemma histRight0_21 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 21 c=histRight0 21 c := by decide +kernel
lemma histRight0_correct : ∀ v c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) v c=histRight0 v c := by
  intro v; fin_cases v
  · exact histRight0_0
  · exact histRight0_1
  · exact histRight0_2
  · exact histRight0_3
  · exact histRight0_4
  · exact histRight0_5
  · exact histRight0_6
  · exact histRight0_7
  · exact histRight0_8
  · exact histRight0_9
  · exact histRight0_10
  · exact histRight0_11
  · exact histRight0_12
  · exact histRight0_13
  · exact histRight0_14
  · exact histRight0_15
  · exact histRight0_16
  · exact histRight0_17
  · exact histRight0_18
  · exact histRight0_19
  · exact histRight0_20
  · exact histRight0_21
lemma refineRight0_iff_0 : ∀ w, refineRight1 0=refineRight1 w ↔ refineRight0 0=refineRight0 w ∧ histRight0 0=histRight0 w := by decide +kernel
lemma refineRight0_iff_1 : ∀ w, refineRight1 1=refineRight1 w ↔ refineRight0 1=refineRight0 w ∧ histRight0 1=histRight0 w := by decide +kernel
lemma refineRight0_iff_2 : ∀ w, refineRight1 2=refineRight1 w ↔ refineRight0 2=refineRight0 w ∧ histRight0 2=histRight0 w := by decide +kernel
lemma refineRight0_iff_3 : ∀ w, refineRight1 3=refineRight1 w ↔ refineRight0 3=refineRight0 w ∧ histRight0 3=histRight0 w := by decide +kernel
lemma refineRight0_iff_4 : ∀ w, refineRight1 4=refineRight1 w ↔ refineRight0 4=refineRight0 w ∧ histRight0 4=histRight0 w := by decide +kernel
lemma refineRight0_iff_5 : ∀ w, refineRight1 5=refineRight1 w ↔ refineRight0 5=refineRight0 w ∧ histRight0 5=histRight0 w := by decide +kernel
lemma refineRight0_iff_6 : ∀ w, refineRight1 6=refineRight1 w ↔ refineRight0 6=refineRight0 w ∧ histRight0 6=histRight0 w := by decide +kernel
lemma refineRight0_iff_7 : ∀ w, refineRight1 7=refineRight1 w ↔ refineRight0 7=refineRight0 w ∧ histRight0 7=histRight0 w := by decide +kernel
lemma refineRight0_iff_8 : ∀ w, refineRight1 8=refineRight1 w ↔ refineRight0 8=refineRight0 w ∧ histRight0 8=histRight0 w := by decide +kernel
lemma refineRight0_iff_9 : ∀ w, refineRight1 9=refineRight1 w ↔ refineRight0 9=refineRight0 w ∧ histRight0 9=histRight0 w := by decide +kernel
lemma refineRight0_iff_10 : ∀ w, refineRight1 10=refineRight1 w ↔ refineRight0 10=refineRight0 w ∧ histRight0 10=histRight0 w := by decide +kernel
lemma refineRight0_iff_11 : ∀ w, refineRight1 11=refineRight1 w ↔ refineRight0 11=refineRight0 w ∧ histRight0 11=histRight0 w := by decide +kernel
lemma refineRight0_iff_12 : ∀ w, refineRight1 12=refineRight1 w ↔ refineRight0 12=refineRight0 w ∧ histRight0 12=histRight0 w := by decide +kernel
lemma refineRight0_iff_13 : ∀ w, refineRight1 13=refineRight1 w ↔ refineRight0 13=refineRight0 w ∧ histRight0 13=histRight0 w := by decide +kernel
lemma refineRight0_iff_14 : ∀ w, refineRight1 14=refineRight1 w ↔ refineRight0 14=refineRight0 w ∧ histRight0 14=histRight0 w := by decide +kernel
lemma refineRight0_iff_15 : ∀ w, refineRight1 15=refineRight1 w ↔ refineRight0 15=refineRight0 w ∧ histRight0 15=histRight0 w := by decide +kernel
lemma refineRight0_iff_16 : ∀ w, refineRight1 16=refineRight1 w ↔ refineRight0 16=refineRight0 w ∧ histRight0 16=histRight0 w := by decide +kernel
lemma refineRight0_iff_17 : ∀ w, refineRight1 17=refineRight1 w ↔ refineRight0 17=refineRight0 w ∧ histRight0 17=histRight0 w := by decide +kernel
lemma refineRight0_iff_18 : ∀ w, refineRight1 18=refineRight1 w ↔ refineRight0 18=refineRight0 w ∧ histRight0 18=histRight0 w := by decide +kernel
lemma refineRight0_iff_19 : ∀ w, refineRight1 19=refineRight1 w ↔ refineRight0 19=refineRight0 w ∧ histRight0 19=histRight0 w := by decide +kernel
lemma refineRight0_iff_20 : ∀ w, refineRight1 20=refineRight1 w ↔ refineRight0 20=refineRight0 w ∧ histRight0 20=histRight0 w := by decide +kernel
lemma refineRight0_iff_21 : ∀ w, refineRight1 21=refineRight1 w ↔ refineRight0 21=refineRight0 w ∧ histRight0 21=histRight0 w := by decide +kernel
lemma refineRight0_iff : ∀ v w, refineRight1 v=refineRight1 w ↔ refineRight0 v=refineRight0 w ∧ histRight0 v=histRight0 w := by
  intro v; fin_cases v
  · exact refineRight0_iff_0
  · exact refineRight0_iff_1
  · exact refineRight0_iff_2
  · exact refineRight0_iff_3
  · exact refineRight0_iff_4
  · exact refineRight0_iff_5
  · exact refineRight0_iff_6
  · exact refineRight0_iff_7
  · exact refineRight0_iff_8
  · exact refineRight0_iff_9
  · exact refineRight0_iff_10
  · exact refineRight0_iff_11
  · exact refineRight0_iff_12
  · exact refineRight0_iff_13
  · exact refineRight0_iff_14
  · exact refineRight0_iff_15
  · exact refineRight0_iff_16
  · exact refineRight0_iff_17
  · exact refineRight0_iff_18
  · exact refineRight0_iff_19
  · exact refineRight0_iff_20
  · exact refineRight0_iff_21
def histLeft1 : Fin 13 → Fin 35 → ℕ := ![![0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histLeft1_0 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 0 c=histLeft1 0 c := by decide +kernel
lemma histLeft1_1 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 1 c=histLeft1 1 c := by decide +kernel
lemma histLeft1_2 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 2 c=histLeft1 2 c := by decide +kernel
lemma histLeft1_3 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 3 c=histLeft1 3 c := by decide +kernel
lemma histLeft1_4 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 4 c=histLeft1 4 c := by decide +kernel
lemma histLeft1_5 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 5 c=histLeft1 5 c := by decide +kernel
lemma histLeft1_6 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 6 c=histLeft1 6 c := by decide +kernel
lemma histLeft1_7 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 7 c=histLeft1 7 c := by decide +kernel
lemma histLeft1_8 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 8 c=histLeft1 8 c := by decide +kernel
lemma histLeft1_9 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 9 c=histLeft1 9 c := by decide +kernel
lemma histLeft1_10 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 10 c=histLeft1 10 c := by decide +kernel
lemma histLeft1_11 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 11 c=histLeft1 11 c := by decide +kernel
lemma histLeft1_12 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) 12 c=histLeft1 12 c := by decide +kernel
lemma histLeft1_correct : ∀ v c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight1 k.1) v c=histLeft1 v c := by
  intro v; fin_cases v
  · exact histLeft1_0
  · exact histLeft1_1
  · exact histLeft1_2
  · exact histLeft1_3
  · exact histLeft1_4
  · exact histLeft1_5
  · exact histLeft1_6
  · exact histLeft1_7
  · exact histLeft1_8
  · exact histLeft1_9
  · exact histLeft1_10
  · exact histLeft1_11
  · exact histLeft1_12
lemma refineLeft1_iff_0 : ∀ w, refineLeft2 0=refineLeft2 w ↔ refineLeft1 0=refineLeft1 w ∧ histLeft1 0=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_1 : ∀ w, refineLeft2 1=refineLeft2 w ↔ refineLeft1 1=refineLeft1 w ∧ histLeft1 1=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_2 : ∀ w, refineLeft2 2=refineLeft2 w ↔ refineLeft1 2=refineLeft1 w ∧ histLeft1 2=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_3 : ∀ w, refineLeft2 3=refineLeft2 w ↔ refineLeft1 3=refineLeft1 w ∧ histLeft1 3=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_4 : ∀ w, refineLeft2 4=refineLeft2 w ↔ refineLeft1 4=refineLeft1 w ∧ histLeft1 4=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_5 : ∀ w, refineLeft2 5=refineLeft2 w ↔ refineLeft1 5=refineLeft1 w ∧ histLeft1 5=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_6 : ∀ w, refineLeft2 6=refineLeft2 w ↔ refineLeft1 6=refineLeft1 w ∧ histLeft1 6=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_7 : ∀ w, refineLeft2 7=refineLeft2 w ↔ refineLeft1 7=refineLeft1 w ∧ histLeft1 7=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_8 : ∀ w, refineLeft2 8=refineLeft2 w ↔ refineLeft1 8=refineLeft1 w ∧ histLeft1 8=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_9 : ∀ w, refineLeft2 9=refineLeft2 w ↔ refineLeft1 9=refineLeft1 w ∧ histLeft1 9=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_10 : ∀ w, refineLeft2 10=refineLeft2 w ↔ refineLeft1 10=refineLeft1 w ∧ histLeft1 10=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_11 : ∀ w, refineLeft2 11=refineLeft2 w ↔ refineLeft1 11=refineLeft1 w ∧ histLeft1 11=histLeft1 w := by decide +kernel
lemma refineLeft1_iff_12 : ∀ w, refineLeft2 12=refineLeft2 w ↔ refineLeft1 12=refineLeft1 w ∧ histLeft1 12=histLeft1 w := by decide +kernel
lemma refineLeft1_iff : ∀ v w, refineLeft2 v=refineLeft2 w ↔ refineLeft1 v=refineLeft1 w ∧ histLeft1 v=histLeft1 w := by
  intro v; fin_cases v
  · exact refineLeft1_iff_0
  · exact refineLeft1_iff_1
  · exact refineLeft1_iff_2
  · exact refineLeft1_iff_3
  · exact refineLeft1_iff_4
  · exact refineLeft1_iff_5
  · exact refineLeft1_iff_6
  · exact refineLeft1_iff_7
  · exact refineLeft1_iff_8
  · exact refineLeft1_iff_9
  · exact refineLeft1_iff_10
  · exact refineLeft1_iff_11
  · exact refineLeft1_iff_12
def histRight1 : Fin 22 → Fin 35 → ℕ := ![![1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histRight1_0 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 0 c=histRight1 0 c := by decide +kernel
lemma histRight1_1 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 1 c=histRight1 1 c := by decide +kernel
lemma histRight1_2 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 2 c=histRight1 2 c := by decide +kernel
lemma histRight1_3 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 3 c=histRight1 3 c := by decide +kernel
lemma histRight1_4 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 4 c=histRight1 4 c := by decide +kernel
lemma histRight1_5 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 5 c=histRight1 5 c := by decide +kernel
lemma histRight1_6 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 6 c=histRight1 6 c := by decide +kernel
lemma histRight1_7 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 7 c=histRight1 7 c := by decide +kernel
lemma histRight1_8 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 8 c=histRight1 8 c := by decide +kernel
lemma histRight1_9 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 9 c=histRight1 9 c := by decide +kernel
lemma histRight1_10 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 10 c=histRight1 10 c := by decide +kernel
lemma histRight1_11 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 11 c=histRight1 11 c := by decide +kernel
lemma histRight1_12 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 12 c=histRight1 12 c := by decide +kernel
lemma histRight1_13 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 13 c=histRight1 13 c := by decide +kernel
lemma histRight1_14 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 14 c=histRight1 14 c := by decide +kernel
lemma histRight1_15 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 15 c=histRight1 15 c := by decide +kernel
lemma histRight1_16 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 16 c=histRight1 16 c := by decide +kernel
lemma histRight1_17 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 17 c=histRight1 17 c := by decide +kernel
lemma histRight1_18 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 18 c=histRight1 18 c := by decide +kernel
lemma histRight1_19 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 19 c=histRight1 19 c := by decide +kernel
lemma histRight1_20 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 20 c=histRight1 20 c := by decide +kernel
lemma histRight1_21 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) 21 c=histRight1 21 c := by decide +kernel
lemma histRight1_correct : ∀ v c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft1 (cornerPoint k)) v c=histRight1 v c := by
  intro v; fin_cases v
  · exact histRight1_0
  · exact histRight1_1
  · exact histRight1_2
  · exact histRight1_3
  · exact histRight1_4
  · exact histRight1_5
  · exact histRight1_6
  · exact histRight1_7
  · exact histRight1_8
  · exact histRight1_9
  · exact histRight1_10
  · exact histRight1_11
  · exact histRight1_12
  · exact histRight1_13
  · exact histRight1_14
  · exact histRight1_15
  · exact histRight1_16
  · exact histRight1_17
  · exact histRight1_18
  · exact histRight1_19
  · exact histRight1_20
  · exact histRight1_21
lemma refineRight1_iff_0 : ∀ w, refineRight2 0=refineRight2 w ↔ refineRight1 0=refineRight1 w ∧ histRight1 0=histRight1 w := by decide +kernel
lemma refineRight1_iff_1 : ∀ w, refineRight2 1=refineRight2 w ↔ refineRight1 1=refineRight1 w ∧ histRight1 1=histRight1 w := by decide +kernel
lemma refineRight1_iff_2 : ∀ w, refineRight2 2=refineRight2 w ↔ refineRight1 2=refineRight1 w ∧ histRight1 2=histRight1 w := by decide +kernel
lemma refineRight1_iff_3 : ∀ w, refineRight2 3=refineRight2 w ↔ refineRight1 3=refineRight1 w ∧ histRight1 3=histRight1 w := by decide +kernel
lemma refineRight1_iff_4 : ∀ w, refineRight2 4=refineRight2 w ↔ refineRight1 4=refineRight1 w ∧ histRight1 4=histRight1 w := by decide +kernel
lemma refineRight1_iff_5 : ∀ w, refineRight2 5=refineRight2 w ↔ refineRight1 5=refineRight1 w ∧ histRight1 5=histRight1 w := by decide +kernel
lemma refineRight1_iff_6 : ∀ w, refineRight2 6=refineRight2 w ↔ refineRight1 6=refineRight1 w ∧ histRight1 6=histRight1 w := by decide +kernel
lemma refineRight1_iff_7 : ∀ w, refineRight2 7=refineRight2 w ↔ refineRight1 7=refineRight1 w ∧ histRight1 7=histRight1 w := by decide +kernel
lemma refineRight1_iff_8 : ∀ w, refineRight2 8=refineRight2 w ↔ refineRight1 8=refineRight1 w ∧ histRight1 8=histRight1 w := by decide +kernel
lemma refineRight1_iff_9 : ∀ w, refineRight2 9=refineRight2 w ↔ refineRight1 9=refineRight1 w ∧ histRight1 9=histRight1 w := by decide +kernel
lemma refineRight1_iff_10 : ∀ w, refineRight2 10=refineRight2 w ↔ refineRight1 10=refineRight1 w ∧ histRight1 10=histRight1 w := by decide +kernel
lemma refineRight1_iff_11 : ∀ w, refineRight2 11=refineRight2 w ↔ refineRight1 11=refineRight1 w ∧ histRight1 11=histRight1 w := by decide +kernel
lemma refineRight1_iff_12 : ∀ w, refineRight2 12=refineRight2 w ↔ refineRight1 12=refineRight1 w ∧ histRight1 12=histRight1 w := by decide +kernel
lemma refineRight1_iff_13 : ∀ w, refineRight2 13=refineRight2 w ↔ refineRight1 13=refineRight1 w ∧ histRight1 13=histRight1 w := by decide +kernel
lemma refineRight1_iff_14 : ∀ w, refineRight2 14=refineRight2 w ↔ refineRight1 14=refineRight1 w ∧ histRight1 14=histRight1 w := by decide +kernel
lemma refineRight1_iff_15 : ∀ w, refineRight2 15=refineRight2 w ↔ refineRight1 15=refineRight1 w ∧ histRight1 15=histRight1 w := by decide +kernel
lemma refineRight1_iff_16 : ∀ w, refineRight2 16=refineRight2 w ↔ refineRight1 16=refineRight1 w ∧ histRight1 16=histRight1 w := by decide +kernel
lemma refineRight1_iff_17 : ∀ w, refineRight2 17=refineRight2 w ↔ refineRight1 17=refineRight1 w ∧ histRight1 17=histRight1 w := by decide +kernel
lemma refineRight1_iff_18 : ∀ w, refineRight2 18=refineRight2 w ↔ refineRight1 18=refineRight1 w ∧ histRight1 18=histRight1 w := by decide +kernel
lemma refineRight1_iff_19 : ∀ w, refineRight2 19=refineRight2 w ↔ refineRight1 19=refineRight1 w ∧ histRight1 19=histRight1 w := by decide +kernel
lemma refineRight1_iff_20 : ∀ w, refineRight2 20=refineRight2 w ↔ refineRight1 20=refineRight1 w ∧ histRight1 20=histRight1 w := by decide +kernel
lemma refineRight1_iff_21 : ∀ w, refineRight2 21=refineRight2 w ↔ refineRight1 21=refineRight1 w ∧ histRight1 21=histRight1 w := by decide +kernel
lemma refineRight1_iff : ∀ v w, refineRight2 v=refineRight2 w ↔ refineRight1 v=refineRight1 w ∧ histRight1 v=histRight1 w := by
  intro v; fin_cases v
  · exact refineRight1_iff_0
  · exact refineRight1_iff_1
  · exact refineRight1_iff_2
  · exact refineRight1_iff_3
  · exact refineRight1_iff_4
  · exact refineRight1_iff_5
  · exact refineRight1_iff_6
  · exact refineRight1_iff_7
  · exact refineRight1_iff_8
  · exact refineRight1_iff_9
  · exact refineRight1_iff_10
  · exact refineRight1_iff_11
  · exact refineRight1_iff_12
  · exact refineRight1_iff_13
  · exact refineRight1_iff_14
  · exact refineRight1_iff_15
  · exact refineRight1_iff_16
  · exact refineRight1_iff_17
  · exact refineRight1_iff_18
  · exact refineRight1_iff_19
  · exact refineRight1_iff_20
  · exact refineRight1_iff_21
def histLeft2 : Fin 13 → Fin 35 → ℕ := ![![0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 2, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histLeft2_0 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 0 c=histLeft2 0 c := by decide +kernel
lemma histLeft2_1 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 1 c=histLeft2 1 c := by decide +kernel
lemma histLeft2_2 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 2 c=histLeft2 2 c := by decide +kernel
lemma histLeft2_3 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 3 c=histLeft2 3 c := by decide +kernel
lemma histLeft2_4 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 4 c=histLeft2 4 c := by decide +kernel
lemma histLeft2_5 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 5 c=histLeft2 5 c := by decide +kernel
lemma histLeft2_6 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 6 c=histLeft2 6 c := by decide +kernel
lemma histLeft2_7 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 7 c=histLeft2 7 c := by decide +kernel
lemma histLeft2_8 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 8 c=histLeft2 8 c := by decide +kernel
lemma histLeft2_9 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 9 c=histLeft2 9 c := by decide +kernel
lemma histLeft2_10 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 10 c=histLeft2 10 c := by decide +kernel
lemma histLeft2_11 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 11 c=histLeft2 11 c := by decide +kernel
lemma histLeft2_12 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) 12 c=histLeft2 12 c := by decide +kernel
lemma histLeft2_correct : ∀ v c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight2 k.1) v c=histLeft2 v c := by
  intro v; fin_cases v
  · exact histLeft2_0
  · exact histLeft2_1
  · exact histLeft2_2
  · exact histLeft2_3
  · exact histLeft2_4
  · exact histLeft2_5
  · exact histLeft2_6
  · exact histLeft2_7
  · exact histLeft2_8
  · exact histLeft2_9
  · exact histLeft2_10
  · exact histLeft2_11
  · exact histLeft2_12
lemma refineLeft2_iff_0 : ∀ w, refineLeft3 0=refineLeft3 w ↔ refineLeft2 0=refineLeft2 w ∧ histLeft2 0=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_1 : ∀ w, refineLeft3 1=refineLeft3 w ↔ refineLeft2 1=refineLeft2 w ∧ histLeft2 1=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_2 : ∀ w, refineLeft3 2=refineLeft3 w ↔ refineLeft2 2=refineLeft2 w ∧ histLeft2 2=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_3 : ∀ w, refineLeft3 3=refineLeft3 w ↔ refineLeft2 3=refineLeft2 w ∧ histLeft2 3=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_4 : ∀ w, refineLeft3 4=refineLeft3 w ↔ refineLeft2 4=refineLeft2 w ∧ histLeft2 4=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_5 : ∀ w, refineLeft3 5=refineLeft3 w ↔ refineLeft2 5=refineLeft2 w ∧ histLeft2 5=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_6 : ∀ w, refineLeft3 6=refineLeft3 w ↔ refineLeft2 6=refineLeft2 w ∧ histLeft2 6=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_7 : ∀ w, refineLeft3 7=refineLeft3 w ↔ refineLeft2 7=refineLeft2 w ∧ histLeft2 7=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_8 : ∀ w, refineLeft3 8=refineLeft3 w ↔ refineLeft2 8=refineLeft2 w ∧ histLeft2 8=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_9 : ∀ w, refineLeft3 9=refineLeft3 w ↔ refineLeft2 9=refineLeft2 w ∧ histLeft2 9=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_10 : ∀ w, refineLeft3 10=refineLeft3 w ↔ refineLeft2 10=refineLeft2 w ∧ histLeft2 10=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_11 : ∀ w, refineLeft3 11=refineLeft3 w ↔ refineLeft2 11=refineLeft2 w ∧ histLeft2 11=histLeft2 w := by decide +kernel
lemma refineLeft2_iff_12 : ∀ w, refineLeft3 12=refineLeft3 w ↔ refineLeft2 12=refineLeft2 w ∧ histLeft2 12=histLeft2 w := by decide +kernel
lemma refineLeft2_iff : ∀ v w, refineLeft3 v=refineLeft3 w ↔ refineLeft2 v=refineLeft2 w ∧ histLeft2 v=histLeft2 w := by
  intro v; fin_cases v
  · exact refineLeft2_iff_0
  · exact refineLeft2_iff_1
  · exact refineLeft2_iff_2
  · exact refineLeft2_iff_3
  · exact refineLeft2_iff_4
  · exact refineLeft2_iff_5
  · exact refineLeft2_iff_6
  · exact refineLeft2_iff_7
  · exact refineLeft2_iff_8
  · exact refineLeft2_iff_9
  · exact refineLeft2_iff_10
  · exact refineLeft2_iff_11
  · exact refineLeft2_iff_12
def histRight2 : Fin 22 → Fin 35 → ℕ := ![![1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histRight2_0 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 0 c=histRight2 0 c := by decide +kernel
lemma histRight2_1 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 1 c=histRight2 1 c := by decide +kernel
lemma histRight2_2 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 2 c=histRight2 2 c := by decide +kernel
lemma histRight2_3 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 3 c=histRight2 3 c := by decide +kernel
lemma histRight2_4 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 4 c=histRight2 4 c := by decide +kernel
lemma histRight2_5 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 5 c=histRight2 5 c := by decide +kernel
lemma histRight2_6 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 6 c=histRight2 6 c := by decide +kernel
lemma histRight2_7 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 7 c=histRight2 7 c := by decide +kernel
lemma histRight2_8 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 8 c=histRight2 8 c := by decide +kernel
lemma histRight2_9 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 9 c=histRight2 9 c := by decide +kernel
lemma histRight2_10 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 10 c=histRight2 10 c := by decide +kernel
lemma histRight2_11 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 11 c=histRight2 11 c := by decide +kernel
lemma histRight2_12 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 12 c=histRight2 12 c := by decide +kernel
lemma histRight2_13 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 13 c=histRight2 13 c := by decide +kernel
lemma histRight2_14 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 14 c=histRight2 14 c := by decide +kernel
lemma histRight2_15 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 15 c=histRight2 15 c := by decide +kernel
lemma histRight2_16 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 16 c=histRight2 16 c := by decide +kernel
lemma histRight2_17 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 17 c=histRight2 17 c := by decide +kernel
lemma histRight2_18 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 18 c=histRight2 18 c := by decide +kernel
lemma histRight2_19 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 19 c=histRight2 19 c := by decide +kernel
lemma histRight2_20 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 20 c=histRight2 20 c := by decide +kernel
lemma histRight2_21 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) 21 c=histRight2 21 c := by decide +kernel
lemma histRight2_correct : ∀ v c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft2 (cornerPoint k)) v c=histRight2 v c := by
  intro v; fin_cases v
  · exact histRight2_0
  · exact histRight2_1
  · exact histRight2_2
  · exact histRight2_3
  · exact histRight2_4
  · exact histRight2_5
  · exact histRight2_6
  · exact histRight2_7
  · exact histRight2_8
  · exact histRight2_9
  · exact histRight2_10
  · exact histRight2_11
  · exact histRight2_12
  · exact histRight2_13
  · exact histRight2_14
  · exact histRight2_15
  · exact histRight2_16
  · exact histRight2_17
  · exact histRight2_18
  · exact histRight2_19
  · exact histRight2_20
  · exact histRight2_21
lemma refineRight2_iff_0 : ∀ w, refineRight3 0=refineRight3 w ↔ refineRight2 0=refineRight2 w ∧ histRight2 0=histRight2 w := by decide +kernel
lemma refineRight2_iff_1 : ∀ w, refineRight3 1=refineRight3 w ↔ refineRight2 1=refineRight2 w ∧ histRight2 1=histRight2 w := by decide +kernel
lemma refineRight2_iff_2 : ∀ w, refineRight3 2=refineRight3 w ↔ refineRight2 2=refineRight2 w ∧ histRight2 2=histRight2 w := by decide +kernel
lemma refineRight2_iff_3 : ∀ w, refineRight3 3=refineRight3 w ↔ refineRight2 3=refineRight2 w ∧ histRight2 3=histRight2 w := by decide +kernel
lemma refineRight2_iff_4 : ∀ w, refineRight3 4=refineRight3 w ↔ refineRight2 4=refineRight2 w ∧ histRight2 4=histRight2 w := by decide +kernel
lemma refineRight2_iff_5 : ∀ w, refineRight3 5=refineRight3 w ↔ refineRight2 5=refineRight2 w ∧ histRight2 5=histRight2 w := by decide +kernel
lemma refineRight2_iff_6 : ∀ w, refineRight3 6=refineRight3 w ↔ refineRight2 6=refineRight2 w ∧ histRight2 6=histRight2 w := by decide +kernel
lemma refineRight2_iff_7 : ∀ w, refineRight3 7=refineRight3 w ↔ refineRight2 7=refineRight2 w ∧ histRight2 7=histRight2 w := by decide +kernel
lemma refineRight2_iff_8 : ∀ w, refineRight3 8=refineRight3 w ↔ refineRight2 8=refineRight2 w ∧ histRight2 8=histRight2 w := by decide +kernel
lemma refineRight2_iff_9 : ∀ w, refineRight3 9=refineRight3 w ↔ refineRight2 9=refineRight2 w ∧ histRight2 9=histRight2 w := by decide +kernel
lemma refineRight2_iff_10 : ∀ w, refineRight3 10=refineRight3 w ↔ refineRight2 10=refineRight2 w ∧ histRight2 10=histRight2 w := by decide +kernel
lemma refineRight2_iff_11 : ∀ w, refineRight3 11=refineRight3 w ↔ refineRight2 11=refineRight2 w ∧ histRight2 11=histRight2 w := by decide +kernel
lemma refineRight2_iff_12 : ∀ w, refineRight3 12=refineRight3 w ↔ refineRight2 12=refineRight2 w ∧ histRight2 12=histRight2 w := by decide +kernel
lemma refineRight2_iff_13 : ∀ w, refineRight3 13=refineRight3 w ↔ refineRight2 13=refineRight2 w ∧ histRight2 13=histRight2 w := by decide +kernel
lemma refineRight2_iff_14 : ∀ w, refineRight3 14=refineRight3 w ↔ refineRight2 14=refineRight2 w ∧ histRight2 14=histRight2 w := by decide +kernel
lemma refineRight2_iff_15 : ∀ w, refineRight3 15=refineRight3 w ↔ refineRight2 15=refineRight2 w ∧ histRight2 15=histRight2 w := by decide +kernel
lemma refineRight2_iff_16 : ∀ w, refineRight3 16=refineRight3 w ↔ refineRight2 16=refineRight2 w ∧ histRight2 16=histRight2 w := by decide +kernel
lemma refineRight2_iff_17 : ∀ w, refineRight3 17=refineRight3 w ↔ refineRight2 17=refineRight2 w ∧ histRight2 17=histRight2 w := by decide +kernel
lemma refineRight2_iff_18 : ∀ w, refineRight3 18=refineRight3 w ↔ refineRight2 18=refineRight2 w ∧ histRight2 18=histRight2 w := by decide +kernel
lemma refineRight2_iff_19 : ∀ w, refineRight3 19=refineRight3 w ↔ refineRight2 19=refineRight2 w ∧ histRight2 19=histRight2 w := by decide +kernel
lemma refineRight2_iff_20 : ∀ w, refineRight3 20=refineRight3 w ↔ refineRight2 20=refineRight2 w ∧ histRight2 20=histRight2 w := by decide +kernel
lemma refineRight2_iff_21 : ∀ w, refineRight3 21=refineRight3 w ↔ refineRight2 21=refineRight2 w ∧ histRight2 21=histRight2 w := by decide +kernel
lemma refineRight2_iff : ∀ v w, refineRight3 v=refineRight3 w ↔ refineRight2 v=refineRight2 w ∧ histRight2 v=histRight2 w := by
  intro v; fin_cases v
  · exact refineRight2_iff_0
  · exact refineRight2_iff_1
  · exact refineRight2_iff_2
  · exact refineRight2_iff_3
  · exact refineRight2_iff_4
  · exact refineRight2_iff_5
  · exact refineRight2_iff_6
  · exact refineRight2_iff_7
  · exact refineRight2_iff_8
  · exact refineRight2_iff_9
  · exact refineRight2_iff_10
  · exact refineRight2_iff_11
  · exact refineRight2_iff_12
  · exact refineRight2_iff_13
  · exact refineRight2_iff_14
  · exact refineRight2_iff_15
  · exact refineRight2_iff_16
  · exact refineRight2_iff_17
  · exact refineRight2_iff_18
  · exact refineRight2_iff_19
  · exact refineRight2_iff_20
  · exact refineRight2_iff_21
def histLeft3 : Fin 13 → Fin 35 → ℕ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histLeft3_0 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 0 c=histLeft3 0 c := by decide +kernel
lemma histLeft3_1 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 1 c=histLeft3 1 c := by decide +kernel
lemma histLeft3_2 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 2 c=histLeft3 2 c := by decide +kernel
lemma histLeft3_3 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 3 c=histLeft3 3 c := by decide +kernel
lemma histLeft3_4 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 4 c=histLeft3 4 c := by decide +kernel
lemma histLeft3_5 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 5 c=histLeft3 5 c := by decide +kernel
lemma histLeft3_6 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 6 c=histLeft3 6 c := by decide +kernel
lemma histLeft3_7 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 7 c=histLeft3 7 c := by decide +kernel
lemma histLeft3_8 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 8 c=histLeft3 8 c := by decide +kernel
lemma histLeft3_9 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 9 c=histLeft3 9 c := by decide +kernel
lemma histLeft3_10 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 10 c=histLeft3 10 c := by decide +kernel
lemma histLeft3_11 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 11 c=histLeft3 11 c := by decide +kernel
lemma histLeft3_12 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 12 c=histLeft3 12 c := by decide +kernel
lemma histLeft3_correct : ∀ v c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) v c=histLeft3 v c := by
  intro v; fin_cases v
  · exact histLeft3_0
  · exact histLeft3_1
  · exact histLeft3_2
  · exact histLeft3_3
  · exact histLeft3_4
  · exact histLeft3_5
  · exact histLeft3_6
  · exact histLeft3_7
  · exact histLeft3_8
  · exact histLeft3_9
  · exact histLeft3_10
  · exact histLeft3_11
  · exact histLeft3_12
lemma refineLeft3_iff_0 : ∀ w, refineLeft4 0=refineLeft4 w ↔ refineLeft3 0=refineLeft3 w ∧ histLeft3 0=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_1 : ∀ w, refineLeft4 1=refineLeft4 w ↔ refineLeft3 1=refineLeft3 w ∧ histLeft3 1=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_2 : ∀ w, refineLeft4 2=refineLeft4 w ↔ refineLeft3 2=refineLeft3 w ∧ histLeft3 2=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_3 : ∀ w, refineLeft4 3=refineLeft4 w ↔ refineLeft3 3=refineLeft3 w ∧ histLeft3 3=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_4 : ∀ w, refineLeft4 4=refineLeft4 w ↔ refineLeft3 4=refineLeft3 w ∧ histLeft3 4=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_5 : ∀ w, refineLeft4 5=refineLeft4 w ↔ refineLeft3 5=refineLeft3 w ∧ histLeft3 5=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_6 : ∀ w, refineLeft4 6=refineLeft4 w ↔ refineLeft3 6=refineLeft3 w ∧ histLeft3 6=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_7 : ∀ w, refineLeft4 7=refineLeft4 w ↔ refineLeft3 7=refineLeft3 w ∧ histLeft3 7=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_8 : ∀ w, refineLeft4 8=refineLeft4 w ↔ refineLeft3 8=refineLeft3 w ∧ histLeft3 8=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_9 : ∀ w, refineLeft4 9=refineLeft4 w ↔ refineLeft3 9=refineLeft3 w ∧ histLeft3 9=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_10 : ∀ w, refineLeft4 10=refineLeft4 w ↔ refineLeft3 10=refineLeft3 w ∧ histLeft3 10=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_11 : ∀ w, refineLeft4 11=refineLeft4 w ↔ refineLeft3 11=refineLeft3 w ∧ histLeft3 11=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_12 : ∀ w, refineLeft4 12=refineLeft4 w ↔ refineLeft3 12=refineLeft3 w ∧ histLeft3 12=histLeft3 w := by decide +kernel
lemma refineLeft3_iff : ∀ v w, refineLeft4 v=refineLeft4 w ↔ refineLeft3 v=refineLeft3 w ∧ histLeft3 v=histLeft3 w := by
  intro v; fin_cases v
  · exact refineLeft3_iff_0
  · exact refineLeft3_iff_1
  · exact refineLeft3_iff_2
  · exact refineLeft3_iff_3
  · exact refineLeft3_iff_4
  · exact refineLeft3_iff_5
  · exact refineLeft3_iff_6
  · exact refineLeft3_iff_7
  · exact refineLeft3_iff_8
  · exact refineLeft3_iff_9
  · exact refineLeft3_iff_10
  · exact refineLeft3_iff_11
  · exact refineLeft3_iff_12
def histRight3 : Fin 22 → Fin 35 → ℕ := ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histRight3_0 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 0 c=histRight3 0 c := by decide +kernel
lemma histRight3_1 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 1 c=histRight3 1 c := by decide +kernel
lemma histRight3_2 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 2 c=histRight3 2 c := by decide +kernel
lemma histRight3_3 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 3 c=histRight3 3 c := by decide +kernel
lemma histRight3_4 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 4 c=histRight3 4 c := by decide +kernel
lemma histRight3_5 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 5 c=histRight3 5 c := by decide +kernel
lemma histRight3_6 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 6 c=histRight3 6 c := by decide +kernel
lemma histRight3_7 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 7 c=histRight3 7 c := by decide +kernel
lemma histRight3_8 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 8 c=histRight3 8 c := by decide +kernel
lemma histRight3_9 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 9 c=histRight3 9 c := by decide +kernel
lemma histRight3_10 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 10 c=histRight3 10 c := by decide +kernel
lemma histRight3_11 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 11 c=histRight3 11 c := by decide +kernel
lemma histRight3_12 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 12 c=histRight3 12 c := by decide +kernel
lemma histRight3_13 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 13 c=histRight3 13 c := by decide +kernel
lemma histRight3_14 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 14 c=histRight3 14 c := by decide +kernel
lemma histRight3_15 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 15 c=histRight3 15 c := by decide +kernel
lemma histRight3_16 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 16 c=histRight3 16 c := by decide +kernel
lemma histRight3_17 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 17 c=histRight3 17 c := by decide +kernel
lemma histRight3_18 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 18 c=histRight3 18 c := by decide +kernel
lemma histRight3_19 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 19 c=histRight3 19 c := by decide +kernel
lemma histRight3_20 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 20 c=histRight3 20 c := by decide +kernel
lemma histRight3_21 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 21 c=histRight3 21 c := by decide +kernel
lemma histRight3_correct : ∀ v c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) v c=histRight3 v c := by
  intro v; fin_cases v
  · exact histRight3_0
  · exact histRight3_1
  · exact histRight3_2
  · exact histRight3_3
  · exact histRight3_4
  · exact histRight3_5
  · exact histRight3_6
  · exact histRight3_7
  · exact histRight3_8
  · exact histRight3_9
  · exact histRight3_10
  · exact histRight3_11
  · exact histRight3_12
  · exact histRight3_13
  · exact histRight3_14
  · exact histRight3_15
  · exact histRight3_16
  · exact histRight3_17
  · exact histRight3_18
  · exact histRight3_19
  · exact histRight3_20
  · exact histRight3_21
lemma refineRight3_iff_0 : ∀ w, refineRight4 0=refineRight4 w ↔ refineRight3 0=refineRight3 w ∧ histRight3 0=histRight3 w := by decide +kernel
lemma refineRight3_iff_1 : ∀ w, refineRight4 1=refineRight4 w ↔ refineRight3 1=refineRight3 w ∧ histRight3 1=histRight3 w := by decide +kernel
lemma refineRight3_iff_2 : ∀ w, refineRight4 2=refineRight4 w ↔ refineRight3 2=refineRight3 w ∧ histRight3 2=histRight3 w := by decide +kernel
lemma refineRight3_iff_3 : ∀ w, refineRight4 3=refineRight4 w ↔ refineRight3 3=refineRight3 w ∧ histRight3 3=histRight3 w := by decide +kernel
lemma refineRight3_iff_4 : ∀ w, refineRight4 4=refineRight4 w ↔ refineRight3 4=refineRight3 w ∧ histRight3 4=histRight3 w := by decide +kernel
lemma refineRight3_iff_5 : ∀ w, refineRight4 5=refineRight4 w ↔ refineRight3 5=refineRight3 w ∧ histRight3 5=histRight3 w := by decide +kernel
lemma refineRight3_iff_6 : ∀ w, refineRight4 6=refineRight4 w ↔ refineRight3 6=refineRight3 w ∧ histRight3 6=histRight3 w := by decide +kernel
lemma refineRight3_iff_7 : ∀ w, refineRight4 7=refineRight4 w ↔ refineRight3 7=refineRight3 w ∧ histRight3 7=histRight3 w := by decide +kernel
lemma refineRight3_iff_8 : ∀ w, refineRight4 8=refineRight4 w ↔ refineRight3 8=refineRight3 w ∧ histRight3 8=histRight3 w := by decide +kernel
lemma refineRight3_iff_9 : ∀ w, refineRight4 9=refineRight4 w ↔ refineRight3 9=refineRight3 w ∧ histRight3 9=histRight3 w := by decide +kernel
lemma refineRight3_iff_10 : ∀ w, refineRight4 10=refineRight4 w ↔ refineRight3 10=refineRight3 w ∧ histRight3 10=histRight3 w := by decide +kernel
lemma refineRight3_iff_11 : ∀ w, refineRight4 11=refineRight4 w ↔ refineRight3 11=refineRight3 w ∧ histRight3 11=histRight3 w := by decide +kernel
lemma refineRight3_iff_12 : ∀ w, refineRight4 12=refineRight4 w ↔ refineRight3 12=refineRight3 w ∧ histRight3 12=histRight3 w := by decide +kernel
lemma refineRight3_iff_13 : ∀ w, refineRight4 13=refineRight4 w ↔ refineRight3 13=refineRight3 w ∧ histRight3 13=histRight3 w := by decide +kernel
lemma refineRight3_iff_14 : ∀ w, refineRight4 14=refineRight4 w ↔ refineRight3 14=refineRight3 w ∧ histRight3 14=histRight3 w := by decide +kernel
lemma refineRight3_iff_15 : ∀ w, refineRight4 15=refineRight4 w ↔ refineRight3 15=refineRight3 w ∧ histRight3 15=histRight3 w := by decide +kernel
lemma refineRight3_iff_16 : ∀ w, refineRight4 16=refineRight4 w ↔ refineRight3 16=refineRight3 w ∧ histRight3 16=histRight3 w := by decide +kernel
lemma refineRight3_iff_17 : ∀ w, refineRight4 17=refineRight4 w ↔ refineRight3 17=refineRight3 w ∧ histRight3 17=histRight3 w := by decide +kernel
lemma refineRight3_iff_18 : ∀ w, refineRight4 18=refineRight4 w ↔ refineRight3 18=refineRight3 w ∧ histRight3 18=histRight3 w := by decide +kernel
lemma refineRight3_iff_19 : ∀ w, refineRight4 19=refineRight4 w ↔ refineRight3 19=refineRight3 w ∧ histRight3 19=histRight3 w := by decide +kernel
lemma refineRight3_iff_20 : ∀ w, refineRight4 20=refineRight4 w ↔ refineRight3 20=refineRight3 w ∧ histRight3 20=histRight3 w := by decide +kernel
lemma refineRight3_iff_21 : ∀ w, refineRight4 21=refineRight4 w ↔ refineRight3 21=refineRight3 w ∧ histRight3 21=histRight3 w := by decide +kernel
lemma refineRight3_iff : ∀ v w, refineRight4 v=refineRight4 w ↔ refineRight3 v=refineRight3 w ∧ histRight3 v=histRight3 w := by
  intro v; fin_cases v
  · exact refineRight3_iff_0
  · exact refineRight3_iff_1
  · exact refineRight3_iff_2
  · exact refineRight3_iff_3
  · exact refineRight3_iff_4
  · exact refineRight3_iff_5
  · exact refineRight3_iff_6
  · exact refineRight3_iff_7
  · exact refineRight3_iff_8
  · exact refineRight3_iff_9
  · exact refineRight3_iff_10
  · exact refineRight3_iff_11
  · exact refineRight3_iff_12
  · exact refineRight3_iff_13
  · exact refineRight3_iff_14
  · exact refineRight3_iff_15
  · exact refineRight3_iff_16
  · exact refineRight3_iff_17
  · exact refineRight3_iff_18
  · exact refineRight3_iff_19
  · exact refineRight3_iff_20
  · exact refineRight3_iff_21
lemma refineLeft_final : Function.Injective refineLeft4 := by decide +kernel
lemma refineRight_final : Function.Injective refineRight4 := by decide +kernel
end SidorenkoCounterexample

end

end OAI
