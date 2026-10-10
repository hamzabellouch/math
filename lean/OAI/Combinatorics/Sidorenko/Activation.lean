import OAI.Combinatorics.Sidorenko.GlobalMoments

namespace OAI


section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff

abbrev ActCorner := Fin 22 × Fin 3
def cornerPoint (k : ActCorner) : Fin 13 := faceVertex k.1 k.2
def cornerPairL (k : ActCorner) : Fin 33 := facePair k.1 (slotLeft k.2)
def cornerPairR (k : ActCorner) : Fin 33 := facePair k.1 (slotRight k.2)
def pairCorners (e : Fin 33) : Finset ActCorner :=
  Finset.univ.filter fun k => cornerPairL k=e ∨ cornerPairR k=e
def cornerMax (k : ActCorner) : Finset ActCorner := pairCorners (cornerPairL k) ∪ pairCorners (cornerPairR k)
def cornerGamma (k : ActCorner) : Finset ActCorner := pairCorners (cornerPairL k) ∆ pairCorners (cornerPairR k)

theorem pairCorners_mem (k : ActCorner) (e : Fin 33) :
    k∈pairCorners e ↔ cornerPairL k=e ∨ cornerPairR k=e := by simp [pairCorners]
def pairCornerTable : Fin 33 → Finset ActCorner := ![{(2,0), (2,1), (3,0), (3,1)},
  {(0,0), (0,2), (2,0), (2,2)},
  {(2,1), (2,2), (8,0), (8,1)},
  {(1,0), (1,2), (3,0), (3,2)},
  {(3,1), (3,2), (9,0), (9,2)},
  {(0,0), (0,1), (1,0), (1,1)},
  {(0,1), (0,2), (4,0), (4,1)},
  {(8,0), (8,2), (9,0), (9,1)},
  {(8,1), (8,2), (10,0), (10,1)},
  {(1,1), (1,2), (7,0), (7,1)},
  {(9,1), (9,2), (12,0), (12,2)},
  {(4,0), (4,2), (5,0), (5,2)},
  {(4,1), (4,2), (11,0), (11,1)},
  {(10,0), (10,2), (11,0), (11,2)},
  {(10,1), (10,2), (13,0), (13,2)},
  {(6,0), (6,2), (7,0), (7,2)},
  {(7,1), (7,2), (21,1), (21,2)},
  {(12,0), (12,1), (13,0), (13,1)},
  {(12,1), (12,2), (21,0), (21,1)},
  {(5,0), (5,1), (6,0), (6,1)},
  {(5,1), (5,2), (16,1), (16,2)},
  {(11,1), (11,2), (17,1), (17,2)},
  {(13,1), (13,2), (19,1), (19,2)},
  {(6,1), (6,2), (18,1), (18,2)},
  {(20,1), (20,2), (21,0), (21,2)},
  {(14,0), (14,2), (16,0), (16,1)},
  {(16,0), (16,2), (17,0), (17,1)},
  {(15,0), (15,2), (17,0), (17,2)},
  {(19,0), (19,1), (20,0), (20,1)},
  {(15,1), (15,2), (19,0), (19,2)},
  {(14,1), (14,2), (18,0), (18,1)},
  {(18,0), (18,2), (20,0), (20,2)},
  {(14,0), (14,1), (15,0), (15,1)}]
lemma pairCorners_table_0 : pairCorners 0=pairCornerTable 0 := by decide
lemma pairCorners_table_1 : pairCorners 1=pairCornerTable 1 := by decide
lemma pairCorners_table_2 : pairCorners 2=pairCornerTable 2 := by decide
lemma pairCorners_table_3 : pairCorners 3=pairCornerTable 3 := by decide
lemma pairCorners_table_4 : pairCorners 4=pairCornerTable 4 := by decide
lemma pairCorners_table_5 : pairCorners 5=pairCornerTable 5 := by decide
lemma pairCorners_table_6 : pairCorners 6=pairCornerTable 6 := by decide
lemma pairCorners_table_7 : pairCorners 7=pairCornerTable 7 := by decide
lemma pairCorners_table_8 : pairCorners 8=pairCornerTable 8 := by decide
lemma pairCorners_table_9 : pairCorners 9=pairCornerTable 9 := by decide
lemma pairCorners_table_10 : pairCorners 10=pairCornerTable 10 := by decide
lemma pairCorners_table_11 : pairCorners 11=pairCornerTable 11 := by decide
lemma pairCorners_table_12 : pairCorners 12=pairCornerTable 12 := by decide
lemma pairCorners_table_13 : pairCorners 13=pairCornerTable 13 := by decide
lemma pairCorners_table_14 : pairCorners 14=pairCornerTable 14 := by decide
lemma pairCorners_table_15 : pairCorners 15=pairCornerTable 15 := by decide
lemma pairCorners_table_16 : pairCorners 16=pairCornerTable 16 := by decide
lemma pairCorners_table_17 : pairCorners 17=pairCornerTable 17 := by decide
lemma pairCorners_table_18 : pairCorners 18=pairCornerTable 18 := by decide
lemma pairCorners_table_19 : pairCorners 19=pairCornerTable 19 := by decide
lemma pairCorners_table_20 : pairCorners 20=pairCornerTable 20 := by decide
lemma pairCorners_table_21 : pairCorners 21=pairCornerTable 21 := by decide
lemma pairCorners_table_22 : pairCorners 22=pairCornerTable 22 := by decide
lemma pairCorners_table_23 : pairCorners 23=pairCornerTable 23 := by decide
lemma pairCorners_table_24 : pairCorners 24=pairCornerTable 24 := by decide
lemma pairCorners_table_25 : pairCorners 25=pairCornerTable 25 := by decide
lemma pairCorners_table_26 : pairCorners 26=pairCornerTable 26 := by decide
lemma pairCorners_table_27 : pairCorners 27=pairCornerTable 27 := by decide
lemma pairCorners_table_28 : pairCorners 28=pairCornerTable 28 := by decide
lemma pairCorners_table_29 : pairCorners 29=pairCornerTable 29 := by decide
lemma pairCorners_table_30 : pairCorners 30=pairCornerTable 30 := by decide
lemma pairCorners_table_31 : pairCorners 31=pairCornerTable 31 := by decide
lemma pairCorners_table_32 : pairCorners 32=pairCornerTable 32 := by decide
theorem pairCorners_table (e : Fin 33) : pairCorners e=pairCornerTable e := by
  fin_cases e
  · exact pairCorners_table_0
  · exact pairCorners_table_1
  · exact pairCorners_table_2
  · exact pairCorners_table_3
  · exact pairCorners_table_4
  · exact pairCorners_table_5
  · exact pairCorners_table_6
  · exact pairCorners_table_7
  · exact pairCorners_table_8
  · exact pairCorners_table_9
  · exact pairCorners_table_10
  · exact pairCorners_table_11
  · exact pairCorners_table_12
  · exact pairCorners_table_13
  · exact pairCorners_table_14
  · exact pairCorners_table_15
  · exact pairCorners_table_16
  · exact pairCorners_table_17
  · exact pairCorners_table_18
  · exact pairCorners_table_19
  · exact pairCorners_table_20
  · exact pairCorners_table_21
  · exact pairCorners_table_22
  · exact pairCorners_table_23
  · exact pairCorners_table_24
  · exact pairCorners_table_25
  · exact pairCorners_table_26
  · exact pairCorners_table_27
  · exact pairCorners_table_28
  · exact pairCorners_table_29
  · exact pairCorners_table_30
  · exact pairCorners_table_31
  · exact pairCorners_table_32
theorem cornerPair_ne (k : ActCorner) : cornerPairL k≠cornerPairR k := by
  intro h
  have he := facePair_injective k.1 h
  have hn : ∀ k : Fin 3,slotLeft k≠slotRight k := by decide
  exact hn k.2 he
lemma pairCorners_inter_0_0 : pairCorners (cornerPairL (0,0)) ∩ pairCorners (cornerPairR (0,0))={(0,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_0_1 : pairCorners (cornerPairL (0,1)) ∩ pairCorners (cornerPairR (0,1))={(0,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_0_2 : pairCorners (cornerPairL (0,2)) ∩ pairCorners (cornerPairR (0,2))={(0,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_1_0 : pairCorners (cornerPairL (1,0)) ∩ pairCorners (cornerPairR (1,0))={(1,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_1_1 : pairCorners (cornerPairL (1,1)) ∩ pairCorners (cornerPairR (1,1))={(1,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_1_2 : pairCorners (cornerPairL (1,2)) ∩ pairCorners (cornerPairR (1,2))={(1,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_2_0 : pairCorners (cornerPairL (2,0)) ∩ pairCorners (cornerPairR (2,0))={(2,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_2_1 : pairCorners (cornerPairL (2,1)) ∩ pairCorners (cornerPairR (2,1))={(2,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_2_2 : pairCorners (cornerPairL (2,2)) ∩ pairCorners (cornerPairR (2,2))={(2,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_3_0 : pairCorners (cornerPairL (3,0)) ∩ pairCorners (cornerPairR (3,0))={(3,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_3_1 : pairCorners (cornerPairL (3,1)) ∩ pairCorners (cornerPairR (3,1))={(3,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_3_2 : pairCorners (cornerPairL (3,2)) ∩ pairCorners (cornerPairR (3,2))={(3,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_4_0 : pairCorners (cornerPairL (4,0)) ∩ pairCorners (cornerPairR (4,0))={(4,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_4_1 : pairCorners (cornerPairL (4,1)) ∩ pairCorners (cornerPairR (4,1))={(4,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_4_2 : pairCorners (cornerPairL (4,2)) ∩ pairCorners (cornerPairR (4,2))={(4,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_5_0 : pairCorners (cornerPairL (5,0)) ∩ pairCorners (cornerPairR (5,0))={(5,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_5_1 : pairCorners (cornerPairL (5,1)) ∩ pairCorners (cornerPairR (5,1))={(5,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_5_2 : pairCorners (cornerPairL (5,2)) ∩ pairCorners (cornerPairR (5,2))={(5,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_6_0 : pairCorners (cornerPairL (6,0)) ∩ pairCorners (cornerPairR (6,0))={(6,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_6_1 : pairCorners (cornerPairL (6,1)) ∩ pairCorners (cornerPairR (6,1))={(6,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_6_2 : pairCorners (cornerPairL (6,2)) ∩ pairCorners (cornerPairR (6,2))={(6,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_7_0 : pairCorners (cornerPairL (7,0)) ∩ pairCorners (cornerPairR (7,0))={(7,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_7_1 : pairCorners (cornerPairL (7,1)) ∩ pairCorners (cornerPairR (7,1))={(7,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_7_2 : pairCorners (cornerPairL (7,2)) ∩ pairCorners (cornerPairR (7,2))={(7,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_8_0 : pairCorners (cornerPairL (8,0)) ∩ pairCorners (cornerPairR (8,0))={(8,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_8_1 : pairCorners (cornerPairL (8,1)) ∩ pairCorners (cornerPairR (8,1))={(8,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_8_2 : pairCorners (cornerPairL (8,2)) ∩ pairCorners (cornerPairR (8,2))={(8,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_9_0 : pairCorners (cornerPairL (9,0)) ∩ pairCorners (cornerPairR (9,0))={(9,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_9_1 : pairCorners (cornerPairL (9,1)) ∩ pairCorners (cornerPairR (9,1))={(9,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_9_2 : pairCorners (cornerPairL (9,2)) ∩ pairCorners (cornerPairR (9,2))={(9,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_10_0 : pairCorners (cornerPairL (10,0)) ∩ pairCorners (cornerPairR (10,0))={(10,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_10_1 : pairCorners (cornerPairL (10,1)) ∩ pairCorners (cornerPairR (10,1))={(10,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_10_2 : pairCorners (cornerPairL (10,2)) ∩ pairCorners (cornerPairR (10,2))={(10,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_11_0 : pairCorners (cornerPairL (11,0)) ∩ pairCorners (cornerPairR (11,0))={(11,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_11_1 : pairCorners (cornerPairL (11,1)) ∩ pairCorners (cornerPairR (11,1))={(11,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_11_2 : pairCorners (cornerPairL (11,2)) ∩ pairCorners (cornerPairR (11,2))={(11,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_12_0 : pairCorners (cornerPairL (12,0)) ∩ pairCorners (cornerPairR (12,0))={(12,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_12_1 : pairCorners (cornerPairL (12,1)) ∩ pairCorners (cornerPairR (12,1))={(12,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_12_2 : pairCorners (cornerPairL (12,2)) ∩ pairCorners (cornerPairR (12,2))={(12,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_13_0 : pairCorners (cornerPairL (13,0)) ∩ pairCorners (cornerPairR (13,0))={(13,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_13_1 : pairCorners (cornerPairL (13,1)) ∩ pairCorners (cornerPairR (13,1))={(13,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_13_2 : pairCorners (cornerPairL (13,2)) ∩ pairCorners (cornerPairR (13,2))={(13,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_14_0 : pairCorners (cornerPairL (14,0)) ∩ pairCorners (cornerPairR (14,0))={(14,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_14_1 : pairCorners (cornerPairL (14,1)) ∩ pairCorners (cornerPairR (14,1))={(14,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_14_2 : pairCorners (cornerPairL (14,2)) ∩ pairCorners (cornerPairR (14,2))={(14,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_15_0 : pairCorners (cornerPairL (15,0)) ∩ pairCorners (cornerPairR (15,0))={(15,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_15_1 : pairCorners (cornerPairL (15,1)) ∩ pairCorners (cornerPairR (15,1))={(15,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_15_2 : pairCorners (cornerPairL (15,2)) ∩ pairCorners (cornerPairR (15,2))={(15,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_16_0 : pairCorners (cornerPairL (16,0)) ∩ pairCorners (cornerPairR (16,0))={(16,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_16_1 : pairCorners (cornerPairL (16,1)) ∩ pairCorners (cornerPairR (16,1))={(16,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_16_2 : pairCorners (cornerPairL (16,2)) ∩ pairCorners (cornerPairR (16,2))={(16,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_17_0 : pairCorners (cornerPairL (17,0)) ∩ pairCorners (cornerPairR (17,0))={(17,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_17_1 : pairCorners (cornerPairL (17,1)) ∩ pairCorners (cornerPairR (17,1))={(17,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_17_2 : pairCorners (cornerPairL (17,2)) ∩ pairCorners (cornerPairR (17,2))={(17,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_18_0 : pairCorners (cornerPairL (18,0)) ∩ pairCorners (cornerPairR (18,0))={(18,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_18_1 : pairCorners (cornerPairL (18,1)) ∩ pairCorners (cornerPairR (18,1))={(18,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_18_2 : pairCorners (cornerPairL (18,2)) ∩ pairCorners (cornerPairR (18,2))={(18,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_19_0 : pairCorners (cornerPairL (19,0)) ∩ pairCorners (cornerPairR (19,0))={(19,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_19_1 : pairCorners (cornerPairL (19,1)) ∩ pairCorners (cornerPairR (19,1))={(19,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_19_2 : pairCorners (cornerPairL (19,2)) ∩ pairCorners (cornerPairR (19,2))={(19,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_20_0 : pairCorners (cornerPairL (20,0)) ∩ pairCorners (cornerPairR (20,0))={(20,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_20_1 : pairCorners (cornerPairL (20,1)) ∩ pairCorners (cornerPairR (20,1))={(20,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_20_2 : pairCorners (cornerPairL (20,2)) ∩ pairCorners (cornerPairR (20,2))={(20,2)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_21_0 : pairCorners (cornerPairL (21,0)) ∩ pairCorners (cornerPairR (21,0))={(21,0)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_21_1 : pairCorners (cornerPairL (21,1)) ∩ pairCorners (cornerPairR (21,1))={(21,1)} := by
  simp only [pairCorners_table]
  decide
lemma pairCorners_inter_21_2 : pairCorners (cornerPairL (21,2)) ∩ pairCorners (cornerPairR (21,2))={(21,2)} := by
  simp only [pairCorners_table]
  decide
theorem pairCorners_inter (k : ActCorner) : pairCorners (cornerPairL k) ∩ pairCorners (cornerPairR k)={k} := by
  rcases k with ⟨j,k⟩
  fin_cases j <;> fin_cases k
  · exact pairCorners_inter_0_0
  · exact pairCorners_inter_0_1
  · exact pairCorners_inter_0_2
  · exact pairCorners_inter_1_0
  · exact pairCorners_inter_1_1
  · exact pairCorners_inter_1_2
  · exact pairCorners_inter_2_0
  · exact pairCorners_inter_2_1
  · exact pairCorners_inter_2_2
  · exact pairCorners_inter_3_0
  · exact pairCorners_inter_3_1
  · exact pairCorners_inter_3_2
  · exact pairCorners_inter_4_0
  · exact pairCorners_inter_4_1
  · exact pairCorners_inter_4_2
  · exact pairCorners_inter_5_0
  · exact pairCorners_inter_5_1
  · exact pairCorners_inter_5_2
  · exact pairCorners_inter_6_0
  · exact pairCorners_inter_6_1
  · exact pairCorners_inter_6_2
  · exact pairCorners_inter_7_0
  · exact pairCorners_inter_7_1
  · exact pairCorners_inter_7_2
  · exact pairCorners_inter_8_0
  · exact pairCorners_inter_8_1
  · exact pairCorners_inter_8_2
  · exact pairCorners_inter_9_0
  · exact pairCorners_inter_9_1
  · exact pairCorners_inter_9_2
  · exact pairCorners_inter_10_0
  · exact pairCorners_inter_10_1
  · exact pairCorners_inter_10_2
  · exact pairCorners_inter_11_0
  · exact pairCorners_inter_11_1
  · exact pairCorners_inter_11_2
  · exact pairCorners_inter_12_0
  · exact pairCorners_inter_12_1
  · exact pairCorners_inter_12_2
  · exact pairCorners_inter_13_0
  · exact pairCorners_inter_13_1
  · exact pairCorners_inter_13_2
  · exact pairCorners_inter_14_0
  · exact pairCorners_inter_14_1
  · exact pairCorners_inter_14_2
  · exact pairCorners_inter_15_0
  · exact pairCorners_inter_15_1
  · exact pairCorners_inter_15_2
  · exact pairCorners_inter_16_0
  · exact pairCorners_inter_16_1
  · exact pairCorners_inter_16_2
  · exact pairCorners_inter_17_0
  · exact pairCorners_inter_17_1
  · exact pairCorners_inter_17_2
  · exact pairCorners_inter_18_0
  · exact pairCorners_inter_18_1
  · exact pairCorners_inter_18_2
  · exact pairCorners_inter_19_0
  · exact pairCorners_inter_19_1
  · exact pairCorners_inter_19_2
  · exact pairCorners_inter_20_0
  · exact pairCorners_inter_20_1
  · exact pairCorners_inter_20_2
  · exact pairCorners_inter_21_0
  · exact pairCorners_inter_21_1
  · exact pairCorners_inter_21_2
theorem pairCorners_card (e : Fin 33) : (pairCorners e).card=4 := by
  rw [pairCorners_table]
  have ht : ∀ e,(pairCornerTable e).card=4 := by decide
  exact ht e

theorem cornerPairL_mem (k : ActCorner) : k∈pairCorners (cornerPairL k) := (pairCorners_mem _ _).mpr (Or.inl rfl)
theorem cornerPairR_mem (k : ActCorner) : k∈pairCorners (cornerPairR k) := (pairCorners_mem _ _).mpr (Or.inr rfl)

theorem cornerGamma_nonempty (k : ActCorner) : cornerGamma k≠∅ := by
  intro he
  have he : pairCorners (cornerPairL k)=pairCorners (cornerPairR k) := Finset.symmDiff_eq_empty.mp he
  have hi := pairCorners_inter k
  rw [he,Finset.inter_self] at hi
  have hc := pairCorners_card (cornerPairR k)
  rw [hi] at hc
  simp at hc

theorem cornerMax_not_sub (k : ActCorner) : ¬cornerMax k⊆cornerGamma k := by
  intro h
  have hk := h (Finset.mem_union_left _ (cornerPairL_mem k))
  have hn : k∉cornerGamma k := by
    simp only [cornerGamma,Finset.mem_symmDiff,cornerPairL_mem,cornerPairR_mem,not_true_eq_false,and_false,or_self,not_false_eq_true]
  exact hn hk
lemma supportIntersect_0 : cornerMax (2,0) ∩ cornerMax (2,1) ∩ cornerMax (3,0) ∩ cornerMax (3,1)=pairCorners 0 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_0 (k : ActCorner) : (∀ b∈pairCorners 0,k∈cornerMax b) ↔ k∈pairCorners 0 := by
  have h := Finset.ext_iff.mp supportIntersect_0 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_0] at h ⊢
  change (∀ b∈{(2,0),(2,1),(3,0),(3,1)},k∈cornerMax b) ↔ k∈pairCornerTable 0
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_1 : cornerMax (0,0) ∩ cornerMax (0,2) ∩ cornerMax (2,0) ∩ cornerMax (2,2)=pairCorners 1 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_1 (k : ActCorner) : (∀ b∈pairCorners 1,k∈cornerMax b) ↔ k∈pairCorners 1 := by
  have h := Finset.ext_iff.mp supportIntersect_1 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_1] at h ⊢
  change (∀ b∈{(0,0),(0,2),(2,0),(2,2)},k∈cornerMax b) ↔ k∈pairCornerTable 1
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_2 : cornerMax (2,1) ∩ cornerMax (2,2) ∩ cornerMax (8,0) ∩ cornerMax (8,1)=pairCorners 2 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_2 (k : ActCorner) : (∀ b∈pairCorners 2,k∈cornerMax b) ↔ k∈pairCorners 2 := by
  have h := Finset.ext_iff.mp supportIntersect_2 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_2] at h ⊢
  change (∀ b∈{(2,1),(2,2),(8,0),(8,1)},k∈cornerMax b) ↔ k∈pairCornerTable 2
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_3 : cornerMax (1,0) ∩ cornerMax (1,2) ∩ cornerMax (3,0) ∩ cornerMax (3,2)=pairCorners 3 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_3 (k : ActCorner) : (∀ b∈pairCorners 3,k∈cornerMax b) ↔ k∈pairCorners 3 := by
  have h := Finset.ext_iff.mp supportIntersect_3 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_3] at h ⊢
  change (∀ b∈{(1,0),(1,2),(3,0),(3,2)},k∈cornerMax b) ↔ k∈pairCornerTable 3
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_4 : cornerMax (3,1) ∩ cornerMax (3,2) ∩ cornerMax (9,0) ∩ cornerMax (9,2)=pairCorners 4 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_4 (k : ActCorner) : (∀ b∈pairCorners 4,k∈cornerMax b) ↔ k∈pairCorners 4 := by
  have h := Finset.ext_iff.mp supportIntersect_4 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_4] at h ⊢
  change (∀ b∈{(3,1),(3,2),(9,0),(9,2)},k∈cornerMax b) ↔ k∈pairCornerTable 4
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_5 : cornerMax (0,0) ∩ cornerMax (0,1) ∩ cornerMax (1,0) ∩ cornerMax (1,1)=pairCorners 5 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_5 (k : ActCorner) : (∀ b∈pairCorners 5,k∈cornerMax b) ↔ k∈pairCorners 5 := by
  have h := Finset.ext_iff.mp supportIntersect_5 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_5] at h ⊢
  change (∀ b∈{(0,0),(0,1),(1,0),(1,1)},k∈cornerMax b) ↔ k∈pairCornerTable 5
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_6 : cornerMax (0,1) ∩ cornerMax (0,2) ∩ cornerMax (4,0) ∩ cornerMax (4,1)=pairCorners 6 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_6 (k : ActCorner) : (∀ b∈pairCorners 6,k∈cornerMax b) ↔ k∈pairCorners 6 := by
  have h := Finset.ext_iff.mp supportIntersect_6 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_6] at h ⊢
  change (∀ b∈{(0,1),(0,2),(4,0),(4,1)},k∈cornerMax b) ↔ k∈pairCornerTable 6
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_7 : cornerMax (8,0) ∩ cornerMax (8,2) ∩ cornerMax (9,0) ∩ cornerMax (9,1)=pairCorners 7 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_7 (k : ActCorner) : (∀ b∈pairCorners 7,k∈cornerMax b) ↔ k∈pairCorners 7 := by
  have h := Finset.ext_iff.mp supportIntersect_7 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_7] at h ⊢
  change (∀ b∈{(8,0),(8,2),(9,0),(9,1)},k∈cornerMax b) ↔ k∈pairCornerTable 7
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_8 : cornerMax (8,1) ∩ cornerMax (8,2) ∩ cornerMax (10,0) ∩ cornerMax (10,1)=pairCorners 8 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_8 (k : ActCorner) : (∀ b∈pairCorners 8,k∈cornerMax b) ↔ k∈pairCorners 8 := by
  have h := Finset.ext_iff.mp supportIntersect_8 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_8] at h ⊢
  change (∀ b∈{(8,1),(8,2),(10,0),(10,1)},k∈cornerMax b) ↔ k∈pairCornerTable 8
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_9 : cornerMax (1,1) ∩ cornerMax (1,2) ∩ cornerMax (7,0) ∩ cornerMax (7,1)=pairCorners 9 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_9 (k : ActCorner) : (∀ b∈pairCorners 9,k∈cornerMax b) ↔ k∈pairCorners 9 := by
  have h := Finset.ext_iff.mp supportIntersect_9 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_9] at h ⊢
  change (∀ b∈{(1,1),(1,2),(7,0),(7,1)},k∈cornerMax b) ↔ k∈pairCornerTable 9
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_10 : cornerMax (9,1) ∩ cornerMax (9,2) ∩ cornerMax (12,0) ∩ cornerMax (12,2)=pairCorners 10 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_10 (k : ActCorner) : (∀ b∈pairCorners 10,k∈cornerMax b) ↔ k∈pairCorners 10 := by
  have h := Finset.ext_iff.mp supportIntersect_10 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_10] at h ⊢
  change (∀ b∈{(9,1),(9,2),(12,0),(12,2)},k∈cornerMax b) ↔ k∈pairCornerTable 10
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_11 : cornerMax (4,0) ∩ cornerMax (4,2) ∩ cornerMax (5,0) ∩ cornerMax (5,2)=pairCorners 11 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_11 (k : ActCorner) : (∀ b∈pairCorners 11,k∈cornerMax b) ↔ k∈pairCorners 11 := by
  have h := Finset.ext_iff.mp supportIntersect_11 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_11] at h ⊢
  change (∀ b∈{(4,0),(4,2),(5,0),(5,2)},k∈cornerMax b) ↔ k∈pairCornerTable 11
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_12 : cornerMax (4,1) ∩ cornerMax (4,2) ∩ cornerMax (11,0) ∩ cornerMax (11,1)=pairCorners 12 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_12 (k : ActCorner) : (∀ b∈pairCorners 12,k∈cornerMax b) ↔ k∈pairCorners 12 := by
  have h := Finset.ext_iff.mp supportIntersect_12 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_12] at h ⊢
  change (∀ b∈{(4,1),(4,2),(11,0),(11,1)},k∈cornerMax b) ↔ k∈pairCornerTable 12
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_13 : cornerMax (10,0) ∩ cornerMax (10,2) ∩ cornerMax (11,0) ∩ cornerMax (11,2)=pairCorners 13 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_13 (k : ActCorner) : (∀ b∈pairCorners 13,k∈cornerMax b) ↔ k∈pairCorners 13 := by
  have h := Finset.ext_iff.mp supportIntersect_13 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_13] at h ⊢
  change (∀ b∈{(10,0),(10,2),(11,0),(11,2)},k∈cornerMax b) ↔ k∈pairCornerTable 13
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_14 : cornerMax (10,1) ∩ cornerMax (10,2) ∩ cornerMax (13,0) ∩ cornerMax (13,2)=pairCorners 14 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_14 (k : ActCorner) : (∀ b∈pairCorners 14,k∈cornerMax b) ↔ k∈pairCorners 14 := by
  have h := Finset.ext_iff.mp supportIntersect_14 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_14] at h ⊢
  change (∀ b∈{(10,1),(10,2),(13,0),(13,2)},k∈cornerMax b) ↔ k∈pairCornerTable 14
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_15 : cornerMax (6,0) ∩ cornerMax (6,2) ∩ cornerMax (7,0) ∩ cornerMax (7,2)=pairCorners 15 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_15 (k : ActCorner) : (∀ b∈pairCorners 15,k∈cornerMax b) ↔ k∈pairCorners 15 := by
  have h := Finset.ext_iff.mp supportIntersect_15 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_15] at h ⊢
  change (∀ b∈{(6,0),(6,2),(7,0),(7,2)},k∈cornerMax b) ↔ k∈pairCornerTable 15
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_16 : cornerMax (7,1) ∩ cornerMax (7,2) ∩ cornerMax (21,1) ∩ cornerMax (21,2)=pairCorners 16 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_16 (k : ActCorner) : (∀ b∈pairCorners 16,k∈cornerMax b) ↔ k∈pairCorners 16 := by
  have h := Finset.ext_iff.mp supportIntersect_16 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_16] at h ⊢
  change (∀ b∈{(7,1),(7,2),(21,1),(21,2)},k∈cornerMax b) ↔ k∈pairCornerTable 16
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_17 : cornerMax (12,0) ∩ cornerMax (12,1) ∩ cornerMax (13,0) ∩ cornerMax (13,1)=pairCorners 17 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_17 (k : ActCorner) : (∀ b∈pairCorners 17,k∈cornerMax b) ↔ k∈pairCorners 17 := by
  have h := Finset.ext_iff.mp supportIntersect_17 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_17] at h ⊢
  change (∀ b∈{(12,0),(12,1),(13,0),(13,1)},k∈cornerMax b) ↔ k∈pairCornerTable 17
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_18 : cornerMax (12,1) ∩ cornerMax (12,2) ∩ cornerMax (21,0) ∩ cornerMax (21,1)=pairCorners 18 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_18 (k : ActCorner) : (∀ b∈pairCorners 18,k∈cornerMax b) ↔ k∈pairCorners 18 := by
  have h := Finset.ext_iff.mp supportIntersect_18 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_18] at h ⊢
  change (∀ b∈{(12,1),(12,2),(21,0),(21,1)},k∈cornerMax b) ↔ k∈pairCornerTable 18
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_19 : cornerMax (5,0) ∩ cornerMax (5,1) ∩ cornerMax (6,0) ∩ cornerMax (6,1)=pairCorners 19 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_19 (k : ActCorner) : (∀ b∈pairCorners 19,k∈cornerMax b) ↔ k∈pairCorners 19 := by
  have h := Finset.ext_iff.mp supportIntersect_19 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_19] at h ⊢
  change (∀ b∈{(5,0),(5,1),(6,0),(6,1)},k∈cornerMax b) ↔ k∈pairCornerTable 19
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_20 : cornerMax (5,1) ∩ cornerMax (5,2) ∩ cornerMax (16,1) ∩ cornerMax (16,2)=pairCorners 20 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_20 (k : ActCorner) : (∀ b∈pairCorners 20,k∈cornerMax b) ↔ k∈pairCorners 20 := by
  have h := Finset.ext_iff.mp supportIntersect_20 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_20] at h ⊢
  change (∀ b∈{(5,1),(5,2),(16,1),(16,2)},k∈cornerMax b) ↔ k∈pairCornerTable 20
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_21 : cornerMax (11,1) ∩ cornerMax (11,2) ∩ cornerMax (17,1) ∩ cornerMax (17,2)=pairCorners 21 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_21 (k : ActCorner) : (∀ b∈pairCorners 21,k∈cornerMax b) ↔ k∈pairCorners 21 := by
  have h := Finset.ext_iff.mp supportIntersect_21 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_21] at h ⊢
  change (∀ b∈{(11,1),(11,2),(17,1),(17,2)},k∈cornerMax b) ↔ k∈pairCornerTable 21
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_22 : cornerMax (13,1) ∩ cornerMax (13,2) ∩ cornerMax (19,1) ∩ cornerMax (19,2)=pairCorners 22 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_22 (k : ActCorner) : (∀ b∈pairCorners 22,k∈cornerMax b) ↔ k∈pairCorners 22 := by
  have h := Finset.ext_iff.mp supportIntersect_22 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_22] at h ⊢
  change (∀ b∈{(13,1),(13,2),(19,1),(19,2)},k∈cornerMax b) ↔ k∈pairCornerTable 22
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_23 : cornerMax (6,1) ∩ cornerMax (6,2) ∩ cornerMax (18,1) ∩ cornerMax (18,2)=pairCorners 23 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_23 (k : ActCorner) : (∀ b∈pairCorners 23,k∈cornerMax b) ↔ k∈pairCorners 23 := by
  have h := Finset.ext_iff.mp supportIntersect_23 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_23] at h ⊢
  change (∀ b∈{(6,1),(6,2),(18,1),(18,2)},k∈cornerMax b) ↔ k∈pairCornerTable 23
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_24 : cornerMax (20,1) ∩ cornerMax (20,2) ∩ cornerMax (21,0) ∩ cornerMax (21,2)=pairCorners 24 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_24 (k : ActCorner) : (∀ b∈pairCorners 24,k∈cornerMax b) ↔ k∈pairCorners 24 := by
  have h := Finset.ext_iff.mp supportIntersect_24 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_24] at h ⊢
  change (∀ b∈{(20,1),(20,2),(21,0),(21,2)},k∈cornerMax b) ↔ k∈pairCornerTable 24
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_25 : cornerMax (14,0) ∩ cornerMax (14,2) ∩ cornerMax (16,0) ∩ cornerMax (16,1)=pairCorners 25 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_25 (k : ActCorner) : (∀ b∈pairCorners 25,k∈cornerMax b) ↔ k∈pairCorners 25 := by
  have h := Finset.ext_iff.mp supportIntersect_25 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_25] at h ⊢
  change (∀ b∈{(14,0),(14,2),(16,0),(16,1)},k∈cornerMax b) ↔ k∈pairCornerTable 25
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_26 : cornerMax (16,0) ∩ cornerMax (16,2) ∩ cornerMax (17,0) ∩ cornerMax (17,1)=pairCorners 26 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_26 (k : ActCorner) : (∀ b∈pairCorners 26,k∈cornerMax b) ↔ k∈pairCorners 26 := by
  have h := Finset.ext_iff.mp supportIntersect_26 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_26] at h ⊢
  change (∀ b∈{(16,0),(16,2),(17,0),(17,1)},k∈cornerMax b) ↔ k∈pairCornerTable 26
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_27 : cornerMax (15,0) ∩ cornerMax (15,2) ∩ cornerMax (17,0) ∩ cornerMax (17,2)=pairCorners 27 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_27 (k : ActCorner) : (∀ b∈pairCorners 27,k∈cornerMax b) ↔ k∈pairCorners 27 := by
  have h := Finset.ext_iff.mp supportIntersect_27 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_27] at h ⊢
  change (∀ b∈{(15,0),(15,2),(17,0),(17,2)},k∈cornerMax b) ↔ k∈pairCornerTable 27
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_28 : cornerMax (19,0) ∩ cornerMax (19,1) ∩ cornerMax (20,0) ∩ cornerMax (20,1)=pairCorners 28 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_28 (k : ActCorner) : (∀ b∈pairCorners 28,k∈cornerMax b) ↔ k∈pairCorners 28 := by
  have h := Finset.ext_iff.mp supportIntersect_28 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_28] at h ⊢
  change (∀ b∈{(19,0),(19,1),(20,0),(20,1)},k∈cornerMax b) ↔ k∈pairCornerTable 28
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_29 : cornerMax (15,1) ∩ cornerMax (15,2) ∩ cornerMax (19,0) ∩ cornerMax (19,2)=pairCorners 29 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_29 (k : ActCorner) : (∀ b∈pairCorners 29,k∈cornerMax b) ↔ k∈pairCorners 29 := by
  have h := Finset.ext_iff.mp supportIntersect_29 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_29] at h ⊢
  change (∀ b∈{(15,1),(15,2),(19,0),(19,2)},k∈cornerMax b) ↔ k∈pairCornerTable 29
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_30 : cornerMax (14,1) ∩ cornerMax (14,2) ∩ cornerMax (18,0) ∩ cornerMax (18,1)=pairCorners 30 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_30 (k : ActCorner) : (∀ b∈pairCorners 30,k∈cornerMax b) ↔ k∈pairCorners 30 := by
  have h := Finset.ext_iff.mp supportIntersect_30 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_30] at h ⊢
  change (∀ b∈{(14,1),(14,2),(18,0),(18,1)},k∈cornerMax b) ↔ k∈pairCornerTable 30
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_31 : cornerMax (18,0) ∩ cornerMax (18,2) ∩ cornerMax (20,0) ∩ cornerMax (20,2)=pairCorners 31 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_31 (k : ActCorner) : (∀ b∈pairCorners 31,k∈cornerMax b) ↔ k∈pairCorners 31 := by
  have h := Finset.ext_iff.mp supportIntersect_31 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_31] at h ⊢
  change (∀ b∈{(18,0),(18,2),(20,0),(20,2)},k∈cornerMax b) ↔ k∈pairCornerTable 31
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
lemma supportIntersect_32 : cornerMax (14,0) ∩ cornerMax (14,1) ∩ cornerMax (15,0) ∩ cornerMax (15,1)=pairCorners 32 := by
  simp only [cornerMax,pairCorners_table]
  decide
lemma corner_support_32 (k : ActCorner) : (∀ b∈pairCorners 32,k∈cornerMax b) ↔ k∈pairCorners 32 := by
  have h := Finset.ext_iff.mp supportIntersect_32 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_32] at h ⊢
  change (∀ b∈{(14,0),(14,1),(15,0),(15,1)},k∈cornerMax b) ↔ k∈pairCornerTable 32
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto
theorem corner_support (e : Fin 33) (k : ActCorner) : (∀ b∈pairCorners e,k∈cornerMax b) ↔ k∈pairCorners e := by
  fin_cases e
  · exact corner_support_0 k
  · exact corner_support_1 k
  · exact corner_support_2 k
  · exact corner_support_3 k
  · exact corner_support_4 k
  · exact corner_support_5 k
  · exact corner_support_6 k
  · exact corner_support_7 k
  · exact corner_support_8 k
  · exact corner_support_9 k
  · exact corner_support_10 k
  · exact corner_support_11 k
  · exact corner_support_12 k
  · exact corner_support_13 k
  · exact corner_support_14 k
  · exact corner_support_15 k
  · exact corner_support_16 k
  · exact corner_support_17 k
  · exact corner_support_18 k
  · exact corner_support_19 k
  · exact corner_support_20 k
  · exact corner_support_21 k
  · exact corner_support_22 k
  · exact corner_support_23 k
  · exact corner_support_24 k
  · exact corner_support_25 k
  · exact corner_support_26 k
  · exact corner_support_27 k
  · exact corner_support_28 k
  · exact corner_support_29 k
  · exact corner_support_30 k
  · exact corner_support_31 k
  · exact corner_support_32 k

theorem cornerGamma_sub (k : ActCorner) : cornerGamma k⊆cornerMax k :=
  Finset.symmDiff_subset_union

def cornerSigma (k : ActCorner) : ℝ := if k=(0,0) then -1 else 1
lemma cornerSigma_abs (k : ActCorner) : |cornerSigma k|=1 := by unfold cornerSigma; split <;> norm_num
noncomputable def cornerLaw (k : ActCorner) : FiniteLaw (Activation ActCorner) :=
  baseActivation (cornerMax k) (cornerGamma k) (cornerGamma_nonempty k) (cornerSigma k/2)
    (by rw [abs_div,cornerSigma_abs]; norm_num)
lemma cornerLaw_zero (k : ActCorner) (α : Finset ActCorner) (hα : α≠∅) :
    (cornerLaw k).mean (activationPhi α)=0 :=
  baseActivation_zero _ _ _ _ (cornerGamma_sub k) _ _ hα
lemma cornerLaw_moment (k : ActCorner) (α β : Finset ActCorner) :
    activationMoment (cornerLaw k) α β=
    (1/2)*(if α∪β⊆cornerMax k then (if α=β then 1 else 0)+(cornerSigma k/2)*(if α ∆ β=cornerGamma k then 1 else 0) else 0)+
    (1/2)*(if α∪β⊆cornerGamma k then (if α=β then 1 else 0)-(cornerSigma k/2)*(if α ∆ β=cornerGamma k then 1 else 0) else 0) :=
  baseActivation_moment ..
lemma cornerLaw_support (k : ActCorner) (α β : Finset ActCorner)
    (h : activationMoment (cornerLaw k) α β≠0) : α∪β⊆cornerMax k := by
  by_contra hn
  have hn' : ¬α∪β⊆cornerGamma k := fun h => hn (h.trans (cornerGamma_sub k))
  rw [cornerLaw_moment] at h
  simp only [hn,hn',ite_false,mul_zero,add_zero,ne_self_iff_false] at h
lemma cornerLaw_disjoint (k : ActCorner) (α β : Finset ActCorner)
    (hd : Disjoint α β) (hn : α∪β≠∅) : activationMoment (cornerLaw k) α β=0 :=
  activationMoment_disjoint _ (cornerLaw_zero k) α β hd hn
lemma cornerLaw_value (k : ActCorner) :
    activationMoment (cornerLaw k) (pairCorners (cornerPairL k)) (pairCorners (cornerPairR k))=cornerSigma k/4 := by
  have hn : pairCorners (cornerPairL k)≠pairCorners (cornerPairR k) := by
    intro h
    have hi := pairCorners_inter k
    rw [h,Finset.inter_self] at hi
    have hc := pairCorners_card (cornerPairR k)
    rw [hi] at hc
    simp at hc
  rw [cornerLaw_moment]
  change (1/2)*(if cornerMax k⊆cornerMax k then (if _ then 1 else 0)+(cornerSigma k/2)*(if cornerGamma k=cornerGamma k then 1 else 0) else 0)+
    (1/2)*(if cornerMax k⊆cornerGamma k then (if _ then 1 else 0)-(cornerSigma k/2)*(if cornerGamma k=cornerGamma k then 1 else 0) else 0)=_
  simp only [le_refl,ite_true,hn,ite_false,cornerMax_not_sub,mul_one,zero_add,mul_zero,add_zero]
  ring
end SidorenkoCounterexample

end

end OAI
