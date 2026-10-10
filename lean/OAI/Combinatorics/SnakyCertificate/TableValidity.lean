import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate

theorem table_size : table.size = 610 := by
  simp only [table, Array.size_append]
  decide +kernel

abbrev TableEntryOk (k : ℕ) : Prop :=
  let e := table[k]?.getD emptyEntry
  e.index = k + 6 ∧ e.terms ≠ [] ∧ ∀ t ∈ e.terms, t.child < e.index

theorem table_entries_block_0 : ∀ j : Fin 10, TableEntryOk (0 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_0 : ∀ k, 0 ≤ k → k < 10 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 0) (n := 10) table_entries_block_0

theorem table_entries_block_10 : ∀ j : Fin 10, TableEntryOk (10 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_10 : ∀ k, 10 ≤ k → k < 20 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 10) (n := 10) table_entries_block_10

theorem table_entries_block_20 : ∀ j : Fin 10, TableEntryOk (20 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_20 : ∀ k, 20 ≤ k → k < 30 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 20) (n := 10) table_entries_block_20

theorem table_entries_block_30 : ∀ j : Fin 10, TableEntryOk (30 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_30 : ∀ k, 30 ≤ k → k < 40 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 30) (n := 10) table_entries_block_30

theorem table_entries_block_40 : ∀ j : Fin 10, TableEntryOk (40 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_40 : ∀ k, 40 ≤ k → k < 50 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 40) (n := 10) table_entries_block_40

theorem table_entries_block_50 : ∀ j : Fin 10, TableEntryOk (50 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_50 : ∀ k, 50 ≤ k → k < 60 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 50) (n := 10) table_entries_block_50

theorem table_entries_block_60 : ∀ j : Fin 10, TableEntryOk (60 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_60 : ∀ k, 60 ≤ k → k < 70 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 60) (n := 10) table_entries_block_60

theorem table_entries_block_70 : ∀ j : Fin 10, TableEntryOk (70 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_70 : ∀ k, 70 ≤ k → k < 80 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 70) (n := 10) table_entries_block_70

theorem table_entries_block_80 : ∀ j : Fin 10, TableEntryOk (80 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_80 : ∀ k, 80 ≤ k → k < 90 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 80) (n := 10) table_entries_block_80

theorem table_entries_block_90 : ∀ j : Fin 10, TableEntryOk (90 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_90 : ∀ k, 90 ≤ k → k < 100 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 90) (n := 10) table_entries_block_90

theorem table_entries_block_100 : ∀ j : Fin 10, TableEntryOk (100 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_100 : ∀ k, 100 ≤ k → k < 110 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 100) (n := 10) table_entries_block_100

theorem table_entries_block_110 : ∀ j : Fin 10, TableEntryOk (110 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_110 : ∀ k, 110 ≤ k → k < 120 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 110) (n := 10) table_entries_block_110

theorem table_entries_block_120 : ∀ j : Fin 10, TableEntryOk (120 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_120 : ∀ k, 120 ≤ k → k < 130 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 120) (n := 10) table_entries_block_120

theorem table_entries_block_130 : ∀ j : Fin 10, TableEntryOk (130 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_130 : ∀ k, 130 ≤ k → k < 140 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 130) (n := 10) table_entries_block_130

theorem table_entries_block_140 : ∀ j : Fin 10, TableEntryOk (140 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_140 : ∀ k, 140 ≤ k → k < 150 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 140) (n := 10) table_entries_block_140

theorem table_entries_block_150 : ∀ j : Fin 10, TableEntryOk (150 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_150 : ∀ k, 150 ≤ k → k < 160 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 150) (n := 10) table_entries_block_150

theorem table_entries_block_160 : ∀ j : Fin 10, TableEntryOk (160 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_160 : ∀ k, 160 ≤ k → k < 170 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 160) (n := 10) table_entries_block_160

theorem table_entries_block_170 : ∀ j : Fin 10, TableEntryOk (170 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_170 : ∀ k, 170 ≤ k → k < 180 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 170) (n := 10) table_entries_block_170

theorem table_entries_block_180 : ∀ j : Fin 10, TableEntryOk (180 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_180 : ∀ k, 180 ≤ k → k < 190 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 180) (n := 10) table_entries_block_180

theorem table_entries_block_190 : ∀ j : Fin 10, TableEntryOk (190 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_190 : ∀ k, 190 ≤ k → k < 200 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 190) (n := 10) table_entries_block_190

theorem table_entries_block_200 : ∀ j : Fin 10, TableEntryOk (200 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_200 : ∀ k, 200 ≤ k → k < 210 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 200) (n := 10) table_entries_block_200

theorem table_entries_block_210 : ∀ j : Fin 10, TableEntryOk (210 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_210 : ∀ k, 210 ≤ k → k < 220 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 210) (n := 10) table_entries_block_210

theorem table_entries_block_220 : ∀ j : Fin 10, TableEntryOk (220 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_220 : ∀ k, 220 ≤ k → k < 230 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 220) (n := 10) table_entries_block_220

theorem table_entries_block_230 : ∀ j : Fin 10, TableEntryOk (230 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_230 : ∀ k, 230 ≤ k → k < 240 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 230) (n := 10) table_entries_block_230

theorem table_entries_block_240 : ∀ j : Fin 10, TableEntryOk (240 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_240 : ∀ k, 240 ≤ k → k < 250 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 240) (n := 10) table_entries_block_240

theorem table_entries_block_250 : ∀ j : Fin 10, TableEntryOk (250 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_250 : ∀ k, 250 ≤ k → k < 260 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 250) (n := 10) table_entries_block_250

theorem table_entries_block_260 : ∀ j : Fin 10, TableEntryOk (260 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_260 : ∀ k, 260 ≤ k → k < 270 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 260) (n := 10) table_entries_block_260

theorem table_entries_block_270 : ∀ j : Fin 10, TableEntryOk (270 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_270 : ∀ k, 270 ≤ k → k < 280 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 270) (n := 10) table_entries_block_270

theorem table_entries_block_280 : ∀ j : Fin 10, TableEntryOk (280 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_280 : ∀ k, 280 ≤ k → k < 290 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 280) (n := 10) table_entries_block_280

theorem table_entries_block_290 : ∀ j : Fin 10, TableEntryOk (290 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_290 : ∀ k, 290 ≤ k → k < 300 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 290) (n := 10) table_entries_block_290

theorem table_entries_block_300 : ∀ j : Fin 10, TableEntryOk (300 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_300 : ∀ k, 300 ≤ k → k < 310 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 300) (n := 10) table_entries_block_300

theorem table_entries_block_310 : ∀ j : Fin 10, TableEntryOk (310 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_310 : ∀ k, 310 ≤ k → k < 320 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 310) (n := 10) table_entries_block_310

theorem table_entries_block_320 : ∀ j : Fin 10, TableEntryOk (320 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_320 : ∀ k, 320 ≤ k → k < 330 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 320) (n := 10) table_entries_block_320

theorem table_entries_block_330 : ∀ j : Fin 10, TableEntryOk (330 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_330 : ∀ k, 330 ≤ k → k < 340 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 330) (n := 10) table_entries_block_330

theorem table_entries_block_340 : ∀ j : Fin 10, TableEntryOk (340 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_340 : ∀ k, 340 ≤ k → k < 350 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 340) (n := 10) table_entries_block_340

theorem table_entries_block_350 : ∀ j : Fin 10, TableEntryOk (350 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_350 : ∀ k, 350 ≤ k → k < 360 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 350) (n := 10) table_entries_block_350

theorem table_entries_block_360 : ∀ j : Fin 10, TableEntryOk (360 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_360 : ∀ k, 360 ≤ k → k < 370 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 360) (n := 10) table_entries_block_360

theorem table_entries_block_370 : ∀ j : Fin 10, TableEntryOk (370 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_370 : ∀ k, 370 ≤ k → k < 380 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 370) (n := 10) table_entries_block_370

theorem table_entries_block_380 : ∀ j : Fin 10, TableEntryOk (380 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_380 : ∀ k, 380 ≤ k → k < 390 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 380) (n := 10) table_entries_block_380

theorem table_entries_block_390 : ∀ j : Fin 10, TableEntryOk (390 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_390 : ∀ k, 390 ≤ k → k < 400 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 390) (n := 10) table_entries_block_390

theorem table_entries_block_400 : ∀ j : Fin 10, TableEntryOk (400 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_400 : ∀ k, 400 ≤ k → k < 410 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 400) (n := 10) table_entries_block_400

theorem table_entries_block_410 : ∀ j : Fin 10, TableEntryOk (410 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_410 : ∀ k, 410 ≤ k → k < 420 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 410) (n := 10) table_entries_block_410

theorem table_entries_block_420 : ∀ j : Fin 10, TableEntryOk (420 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_420 : ∀ k, 420 ≤ k → k < 430 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 420) (n := 10) table_entries_block_420

theorem table_entries_block_430 : ∀ j : Fin 10, TableEntryOk (430 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_430 : ∀ k, 430 ≤ k → k < 440 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 430) (n := 10) table_entries_block_430

theorem table_entries_block_440 : ∀ j : Fin 10, TableEntryOk (440 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_440 : ∀ k, 440 ≤ k → k < 450 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 440) (n := 10) table_entries_block_440

theorem table_entries_block_450 : ∀ j : Fin 10, TableEntryOk (450 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_450 : ∀ k, 450 ≤ k → k < 460 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 450) (n := 10) table_entries_block_450

theorem table_entries_block_460 : ∀ j : Fin 10, TableEntryOk (460 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_460 : ∀ k, 460 ≤ k → k < 470 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 460) (n := 10) table_entries_block_460

theorem table_entries_block_470 : ∀ j : Fin 10, TableEntryOk (470 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_470 : ∀ k, 470 ≤ k → k < 480 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 470) (n := 10) table_entries_block_470

theorem table_entries_block_480 : ∀ j : Fin 10, TableEntryOk (480 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_480 : ∀ k, 480 ≤ k → k < 490 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 480) (n := 10) table_entries_block_480

theorem table_entries_block_490 : ∀ j : Fin 10, TableEntryOk (490 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_490 : ∀ k, 490 ≤ k → k < 500 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 490) (n := 10) table_entries_block_490

theorem table_entries_block_500 : ∀ j : Fin 10, TableEntryOk (500 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_500 : ∀ k, 500 ≤ k → k < 510 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 500) (n := 10) table_entries_block_500

theorem table_entries_block_510 : ∀ j : Fin 10, TableEntryOk (510 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_510 : ∀ k, 510 ≤ k → k < 520 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 510) (n := 10) table_entries_block_510

theorem table_entries_block_520 : ∀ j : Fin 10, TableEntryOk (520 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_520 : ∀ k, 520 ≤ k → k < 530 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 520) (n := 10) table_entries_block_520

theorem table_entries_block_530 : ∀ j : Fin 10, TableEntryOk (530 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_530 : ∀ k, 530 ≤ k → k < 540 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 530) (n := 10) table_entries_block_530

theorem table_entries_block_540 : ∀ j : Fin 10, TableEntryOk (540 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_540 : ∀ k, 540 ≤ k → k < 550 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 540) (n := 10) table_entries_block_540

theorem table_entries_block_550 : ∀ j : Fin 10, TableEntryOk (550 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_550 : ∀ k, 550 ≤ k → k < 560 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 550) (n := 10) table_entries_block_550

theorem table_entries_block_560 : ∀ j : Fin 10, TableEntryOk (560 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_560 : ∀ k, 560 ≤ k → k < 570 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 560) (n := 10) table_entries_block_560

theorem table_entries_block_570 : ∀ j : Fin 10, TableEntryOk (570 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_570 : ∀ k, 570 ≤ k → k < 580 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 570) (n := 10) table_entries_block_570

theorem table_entries_block_580 : ∀ j : Fin 10, TableEntryOk (580 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_580 : ∀ k, 580 ≤ k → k < 590 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 580) (n := 10) table_entries_block_580

theorem table_entries_block_590 : ∀ j : Fin 10, TableEntryOk (590 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_590 : ∀ k, 590 ≤ k → k < 600 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 590) (n := 10) table_entries_block_590

theorem table_entries_block_600 : ∀ j : Fin 10, TableEntryOk (600 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_600 : ∀ k, 600 ≤ k → k < 610 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 600) (n := 10) table_entries_block_600

theorem table_entries_range_10_30 : ∀ i, 10 ≤ i → i < 30 → TableEntryOk i :=
  merge_ranges table_entries_range_10 table_entries_range_20

theorem table_entries_range_0_30 : ∀ i, 0 ≤ i → i < 30 → TableEntryOk i :=
  merge_ranges table_entries_range_0 table_entries_range_10_30

theorem table_entries_range_30_50 : ∀ i, 30 ≤ i → i < 50 → TableEntryOk i :=
  merge_ranges table_entries_range_30 table_entries_range_40

theorem table_entries_range_50_70 : ∀ i, 50 ≤ i → i < 70 → TableEntryOk i :=
  merge_ranges table_entries_range_50 table_entries_range_60

theorem table_entries_range_30_70 : ∀ i, 30 ≤ i → i < 70 → TableEntryOk i :=
  merge_ranges table_entries_range_30_50 table_entries_range_50_70

theorem table_entries_range_0_70 : ∀ i, 0 ≤ i → i < 70 → TableEntryOk i :=
  merge_ranges table_entries_range_0_30 table_entries_range_30_70

theorem table_entries_range_70_90 : ∀ i, 70 ≤ i → i < 90 → TableEntryOk i :=
  merge_ranges table_entries_range_70 table_entries_range_80

theorem table_entries_range_90_110 : ∀ i, 90 ≤ i → i < 110 → TableEntryOk i :=
  merge_ranges table_entries_range_90 table_entries_range_100

theorem table_entries_range_70_110 : ∀ i, 70 ≤ i → i < 110 → TableEntryOk i :=
  merge_ranges table_entries_range_70_90 table_entries_range_90_110

theorem table_entries_range_110_130 : ∀ i, 110 ≤ i → i < 130 → TableEntryOk i :=
  merge_ranges table_entries_range_110 table_entries_range_120

theorem table_entries_range_130_150 : ∀ i, 130 ≤ i → i < 150 → TableEntryOk i :=
  merge_ranges table_entries_range_130 table_entries_range_140

theorem table_entries_range_110_150 : ∀ i, 110 ≤ i → i < 150 → TableEntryOk i :=
  merge_ranges table_entries_range_110_130 table_entries_range_130_150

theorem table_entries_range_70_150 : ∀ i, 70 ≤ i → i < 150 → TableEntryOk i :=
  merge_ranges table_entries_range_70_110 table_entries_range_110_150

theorem table_entries_range_0_150 : ∀ i, 0 ≤ i → i < 150 → TableEntryOk i :=
  merge_ranges table_entries_range_0_70 table_entries_range_70_150

theorem table_entries_range_160_180 : ∀ i, 160 ≤ i → i < 180 → TableEntryOk i :=
  merge_ranges table_entries_range_160 table_entries_range_170

theorem table_entries_range_150_180 : ∀ i, 150 ≤ i → i < 180 → TableEntryOk i :=
  merge_ranges table_entries_range_150 table_entries_range_160_180

theorem table_entries_range_180_200 : ∀ i, 180 ≤ i → i < 200 → TableEntryOk i :=
  merge_ranges table_entries_range_180 table_entries_range_190

theorem table_entries_range_200_220 : ∀ i, 200 ≤ i → i < 220 → TableEntryOk i :=
  merge_ranges table_entries_range_200 table_entries_range_210

theorem table_entries_range_180_220 : ∀ i, 180 ≤ i → i < 220 → TableEntryOk i :=
  merge_ranges table_entries_range_180_200 table_entries_range_200_220

theorem table_entries_range_150_220 : ∀ i, 150 ≤ i → i < 220 → TableEntryOk i :=
  merge_ranges table_entries_range_150_180 table_entries_range_180_220

theorem table_entries_range_220_240 : ∀ i, 220 ≤ i → i < 240 → TableEntryOk i :=
  merge_ranges table_entries_range_220 table_entries_range_230

theorem table_entries_range_240_260 : ∀ i, 240 ≤ i → i < 260 → TableEntryOk i :=
  merge_ranges table_entries_range_240 table_entries_range_250

theorem table_entries_range_220_260 : ∀ i, 220 ≤ i → i < 260 → TableEntryOk i :=
  merge_ranges table_entries_range_220_240 table_entries_range_240_260

theorem table_entries_range_260_280 : ∀ i, 260 ≤ i → i < 280 → TableEntryOk i :=
  merge_ranges table_entries_range_260 table_entries_range_270

theorem table_entries_range_280_300 : ∀ i, 280 ≤ i → i < 300 → TableEntryOk i :=
  merge_ranges table_entries_range_280 table_entries_range_290

theorem table_entries_range_260_300 : ∀ i, 260 ≤ i → i < 300 → TableEntryOk i :=
  merge_ranges table_entries_range_260_280 table_entries_range_280_300

theorem table_entries_range_220_300 : ∀ i, 220 ≤ i → i < 300 → TableEntryOk i :=
  merge_ranges table_entries_range_220_260 table_entries_range_260_300

theorem table_entries_range_150_300 : ∀ i, 150 ≤ i → i < 300 → TableEntryOk i :=
  merge_ranges table_entries_range_150_220 table_entries_range_220_300

theorem table_entries_range_0_300 : ∀ i, 0 ≤ i → i < 300 → TableEntryOk i :=
  merge_ranges table_entries_range_0_150 table_entries_range_150_300

theorem table_entries_range_310_330 : ∀ i, 310 ≤ i → i < 330 → TableEntryOk i :=
  merge_ranges table_entries_range_310 table_entries_range_320

theorem table_entries_range_300_330 : ∀ i, 300 ≤ i → i < 330 → TableEntryOk i :=
  merge_ranges table_entries_range_300 table_entries_range_310_330

theorem table_entries_range_330_350 : ∀ i, 330 ≤ i → i < 350 → TableEntryOk i :=
  merge_ranges table_entries_range_330 table_entries_range_340

theorem table_entries_range_350_370 : ∀ i, 350 ≤ i → i < 370 → TableEntryOk i :=
  merge_ranges table_entries_range_350 table_entries_range_360

theorem table_entries_range_330_370 : ∀ i, 330 ≤ i → i < 370 → TableEntryOk i :=
  merge_ranges table_entries_range_330_350 table_entries_range_350_370

theorem table_entries_range_300_370 : ∀ i, 300 ≤ i → i < 370 → TableEntryOk i :=
  merge_ranges table_entries_range_300_330 table_entries_range_330_370

theorem table_entries_range_370_390 : ∀ i, 370 ≤ i → i < 390 → TableEntryOk i :=
  merge_ranges table_entries_range_370 table_entries_range_380

theorem table_entries_range_390_410 : ∀ i, 390 ≤ i → i < 410 → TableEntryOk i :=
  merge_ranges table_entries_range_390 table_entries_range_400

theorem table_entries_range_370_410 : ∀ i, 370 ≤ i → i < 410 → TableEntryOk i :=
  merge_ranges table_entries_range_370_390 table_entries_range_390_410

theorem table_entries_range_410_430 : ∀ i, 410 ≤ i → i < 430 → TableEntryOk i :=
  merge_ranges table_entries_range_410 table_entries_range_420

theorem table_entries_range_430_450 : ∀ i, 430 ≤ i → i < 450 → TableEntryOk i :=
  merge_ranges table_entries_range_430 table_entries_range_440

theorem table_entries_range_410_450 : ∀ i, 410 ≤ i → i < 450 → TableEntryOk i :=
  merge_ranges table_entries_range_410_430 table_entries_range_430_450

theorem table_entries_range_370_450 : ∀ i, 370 ≤ i → i < 450 → TableEntryOk i :=
  merge_ranges table_entries_range_370_410 table_entries_range_410_450

theorem table_entries_range_300_450 : ∀ i, 300 ≤ i → i < 450 → TableEntryOk i :=
  merge_ranges table_entries_range_300_370 table_entries_range_370_450

theorem table_entries_range_450_470 : ∀ i, 450 ≤ i → i < 470 → TableEntryOk i :=
  merge_ranges table_entries_range_450 table_entries_range_460

theorem table_entries_range_470_490 : ∀ i, 470 ≤ i → i < 490 → TableEntryOk i :=
  merge_ranges table_entries_range_470 table_entries_range_480

theorem table_entries_range_450_490 : ∀ i, 450 ≤ i → i < 490 → TableEntryOk i :=
  merge_ranges table_entries_range_450_470 table_entries_range_470_490

theorem table_entries_range_490_510 : ∀ i, 490 ≤ i → i < 510 → TableEntryOk i :=
  merge_ranges table_entries_range_490 table_entries_range_500

theorem table_entries_range_510_530 : ∀ i, 510 ≤ i → i < 530 → TableEntryOk i :=
  merge_ranges table_entries_range_510 table_entries_range_520

theorem table_entries_range_490_530 : ∀ i, 490 ≤ i → i < 530 → TableEntryOk i :=
  merge_ranges table_entries_range_490_510 table_entries_range_510_530

theorem table_entries_range_450_530 : ∀ i, 450 ≤ i → i < 530 → TableEntryOk i :=
  merge_ranges table_entries_range_450_490 table_entries_range_490_530

theorem table_entries_range_530_550 : ∀ i, 530 ≤ i → i < 550 → TableEntryOk i :=
  merge_ranges table_entries_range_530 table_entries_range_540

theorem table_entries_range_550_570 : ∀ i, 550 ≤ i → i < 570 → TableEntryOk i :=
  merge_ranges table_entries_range_550 table_entries_range_560

theorem table_entries_range_530_570 : ∀ i, 530 ≤ i → i < 570 → TableEntryOk i :=
  merge_ranges table_entries_range_530_550 table_entries_range_550_570

theorem table_entries_range_570_590 : ∀ i, 570 ≤ i → i < 590 → TableEntryOk i :=
  merge_ranges table_entries_range_570 table_entries_range_580

theorem table_entries_range_590_610 : ∀ i, 590 ≤ i → i < 610 → TableEntryOk i :=
  merge_ranges table_entries_range_590 table_entries_range_600

theorem table_entries_range_570_610 : ∀ i, 570 ≤ i → i < 610 → TableEntryOk i :=
  merge_ranges table_entries_range_570_590 table_entries_range_590_610

theorem table_entries_range_530_610 : ∀ i, 530 ≤ i → i < 610 → TableEntryOk i :=
  merge_ranges table_entries_range_530_570 table_entries_range_570_610

theorem table_entries_range_450_610 : ∀ i, 450 ≤ i → i < 610 → TableEntryOk i :=
  merge_ranges table_entries_range_450_530 table_entries_range_530_610

theorem table_entries_range_300_610 : ∀ i, 300 ≤ i → i < 610 → TableEntryOk i :=
  merge_ranges table_entries_range_300_450 table_entries_range_450_610

theorem table_entries_range_0_610 : ∀ i, 0 ≤ i → i < 610 → TableEntryOk i :=
  merge_ranges table_entries_range_0_300 table_entries_range_300_610

theorem table_entries_valid : ∀ k : Fin 610,
    let e := table[k.val]?.getD emptyEntry
    e.index = k.val + 6 ∧ e.terms ≠ [] ∧ ∀ t ∈ e.terms, t.child < e.index := by
  intro k
  exact table_entries_range_0_610 k.val (Nat.zero_le _) k.isLt

theorem table_valid : TableValid := by
  refine ⟨table_size, ?_⟩
  intro k hk
  exact table_entries_valid ⟨k, by simpa only [table_size] using hk⟩

theorem placement_count : placementCount = 1837 := by
  rw [placementCount, table_toList]
  decide +kernel

theorem entryAt_index {i : ℕ} (hlo : 6 ≤ i) (hhi : i < 616) :
    (entryAt i).index = i := by
  have h := (table_entries_valid ⟨i - 6, by omega⟩).1
  simpa only [entryAt, Nat.sub_add_cancel hlo] using h

theorem entryAt_nonempty {i : ℕ} (hlo : 6 ≤ i) (hhi : i < 616) :
    (entryAt i).terms ≠ [] :=
  (table_entries_valid ⟨i - 6, by omega⟩).2.1

theorem entryAt_backward {i : ℕ} (hlo : 6 ≤ i) (hhi : i < 616)
    {t : Term} (ht : t ∈ (entryAt i).terms) : t.child < i := by
  have h := (table_entries_valid ⟨i - 6, by omega⟩).2.2 t ht
  change t.child < (entryAt i).index at h
  simpa only [entryAt_index hlo hhi] using h

end SnakyCertificate

end OAI
