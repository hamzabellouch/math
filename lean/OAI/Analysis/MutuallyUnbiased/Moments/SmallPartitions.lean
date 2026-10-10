import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.NormNum
import OAI.Analysis.MutuallyUnbiased.Moments.EqualityPatterns

namespace OAI

namespace MUB6.EqualityPatterns

def blocks1 : Fin 1 → ℕ := ![1]
def raw1 : Fin 1 → Fin 1 → ℕ := ![![0]]
def label1 (p : Fin 1) (i : Fin 1) : Fin (blocks1 p) :=
  ⟨raw1 p i, by fin_cases p; fin_cases i; decide⟩

def family1 : Family (Fin 1) (Fin 1) where
  blocks := blocks1
  label := label1
  onto := by decide +kernel
  unique := by decide +kernel

theorem pattern1_0 {B : Type*} (f : Fin 1 → B)
    : ∀ i j, family1.label 0 i = family1.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i; fin_cases j; simp_all [family1, label1, raw1, blocks1]

theorem covers1 {B : Type*} (f : Fin 1 → B) :
    ∃ p, ∀ i j, (family1.label p i = family1.label p j ↔ f i = f j) := by
  classical
  refine ⟨0, ?_⟩
  apply pattern1_0 f

def blocks2 : Fin 2 → ℕ := ![1, 2]
def raw2 : Fin 2 → Fin 2 → ℕ := ![![0, 0], ![0, 1]]
def label2 (p : Fin 2) (i : Fin 2) : Fin (blocks2 p) :=
  ⟨raw2 p i, by fin_cases p <;> fin_cases i <;> decide⟩

def family2 : Family (Fin 2) (Fin 2) where
  blocks := blocks2
  label := label2
  onto := by decide +kernel
  unique := by decide +kernel

theorem pattern2_0 {B : Type*} (f : Fin 2 → B)
    (h10 : f 1 = f 0)
    : ∀ i j, family2.label 0 i = family2.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family2, label2, raw2, blocks2, eq_comm]

theorem pattern2_1 {B : Type*} (f : Fin 2 → B)
    (h10 : f 1 ≠ f 0)
    : ∀ i j, family2.label 1 i = family2.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family2, label2, raw2, blocks2, eq_comm]

theorem covers2 {B : Type*} (f : Fin 2 → B) :
    ∃ p, ∀ i j, (family2.label p i = family2.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    refine ⟨0, ?_⟩
    apply pattern2_0 f; simp_all [eq_comm]
  ·
    refine ⟨1, ?_⟩
    apply pattern2_1 f; simp_all [eq_comm]

def blocks3 : Fin 5 → ℕ := ![1, 2, 2, 2, 3]
def raw3 : Fin 5 → Fin 3 → ℕ := ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2]]
def label3 (p : Fin 5) (i : Fin 3) : Fin (blocks3 p) :=
  ⟨raw3 p i, by fin_cases p <;> fin_cases i <;> decide⟩

def family3 : Family (Fin 3) (Fin 5) where
  blocks := blocks3
  label := label3
  onto := by decide +kernel
  unique := by decide +kernel

theorem pattern3_0 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 0 i = family3.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_1 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 1 i = family3.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_2 {B : Type*} (f : Fin 3 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 2 i = family3.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_3 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 3 i = family3.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_4 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 4 i = family3.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm] <;> grind

theorem covers3 {B : Type*} (f : Fin 3 → B) :
    ∃ p, ∀ i j, (family3.label p i = family3.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨0, ?_⟩
      apply pattern3_0 f <;> simp_all [eq_comm]
    ·
      refine ⟨1, ?_⟩
      apply pattern3_1 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨2, ?_⟩
      apply pattern3_2 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        refine ⟨3, ?_⟩
        apply pattern3_3 f <;> simp_all [eq_comm]
      ·
        refine ⟨4, ?_⟩
        apply pattern3_4 f <;> simp_all [eq_comm]

def blocks4 : Fin 15 → ℕ := ![1, 2, 2, 2, 3, 2, 2, 3, 2, 2, 3, 3, 3, 3, 4]
def raw4 : Fin 15 → Fin 4 → ℕ := ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 0, 1, 2], ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 0, 2], ![0, 1, 1, 0], ![0, 1, 1, 1], ![0, 1, 1, 2], ![0, 1, 2, 0], ![0, 1, 2, 1], ![0, 1, 2, 2], ![0, 1, 2, 3]]
def label4 (p : Fin 15) (i : Fin 4) : Fin (blocks4 p) :=
  ⟨raw4 p i, by fin_cases p <;> fin_cases i <;> decide⟩

def family4 : Family (Fin 4) (Fin 15) where
  blocks := blocks4
  label := label4
  onto := by decide +kernel
  unique := by decide +kernel

theorem pattern4_0 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    (_h30 : f 3 = f 0)
    (_h31 : f 3 = f 1)
    (h32 : f 3 = f 2)
    : ∀ i j, family4.label 0 i = family4.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_1 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    (h30 : f 3 ≠ f 0)
    (_h31 : f 3 ≠ f 1)
    (_h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 1 i = family4.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_2 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    (_h30 : f 3 = f 0)
    (h31 : f 3 = f 1)
    (h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 2 i = family4.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_3 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    (_h30 : f 3 ≠ f 0)
    (_h31 : f 3 ≠ f 1)
    (h32 : f 3 = f 2)
    : ∀ i j, family4.label 3 i = family4.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_4 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    (h30 : f 3 ≠ f 0)
    (_h31 : f 3 ≠ f 1)
    (h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 4 i = family4.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_5 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (_h21 : f 2 ≠ f 1)
    (_h30 : f 3 = f 0)
    (_h31 : f 3 ≠ f 1)
    (h32 : f 3 = f 2)
    : ∀ i j, family4.label 5 i = family4.label 5 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_6 {B : Type*} (f : Fin 4 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (_h21 : f 2 ≠ f 1)
    (_h30 : f 3 ≠ f 0)
    (h31 : f 3 = f 1)
    (h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 6 i = family4.label 6 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_7 {B : Type*} (f : Fin 4 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    (h30 : f 3 ≠ f 0)
    (h31 : f 3 ≠ f 1)
    (_h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 7 i = family4.label 7 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_8 {B : Type*} (f : Fin 4 → B)
    (_h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    (h30 : f 3 = f 0)
    (h31 : f 3 ≠ f 1)
    (_h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 8 i = family4.label 8 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_9 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    (_h30 : f 3 ≠ f 0)
    (_h31 : f 3 = f 1)
    (h32 : f 3 = f 2)
    : ∀ i j, family4.label 9 i = family4.label 9 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_10 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    (h30 : f 3 ≠ f 0)
    (h31 : f 3 ≠ f 1)
    (_h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 10 i = family4.label 10 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_11 {B : Type*} (f : Fin 4 → B)
    (_h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    (h30 : f 3 = f 0)
    (h31 : f 3 ≠ f 1)
    (h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 11 i = family4.label 11 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_12 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    (_h30 : f 3 ≠ f 0)
    (h31 : f 3 = f 1)
    (h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 12 i = family4.label 12 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm]

theorem pattern4_13 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    (_h30 : f 3 ≠ f 0)
    (_h31 : f 3 ≠ f 1)
    (h32 : f 3 = f 2)
    : ∀ i j, family4.label 13 i = family4.label 13 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm] <;> grind

theorem pattern4_14 {B : Type*} (f : Fin 4 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    (h30 : f 3 ≠ f 0)
    (h31 : f 3 ≠ f 1)
    (h32 : f 3 ≠ f 2)
    : ∀ i j, family4.label 14 i = family4.label 14 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family4, label4, raw4, blocks4, eq_comm] <;> grind

theorem covers4 {B : Type*} (f : Fin 4 → B) :
    ∃ p, ∀ i j, (family4.label p i = family4.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      by_cases h30 : f 3 = f 0
      ·
        refine ⟨0, ?_⟩
        apply pattern4_0 f <;> simp_all [eq_comm]
      ·
        refine ⟨1, ?_⟩
        apply pattern4_1 f <;> simp_all [eq_comm]
    ·
      by_cases h30 : f 3 = f 0
      ·
        refine ⟨2, ?_⟩
        apply pattern4_2 f <;> simp_all [eq_comm]
      ·
        by_cases h32 : f 3 = f 2
        ·
          refine ⟨3, ?_⟩
          apply pattern4_3 f <;> simp_all [eq_comm]
        ·
          refine ⟨4, ?_⟩
          apply pattern4_4 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      by_cases h30 : f 3 = f 0
      ·
        refine ⟨5, ?_⟩
        apply pattern4_5 f <;> simp_all [eq_comm]
      ·
        by_cases h31 : f 3 = f 1
        ·
          refine ⟨6, ?_⟩
          apply pattern4_6 f <;> simp_all [eq_comm]
        ·
          refine ⟨7, ?_⟩
          apply pattern4_7 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        by_cases h30 : f 3 = f 0
        ·
          refine ⟨8, ?_⟩
          apply pattern4_8 f <;> simp_all [eq_comm]
        ·
          by_cases h31 : f 3 = f 1
          ·
            refine ⟨9, ?_⟩
            apply pattern4_9 f <;> simp_all [eq_comm]
          ·
            refine ⟨10, ?_⟩
            apply pattern4_10 f <;> simp_all [eq_comm]
      ·
        by_cases h30 : f 3 = f 0
        ·
          refine ⟨11, ?_⟩
          apply pattern4_11 f <;> simp_all [eq_comm]
        ·
          by_cases h31 : f 3 = f 1
          ·
            refine ⟨12, ?_⟩
            apply pattern4_12 f <;> simp_all [eq_comm]
          ·
            by_cases h32 : f 3 = f 2
            ·
              refine ⟨13, ?_⟩
              apply pattern4_13 f <;> simp_all [eq_comm]
            ·
              refine ⟨14, ?_⟩
              apply pattern4_14 f <;> simp_all [eq_comm]

end MUB6.EqualityPatterns

end OAI
