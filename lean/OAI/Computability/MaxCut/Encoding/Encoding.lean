import Mathlib
import OAI.Computability.MaxCut.Games.Target
import OAI.Computability.MaxCut.Encoding.BinaryCoordinates

namespace OAI

/-! Computable binary alphabet indexing and full translation permutation tables.
The labels are actual `Fin (2^s)` entries in the target instance format.
-/

namespace MaxCutGames.Reduction.Encoding

open Integration.BinaryLinear
open Foundations.Target

/-- Number the left side first and the right side second. -/
def sideEquiv (n : Nat) : Bool × Fin n ≃ Fin (2*n) :=
  (finTwoEquiv.symm.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv

@[simp] theorem sideEquiv_false_val {vertexCount : Nat} (i : Fin vertexCount) :
    (sideEquiv vertexCount (false, i)).val = i.val := by
  simp [sideEquiv, finProdFinEquiv, finTwoEquiv]

@[simp] theorem sideEquiv_true_val {vertexCount : Nat} (i : Fin vertexCount) :
    (sideEquiv vertexCount (true, i)).val = vertexCount + i.val := by
  simp [sideEquiv, finProdFinEquiv, finTwoEquiv, Nat.add_comm]

/-- The integer label is the packed, least-significant-bit-first coordinate word. -/
def alphabetEquiv (s : Nat) : Integration.BinaryLinear.Vector s ≃ Fin (2^s) :=
  (coordinatesEquiv s).symm.trans
    { toFun := BitVec.toFin
      invFun := BitVec.ofFin
      left_inv := BitVec.ofFin_toFin
      right_inv := BitVec.toFin_ofFin }

@[simp] theorem alphabetEquiv_symm_apply_apply (s : Nat)
    (c : Integration.BinaryLinear.Vector s) :
    (alphabetEquiv s).symm (alphabetEquiv s c) = c :=
  (alphabetEquiv s).symm_apply_apply c

@[simp] theorem alphabetEquiv_apply_symm_apply (s : Nat) (c : Fin (2^s)) :
    alphabetEquiv s ((alphabetEquiv s).symm c) = c :=
  (alphabetEquiv s).apply_symm_apply c

def translate {s : Nat} (a b : Integration.BinaryLinear.Vector s)
    (c : Fin (2^s)) : Fin (2^s) :=
  alphabetEquiv s ((alphabetEquiv s).symm c + a + b)

theorem translate_involutive {s : Nat} (a b : Integration.BinaryLinear.Vector s) :
    Function.Involutive (translate a b) := by
  intro c
  simp only [translate, alphabetEquiv_symm_apply_apply]
  have h : (alphabetEquiv s).symm c + a + b + a + b = (alphabetEquiv s).symm c := by
    ext i
    simp only [Pi.add_apply]
    rw [show (alphabetEquiv s).symm c i + a i + b i + a i + b i =
      (alphabetEquiv s).symm c i + (a i + a i) + (b i + b i) by abel]
    simp [CharTwo.add_self_eq_zero]
  rw [h, alphabetEquiv_apply_symm_apply]

/-- Both forward and inverse tables are explicitly generated from every alphabet
index. Characteristic two makes these two tables equal. -/
def translationTable {s : Nat} (a b : Integration.BinaryLinear.Vector s) :
    PermutationTable (2^s) where
  images := _root_.Vector.ofFn (translate a b)
  inverseImages := _root_.Vector.ofFn (translate a b)
  leftInverse c := by simpa using translate_involutive a b c
  rightInverse c := by simpa using translate_involutive a b c

@[simp] theorem translationTable_images {s : Nat}
    (a b c : Integration.BinaryLinear.Vector s) :
    (translationTable a b).images[alphabetEquiv s c] = alphabetEquiv s (c + a + b) := by
  simp [translationTable, translate]

@[simp] theorem translationTable_inverseImages {s : Nat}
    (a b c : Integration.BinaryLinear.Vector s) :
    (translationTable a b).inverseImages[alphabetEquiv s c] =
      alphabetEquiv s (c + a + b) := by
  simp [translationTable, translate]

theorem translationTable_satisfied_iff {s : Nat}
    (a b cLeft cRight : Integration.BinaryLinear.Vector s) :
    (translationTable a b).images[alphabetEquiv s cLeft] = alphabetEquiv s cRight ↔
      cLeft + a + b = cRight := by
  rw [translationTable_images]
  exact (alphabetEquiv s).injective.eq_iff

variable {Q V : Type*} [DecidableEq V]

/-- Canonical vertex bodies are compared using their actual decidable equality.
`List.dedup` fixes a deterministic order by retaining the last occurrence. -/
def imageVertices (queries : List Q) (body : Q → V) : List V :=
  (queries.map body).dedup

theorem mem_imageVertices {queries : List Q} {body : Q → V} {v : V} :
    v ∈ imageVertices queries body ↔ ∃ q ∈ queries, body q = v := by
  simp [imageVertices]

theorem imageVertices_nodup (queries : List Q) (body : Q → V) :
    (imageVertices queries body).Nodup := List.nodup_dedup _

theorem imageVertices_length_le (queries : List Q) (body : Q → V) :
    (imageVertices queries body).length ≤ queries.length := by
  simpa only [imageVertices, List.length_map] using
    (List.dedup_sublist (queries.map body)).length_le

abbrev ImageVertex (queries : List Q) (body : Q → V) :=
  {v : V // v ∈ imageVertices queries body}

/-- A computable numbering using `idxOf`; its inverse looks up that index.
It involves no chosen `Fintype.equivFin`. -/
def imageEquiv (queries : List Q) (body : Q → V) :
    ImageVertex queries body ≃ Fin (imageVertices queries body).length :=
  (List.Nodup.getEquiv _ (imageVertices_nodup queries body)).symm

def imageVertex (queries : List Q) (body : Q → V) (q : Q) (hq : q ∈ queries) :
    ImageVertex queries body := ⟨body q, mem_imageVertices.mpr ⟨q, hq, rfl⟩⟩

def imageIndex (queries : List Q) (body : Q → V) (q : Q) (hq : q ∈ queries) :
    Fin (imageVertices queries body).length := imageEquiv queries body (imageVertex queries body q hq)

theorem imageIndex_eq_iff (queries : List Q) (body : Q → V)
    (q r : Q) (hq : q ∈ queries) (hr : r ∈ queries) :
    imageIndex queries body q hq = imageIndex queries body r hr ↔ body q = body r := by
  simp only [imageIndex, (imageEquiv queries body).injective.eq_iff, Subtype.mk.injEq,
    imageVertex]

theorem imageVertices_range (queries : List Q) (body : Q → V)
    (full : ∀ q, q ∈ queries) (v : V) :
    v ∈ imageVertices queries body ↔ v ∈ Set.range body := by
  simp [mem_imageVertices, full, Set.mem_range]

end MaxCutGames.Reduction.Encoding

end OAI
