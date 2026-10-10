import OAI.NumberTheory.DukePrimeDegree.Geometry.HorosphereDiagonal

namespace OAI

/-!
# Row and column coordinates for the shearing horosphere

Every element factors uniquely into a column displacement and a row
displacement, with the shared root entry assigned to the row factor.
The determinant lemma constructs both factors in the special linear
group without extending the ambient group.
-/

noncomputable section
open Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rootRowElement {n : ℕ} (i : Fin n) (a : Fin n → ℝ) (ha : a i = 0) : G n :=
  ⟨1 + Matrix.vecMulVec (Pi.single i 1) a, by
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [ha]⟩

def rootColumnElement {n : ℕ} (j : Fin n) (b : Fin n → ℝ) (hb : b j = 0) : G n :=
  ⟨1 + Matrix.vecMulVec b (Pi.single j 1), by
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [hb]⟩

lemma rootRowElement_entry {n : ℕ} (i : Fin n) (a : Fin n → ℝ) (ha : a i = 0)
    (r s : Fin n) :
    (rootRowElement i a ha).val r s = (1 : Matrix (Fin n) (Fin n) ℝ) r s +
      if r = i then a s else 0 := by
  simp [rootRowElement, Matrix.vecMulVec_apply, Pi.single_apply]

lemma rootColumnElement_entry {n : ℕ} (j : Fin n) (b : Fin n → ℝ) (hb : b j = 0)
    (r s : Fin n) :
    (rootColumnElement j b hb).val r s = (1 : Matrix (Fin n) (Fin n) ℝ) r s +
      if s = j then b r else 0 := by
  simp [rootColumnElement, Matrix.vecMulVec_apply, Pi.single_apply]

theorem rootRowElement_shape {n : ℕ} (i j : Fin n) (a : Fin n → ℝ) (ha : a i = 0) :
    RootHorosphereShape i j (rootRowElement i a ha) := by
  intro r s hrs
  rw [rootRowElement_entry]
  rcases hrs with hrs | rfl
  · simp only [hrs.1, ite_false, add_zero]
  · by_cases hr : r = i
    · subst r; simp [ha]
    · simp [hr]

theorem rootColumnElement_shape {n : ℕ} (i j : Fin n) (b : Fin n → ℝ) (hb : b j = 0) :
    RootHorosphereShape i j (rootColumnElement j b hb) := by
  intro r s hrs
  rw [rootColumnElement_entry]
  rcases hrs with hrs | rfl
  · simp only [hrs.2, ite_false, add_zero]
  · by_cases hr : r = j
    · subst r; simp [hb]
    · simp [hr]

def horosphereRowCoordinates {n : ℕ} (i : Fin n) (g : G n) : Fin n → ℝ :=
  fun s => g.val i s - (1 : Matrix (Fin n) (Fin n) ℝ) i s

def horosphereColumnCoordinates {n : ℕ} (i j : Fin n) (g : G n) : Fin n → ℝ :=
  fun r => if r = i then 0 else g.val r j - (1 : Matrix (Fin n) (Fin n) ℝ) r j

lemma horosphereRowCoordinates_self {n : ℕ} {i j : Fin n}
    (g : G n) (hg : RootHorosphereShape i j g) : horosphereRowCoordinates i g i = 0 := by
  exact sub_eq_zero.mpr (hg i i (Or.inr rfl))

lemma horosphereColumnCoordinates_self {n : ℕ} {i j : Fin n}
    (g : G n) (hg : RootHorosphereShape i j g) : horosphereColumnCoordinates i j g j = 0 := by
  by_cases hji : j = i
  · simp [horosphereColumnCoordinates, hji]
  · simp only [horosphereColumnCoordinates, hji, ite_false]
    exact sub_eq_zero.mpr (hg j j (Or.inr rfl))

theorem rootHorosphere_column_row_factorization {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hg : RootHorosphereShape i j g) :
    g = rootColumnElement j (horosphereColumnCoordinates i j g)
        (horosphereColumnCoordinates_self g hg) *
      rootRowElement i (horosphereRowCoordinates i g) (horosphereRowCoordinates_self g hg) := by
  let a := horosphereRowCoordinates i g
  let b := horosphereColumnCoordinates i j g
  have hcross : Matrix.vecMulVec b (Pi.single j 1) * Matrix.vecMulVec (Pi.single i 1) a = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    simp [hij]
  apply Subtype.ext
  change g.val = (1 + Matrix.vecMulVec b (Pi.single j 1)) *
    (1 + Matrix.vecMulVec (Pi.single i 1) a)
  simp only [mul_add, add_mul, Matrix.one_mul, Matrix.mul_one, hcross, add_zero]
  ext r s
  change g.val r s = (1 : Matrix (Fin n) (Fin n) ℝ) r s +
    (Matrix.vecMulVec b (Pi.single j 1)) r s + (Matrix.vecMulVec (Pi.single i 1) a) r s
  by_cases hri : r = i
  · subst r
    simp [a, b, horosphereRowCoordinates, horosphereColumnCoordinates, Matrix.vecMulVec_apply]
  · by_cases hsj : s = j
    · subst s
      simp [a, b, horosphereRowCoordinates, horosphereColumnCoordinates,
        Matrix.vecMulVec_apply, hri]
    · have he := hg r s (Or.inl ⟨hri, hsj⟩)
      simp [Matrix.vecMulVec_apply, hri, hsj, he]

theorem rootColumn_mul_rootRow_entry {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a b : Fin n → ℝ) (ha : a i = 0) (hb : b j = 0) (r s : Fin n) :
    (rootColumnElement j b hb * rootRowElement i a ha).val r s =
      (1 : Matrix (Fin n) (Fin n) ℝ) r s + (if s = j then b r else 0) +
        (if r = i then a s else 0) := by
  have hcross : Matrix.vecMulVec b (Pi.single j 1) * Matrix.vecMulVec (Pi.single i 1) a = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    simp [hij]
  change ((1 + Matrix.vecMulVec b (Pi.single j 1)) *
    (1 + Matrix.vecMulVec (Pi.single i 1) a)) r s = _
  simp only [mul_add, add_mul, Matrix.one_mul, Matrix.mul_one, hcross, add_zero,
    Matrix.add_apply, Matrix.vecMulVec_apply]
  by_cases hr : r = i <;> by_cases hs : s = j <;> simp [hr, hs]

end DukePrimeDegree

end

end OAI
