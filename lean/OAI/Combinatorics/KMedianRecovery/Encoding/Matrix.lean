import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FacePoint
import OAI.Combinatorics.KMedianRecovery.Recovery.CommonDen

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid.Stored
open Matrix RationalLinearFeasibility
open scoped BigOperators

def matrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℚ :=
  let ar := Vector.ofFn (fun i => Vector.ofFn (A i))
  fun i j => ar[i][j]
def vector {n : ℕ} (v : Fin n → ℚ) : Fin n → ℚ :=
  let ar := Vector.ofFn v
  fun i => ar[i]
@[simp] lemma matrix_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : matrix A=A := by
  funext i j
  simp [matrix]
@[simp] lemma vector_eq {n : ℕ} (v : Fin n → ℚ) : vector v=v := by
  funext i
  simp [vector]

def state {n : ℕ} (S : State n) : State n := ⟨matrix S.shape,vector S.center⟩
@[simp] lemma state_eq {n : ℕ} (S : State n) : state S=S := by
  cases S
  simp only [state,matrix_eq,vector_eq]

def iterate {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n) : ℕ → State n
  | 0 => state S
  | t+1 => state (advance D rows (iterate D rows S t))

@[simp] lemma iterate_eq {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n) (t : ℕ) :
    iterate D rows S t=Ellipsoid.iterate D rows S t := by
  induction t with
  | zero => simp only [iterate,Ellipsoid.iterate,state_eq]
  | succ t ih => simp only [iterate,Ellipsoid.iterate,state_eq,ih]

def weakSolve {n : ℕ} (rows : List (Row n)) (R : ℚ) (p s : ℕ) : Option (Fin n → ℚ) :=
  let T := iterationBudget n p s
  let c := (iterate (gridDenominator n T) rows (initialState n R) T).center
  if badRow rows c=none then some c else none
@[simp] lemma weakSolve_eq {n : ℕ} (rows : List (Row n)) (R : ℚ) (p s : ℕ) :
    weakSolve rows R p s=Ellipsoid.weakSolve rows R p s := by
  simp only [weakSolve,Ellipsoid.weakSolve,iterate_eq]

def integerDecide {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) : Bool :=
  (weakSolve (relaxedRows (gapEpsilon m n H) (boundedRows A b B))
    ((n:ℚ)*(B+1)) (precisionLog m n H) (radiusLog n B)).isSome
@[simp] lemma integerDecide_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    integerDecide A b B H=Ellipsoid.integerDecide A b B H := by
  simp only [integerDecide,Ellipsoid.integerDecide,weakSolve_eq]

def boundedIntegerDecide {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : Bool :=
  integerDecide (padMatrix A) b B (dataHeight (padMatrix A) b B)
@[simp] lemma boundedIntegerDecide_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    boundedIntegerDecide A b B=Ellipsoid.boundedIntegerDecide A b B := by
  simp only [boundedIntegerDecide,Ellipsoid.boundedIntegerDecide,integerDecide_eq]

def boundedRationalDecide {n : ℕ} (rows : List (Row n)) (B : ℕ) : Bool :=
  boundedIntegerDecide (clearedMatrix rows) (clearedBounds rows) B
@[simp] lemma boundedRationalDecide_eq {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    boundedRationalDecide rows B=Ellipsoid.boundedRationalDecide rows B := by
  simp only [boundedRationalDecide,Ellipsoid.boundedRationalDecide,boundedIntegerDecide_eq]

def selectFace {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    List (Row n) → List (Row n) → List (Row n)
  | [],picked => picked
  | q::todo,picked =>
    if boundedRationalDecide (faceRows rows (q::picked)) B then
      selectFace rows B todo (q::picked)
    else selectFace rows B todo picked
@[simp] lemma selectFace_eq {n : ℕ} (rows : List (Row n)) (B : ℕ) (todo picked : List (Row n)) :
    selectFace rows B todo picked=Ellipsoid.selectFace rows B todo picked := by
  induction todo generalizing picked with
  | nil => rfl
  | cons q todo ih => simp only [selectFace,Ellipsoid.selectFace,boundedRationalDecide_eq,ih]

def finalFace {n : ℕ} (rows : List (Row n)) (B : ℕ) : List (Row n) :=
  selectFace (withBox rows B) B (withBox rows B) []
@[simp] lemma finalFace_eq {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    finalFace rows B=Ellipsoid.finalFace rows B := selectFace_eq _ _ _ _

def point {n : ℕ} (picked : List (Row n)) : Fin n → ℚ :=
  let C := matrix (rowMatrix picked)
  let G := matrix (Cᵀ*C)
  let d := vector (Cᵀ *ᵥ rowBounds picked)
  BirdRational.solve G d

lemma linearSolve_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (hA : A.PosDef) : BirdRational.solve A b=PositiveSolve.solve n A b := by
  apply mulVec_injective_of_isUnit hA.isUnit
  rw [BirdRational.solve_correct A b ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit).ne_zero,PositiveSolve.solve_correct n A b hA]

lemma point_eq {n : ℕ} (picked : List (Row n))
    (hC : Function.Injective (rowMatrix picked).mulVec) :
    point picked=PositiveSolve.solve n
      (PositiveSolve.freezeMat ((rowMatrix picked)ᵀ*rowMatrix picked))
      (PositiveSolve.freezeVec ((rowMatrix picked)ᵀ *ᵥ rowBounds picked)) := by
  have hG : ((rowMatrix picked)ᵀ*rowMatrix picked).PosDef := by
    simpa using PosDef.conjTranspose_mul_self (rowMatrix picked) hC
  simp only [point,matrix_eq,vector_eq,PositiveSolve.freezeMat_eq,PositiveSolve.freezeVec_eq]
  exact linearSolve_eq _ _ hG

def facePoint {n : ℕ} (rows : List (Row n)) (B : ℕ) : Fin n → ℚ :=
  point (finalFace rows B)

lemma facePoint_eq {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    facePoint rows B=Ellipsoid.facePoint rows B := by
  unfold facePoint Ellipsoid.facePoint
  rw [finalFace_eq]
  exact point_eq _ (finalFace_rat_injective rows B hfeas)

def exactSolve {n : ℕ} (rows : List (Row n)) (B : ℕ) : Option (Fin n → ℚ) :=
  if boundedRationalDecide rows B then some (facePoint rows B) else none
@[simp] theorem exactSolve_eq {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    exactSolve rows B=Ellipsoid.exactSolve rows B := by
  unfold exactSolve Ellipsoid.exactSolve
  rw [boundedRationalDecide_eq]
  split_ifs with h
  · rw [facePoint_eq rows B ((boundedRationalDecide_correct rows B).mp h)]
  · rfl

theorem exactSolve_some {n : ℕ} (rows : List (Row n)) (B : ℕ) (x : Fin n → ℚ)
    (hx : exactSolve rows B=some x) :
    (∀ q∈rows,q.Holds x) ∧ (∀ j,|x j|≤(B:ℚ)) :=
  Ellipsoid.exactSolve_some rows B x (by simpa only [exactSolve_eq] using hx)

theorem exactSolve_complete {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    ∃ x, exactSolve rows B=some x := by
  simpa only [exactSolve_eq] using Ellipsoid.exactSolve_complete rows B hfeas

end MetricKMedianRecovery.Ellipsoid.Stored

end OAI
