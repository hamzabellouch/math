import OAI.Analysis.Quantum.PPTSquare.TensorModel

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex

namespace DimensionTen

def blocksZ : Fin 4 → Matrix (Fin 6) (Fin 4) ℤ :=
  ![ ![ ![6,0,0,0], ![0,6,0,0], ![0,0,6,0], ![0,0,0,6], ![0,0,0,0], ![0,0,0,0] ],
     ![ ![-12,0,0,0], ![0,-6,0,0], ![0,0,6,0], ![0,0,0,12], ![-6,0,6,6], ![-6,-6,6,0] ],
     ![ ![0,6,-2,0], ![6,6,0,2], ![-2,0,10,0], ![0,2,0,24], ![0,0,0,6], ![0,-6,6,-6] ],
     ![ ![0,0,-4,-3], ![0,-2,-3,-4], ![-4,-3,11,6], ![-3,-4,6,25], ![6,6,0,0], ![0,-6,6,6] ] ]

def blocks (i : Fin 4) : Matrix (Fin 6) (Fin 4) ℂ :=
  (blocksZ i).map (Int.castRingHom ℂ)

def pencil (x : Fin 4 → ℂ) : Matrix (Fin 6) (Fin 4) ℂ :=
  ∑ i : Fin 4, x i • blocks i


def pencilMap (A : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, A i j • ((blocks i)ᵀ * blocks j)

def projector (x : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.vecMulVec x (star x)


def chart (t : Fin 3 → ℂ) : Fin 4 → ℂ := Fin.cons 1 t


abbrev QuadraticIndex := { ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2 }

def quadraticEval (q : QuadraticIndex → ℂ) (x : Fin 4 → ℂ) : ℂ :=
  ∑ ij : QuadraticIndex, q ij * x ij.val.1 * x ij.val.2




def TwentyDirections : Prop :=
  ∃ t : Fin 20 → (Fin 3 → ℂ),
    Function.Injective t ∧
    (∀ k, (pencil (chart (t k))).rank < 4) ∧
    (∀ x : Fin 4 → ℂ, x ≠ 0 → (pencil x).rank < 4 →
      ∃ k : Fin 20, ∃ c : ℂ, c ≠ 0 ∧ x = c • chart (t k)) ∧
    (∀ q : QuadraticIndex → ℂ, q ≠ 0 →
      (Finset.univ.filter (fun k : Fin 20 => quadraticEval q (chart (t k)) = 0)).card ≤ 9)



abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def IsComplexLinear {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  (∀ A B, F (A + B) = F A + F B) ∧
  (∀ (c : ℂ) A, F (c • A) = c • F A)


def amplify {a b : ℕ} (F : Mat a → Mat b) (k : ℕ)
    (X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) ℂ :=
  fun u v => F (fun i j => X (u.1, i) (v.1, j)) u.2 v.2

def CompletelyPositive {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  ∀ k : ℕ, 0 < k → ∀ X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ,
    X.PosSemidef → (amplify F k X).PosSemidef


def PPT {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  IsComplexLinear F ∧ CompletelyPositive F ∧
    CompletelyPositive (fun X => (F X)ᵀ)

def separable {a b : ℕ} (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : Prop :=
  ∃ r : ℕ, ∃ A : Fin r → Mat a, ∃ B : Fin r → Mat b,
    (∀ i, (A i).PosSemidef ∧ (B i).PosSemidef) ∧
    X = ∑ i, Matrix.kronecker (A i) (B i)

def EntanglementBreaking {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  CompletelyPositive F ∧
  ∀ k : ℕ, 0 < k → ∀ X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ,
    X.PosSemidef → separable (amplify F k X)

def choi {a b : ℕ} (F : Mat a → Mat b) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  fun u v => F (Matrix.single u.1 v.1 1) u.2 v.2


def tensorMap {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    Matrix (Fin b × Fin d) (Fin b × Fin d) ℂ :=
  ∑ i : Fin c, ∑ j : Fin c,
    Matrix.kronecker (F (fun a b => X (a, i) (b, j))) (G (Matrix.single i j 1))


def hsAdjoint {a b : ℕ} (F : Mat a → Mat b) (Y : Mat b) : Mat a :=
  fun i j => ∑ u : Fin b, ∑ v : Fin b, star (F (Matrix.single i j 1) u v) * Y u v

def symmetricPairs : Fin 10 → Fin 4 × Fin 4 :=
  ![(0,0), (0,1), (0,2), (0,3), (1,1), (1,2), (1,3), (2,2), (2,3), (3,3)]

def exteriorPairs : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def symmetricIsometry : Matrix (Fin 4 × Fin 4) (Fin 10) ℂ :=
  fun ij a =>
    let p := (symmetricPairs a).1
    let q := (symmetricPairs a).2
    if p = q then (if ij = (p,p) then 1 else 0)
    else ((if ij = (p,q) then 1 else 0) + (if ij = (q,p) then 1 else 0)) /
      (Real.sqrt 2 : ℂ)

def exteriorIsometry : Matrix (Fin 4 × Fin 4) (Fin 6) ℂ :=
  fun ij a =>
    let p := (exteriorPairs a).1
    let q := (exteriorPairs a).2
    ((if ij = (p,q) then 1 else 0) - (if ij = (q,p) then 1 else 0)) /
      (Real.sqrt 2 : ℂ)

def hodgeComplement : Mat 6 :=
  ![ ![0,0,0,0,0,1], ![0,0,0,0,-1,0], ![0,0,0,1,0,0],
     ![0,0,1,0,0,0], ![0,-1,0,0,0,0], ![1,0,0,0,0,0] ]

def firstSix : Matrix (Fin 10) (Fin 6) ℂ :=
  fun i j => if i.val = j.val then 1 else 0

def exteriorMap (A : Mat 10) : Mat 6 :=
  exteriorIsometryᴴ *
    tensorMap pencilMap pencilMap (symmetricIsometry * A * symmetricIsometryᴴ) *
      exteriorIsometry

def complementaryMap (A : Mat 10) : Mat 6 :=
  hodgeComplement * (exteriorMap A)ᵀ * hodgeComplementᴴ

def phiOne (A : Mat 10) : Mat 10 :=
  firstSix * exteriorMap Aᵀ * firstSixᴴ

def phiTwo (B : Mat 10) : Mat 10 :=
  hsAdjoint complementaryMap (firstSixᴴ * B * firstSix)

def compositeChoi : Matrix (Fin 10 × Fin 10) (Fin 10 × Fin 10) ℂ :=
  choi (phiTwo ∘ phiOne)

def productVector {a b : ℕ} (u : Fin a → ℂ) (v : Fin b → ℂ) : Fin a × Fin b → ℂ :=
  fun ij => u ij.1 * v ij.2


def ExactDimensionTenPair : Prop :=
  PPT phiOne ∧ PPT phiTwo ∧ compositeChoi ≠ 0 ∧
    (∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
      compositeChoi *ᵥ w = productVector u v → u = 0 ∨ v = 0) ∧
    ¬ EntanglementBreaking (phiTwo ∘ phiOne)


theorem blocksZ_transpose_mul_comm (i j : Fin 4) :
    (blocksZ i)ᵀ * blocksZ j = (blocksZ j)ᵀ * blocksZ i := by
  decide +revert


theorem blocks_transpose_mul_comm (i j : Fin 4) :
    (blocks i)ᵀ * blocks j = (blocks j)ᵀ * blocks i := by
  have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℤ =>
    A.map (Int.castRingHom ℂ)) (blocksZ_transpose_mul_comm i j)
  simpa only [Matrix.map_mul, Matrix.transpose_map, blocks] using h

theorem blocks_conjTranspose (i : Fin 4) : (blocks i)ᴴ = (blocks i)ᵀ := by
  ext a b
  simp [blocks, Matrix.conjTranspose_apply]

theorem pencilMap_projector_gram (x : Fin 4 → ℂ) :
    pencilMap (projector x) = (pencil x)ᴴ * pencil x := by
  simp only [pencilMap, projector, Matrix.vecMulVec_apply, Pi.star_apply, pencil,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, blocks_conjTranspose,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [blocks_transpose_mul_comm j i]

theorem pencilMap_projector_rank (x : Fin 4 → ℂ) :
    (pencilMap (projector x)).rank = (pencil x).rank := by
  rw [pencilMap_projector_gram, Matrix.rank_conjTranspose_mul_self]

theorem pencilMap_projector_posSemidef (x : Fin 4 → ℂ) :
    (pencilMap (projector x)).PosSemidef := by
  rw [pencilMap_projector_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end DimensionTen

end
end

end OAI
