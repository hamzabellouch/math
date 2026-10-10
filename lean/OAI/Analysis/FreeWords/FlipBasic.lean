import Mathlib

namespace OAI

noncomputable section

namespace KKFreeLiftDiagnostic

open scoped BigOperators Matrix.Norms.L2Operator Kronecker

noncomputable section

abbrev Block (d : ℕ) := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ

def flip (d : ℕ) : Block d := fun i j => if i = j.swap then 1 else 0

def left {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Block d := U ⊗ₖ 1

def partialTrace {d : ℕ} (A : Block d) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => (d : ℂ)⁻¹ * ∑ k, A (k,i) (k,j)

def normalizedTrace {d : ℕ} (A : Block d) : ℂ :=
  ((d : ℂ)^2)⁻¹ * Matrix.trace A

def centeredFlip (d : ℕ) : Block d := flip d - (d : ℂ)⁻¹ • 1

def mixedWord {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (X : Block d) : Block d :=
  left U * X * left U * X * star (left U) * X * star (left U) * X

def right {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Block d := 1 ⊗ₖ U

@[simp] theorem mul_flip {d : ℕ} (A : Block d) (i j : Fin d × Fin d) :
    (A * flip d) i j = A i j.swap := by
  classical
  simp [Matrix.mul_apply, flip]

@[simp] theorem flip_mul {d : ℕ} (A : Block d) (i j : Fin d × Fin d) :
    (flip d * A) i j = A i.swap j := by
  classical
  have he (k : Fin d × Fin d) : i = k.swap ↔ k = i.swap := by
    constructor <;> intro h
    · simpa using (congrArg Prod.swap h).symm
    · simpa using (congrArg Prod.swap h).symm
  simp [Matrix.mul_apply, flip,he]

@[simp] theorem flip_mul_flip (d : ℕ) : flip d * flip d = 1 := by
  ext i j
  simp [flip, Matrix.one_apply]

@[simp] theorem flip_star (d : ℕ) : star (flip d) = flip d := by
  ext i j
  have he : j = i.swap ↔ i = j.swap := by
    constructor <;> intro h <;> simpa using (congrArg Prod.swap h).symm
  simp [flip, Matrix.star_apply,he]

theorem flip_unitary (d : ℕ) : flip d ∈ unitary (Block d) := by
  exact ⟨by simp,by simp⟩

@[simp] theorem flip_left_flip {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    flip d * left U * flip d = right U := by
  ext i j
  simp [left,right,Prod.swap,mul_comm]

@[simp] theorem left_star {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    star (left U)=left (star U) := by
  ext i j
  by_cases hij : i.2=j.2 <;> simp [left, Matrix.star_apply,Matrix.one_apply,eq_comm,hij]

theorem left_unitary {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    left (U : Matrix (Fin d) (Fin d) ℂ) ∈ unitary (Block d) := by
  have h1 : star (U.val)*U.val=1 := U.property.1
  have h2 : U.val*star (U.val)=1 := U.property.2
  constructor
  · rw [left_star]
    dsimp [left]
    rw [← Matrix.mul_kronecker_mul,h1,one_mul,Matrix.one_kronecker_one]
  · rw [left_star]
    dsimp [left]
    rw [← Matrix.mul_kronecker_mul,h2,one_mul,Matrix.one_kronecker_one]

theorem mixedWord_flip {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    mixedWord (U : Matrix (Fin d) (Fin d) ℂ) (flip d)=1 := by
  have hU : U.val*star (U.val)=1 := U.property.2
  calc
    _ = (left U.val*(flip d*left U.val*flip d))*
        (star (left U.val)*(flip d*star (left U.val)*flip d)) := by
      dsimp [mixedWord]
      noncomm_ring
    _ = (left U.val*right U.val)*(left (star U.val)*right (star U.val)) := by
      rw [left_star,flip_left_flip,flip_left_flip]
    _ = (U.val*star (U.val)) ⊗ₖ (U.val*star (U.val)) := by
      dsimp [left,right]
      rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
      simp only [mul_one,one_mul]
      exact (Matrix.mul_kronecker_mul _ _ _ _).symm
    _ = 1 := by rw [hU,Matrix.one_kronecker_one]

@[simp] theorem partialTrace_sub {d : ℕ} (A B : Block d) :
    partialTrace (A-B)=partialTrace A-partialTrace B := by
  ext i j
  simp [partialTrace,Finset.sum_sub_distrib,mul_sub]

@[simp] theorem partialTrace_smul {d : ℕ} (c : ℂ) (A : Block d) :
    partialTrace (c • A)=c • partialTrace A := by
  ext i j
  simp [partialTrace,Finset.mul_sum,mul_left_comm]

@[simp] theorem partialTrace_one {d : ℕ} (hd : 0 < d) :
    partialTrace (1 : Block d)=1 := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  ext i j
  by_cases hij : i=j
  · subst j
    simp [partialTrace,hd0]
  · simp [partialTrace,hij]

@[simp] theorem partialTrace_flip (d : ℕ) :
    partialTrace (flip d)=(d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [partialTrace,flip,Prod.mk.injEq,eq_comm]
  · have hh (k : Fin d) : ¬(k=j ∧ i=k) := by aesop
    simp [partialTrace,flip,Prod.mk.injEq,hh,hij]

@[simp] theorem partialTrace_centeredFlip {d : ℕ} (hd : 0 < d) :
    partialTrace (centeredFlip d)=0 := by
  simp [centeredFlip,partialTrace_one hd]

@[simp] theorem trace_flip (d : ℕ) : Matrix.trace (flip d)=(d : ℂ) := by
  change (∑ i : Fin d × Fin d, if i=i.swap then (1 : ℂ) else 0) = _
  rw [Fintype.sum_prod_type]
  simp [Prod.mk.injEq,eq_comm]

@[simp] theorem normalizedTrace_one {d : ℕ} (hd : 0 < d) :
    normalizedTrace (1 : Block d)=1 := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [normalizedTrace,Matrix.trace_one,Fintype.card_prod,Fintype.card_fin, Nat.cast_mul]
  field_simp

@[simp] theorem normalizedTrace_centeredFlip {d : ℕ} (hd : 0 < d) :
    normalizedTrace (centeredFlip d)=0 := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  simp [normalizedTrace,centeredFlip,Matrix.trace_sub,Matrix.trace_smul,
    Matrix.trace_one,Fintype.card_prod,smul_eq_mul,pow_two,hd0]

end

end KKFreeLiftDiagnostic
end

end OAI
