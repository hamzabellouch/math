import Mathlib
import OAI.Analysis.LaughlinFock.SpinSchur

namespace OAI

/-! Fock Rotations. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
def sectorOneBodyLinear (Q k : ℕ) :
    Matrix (Orbital Q) (Orbital Q) ℂ →ₗ[ℂ]
      Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ where
  toFun := sectorOneBody Q k
  map_add' A B := by ext S T; exact congrFun (congrFun (oneBodyLift_add Q A B) S.val) T.val
  map_smul' c A := by ext S T; exact congrFun (congrFun (oneBodyLift_smul Q c A) S.val) T.val

 

inductive FockRotationIndex
  | spin (n : ℕ)
  | sector (k : ℕ)
  | fock
  deriving DecidableEq

 

abbrev FockRotationSpace (Q : ℕ) : FockRotationIndex → Type
  | .spin n => Fin (n+1)
  | .sector k => SectorOccupation Q k
  | .fock => Occupation Q

instance (Q : ℕ) (j : FockRotationIndex) : Fintype (FockRotationSpace Q j) := by
  cases j <;> unfold FockRotationSpace <;> infer_instance
instance (Q : ℕ) (j : FockRotationIndex) : DecidableEq (FockRotationSpace Q j) := by
  cases j <;> unfold FockRotationSpace <;> infer_instance

 
def fockRotationGenerator (Q : ℕ) (s : Fin 3) :
    ∀ j, Matrix (FockRotationSpace Q j) (FockRotationSpace Q j) ℂ
  | .spin n => spinGenerator n s
  | .sector k => sectorOneBody Q k (spinGenerator Q s)
  | .fock => oneBodyLift Q (spinGenerator Q s)

theorem fockRotationGenerator_skew (Q : ℕ) (s : Fin 3) (j : FockRotationIndex) :
    (fockRotationGenerator Q s j)ᴴ = -fockRotationGenerator Q s j := by
  cases j with
  | spin n => exact spinGenerator_skew n s
  | sector k =>
    change (sectorOneBody Q k _)ᴴ = _
    rw [sectorOneBody_adjoint, spinGenerator_skew]
    exact (sectorOneBodyLinear Q k).map_neg _
  | fock =>
    change (oneBodyLift Q _)ᴴ = _
    rw [oneBodyLift_adjoint, spinGenerator_skew]
    exact (oneBodyLiftLinear Q).map_neg _

 
def fockAverage (Q : ℕ) : FockMatrix Q →ₗ[ℂ] FockMatrix Q :=
  rotationAverageLinear (fockRotationGenerator Q) (fockRotationGenerator_skew Q) .fock

 
def sectorAverage (Q k : ℕ) :
    Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ →ₗ[ℂ]
      Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ :=
  rotationAverageLinear (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.sector k)

 
theorem fockAverage_exteriorLift (Q k : ℕ)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    fockAverage Q (exteriorLift Q k M) = exteriorLift Q k (sectorAverage Q k M) := by
  exact (rotationAverage_covariance (fockRotationGenerator Q) (fockRotationGenerator_skew Q)
    (i:=.sector k) (j:=.fock) (exteriorLiftLinear Q k)
    (fun s M => (oneBody_exteriorLift_commutator Q k (spinGenerator Q s) M).symm) M).symm

theorem fockAverage_posSemidef (Q : ℕ) (M : FockMatrix Q) (hM : M.PosSemidef) :
    (fockAverage Q M).PosSemidef :=
  rotationAverage_posSemidef (fockRotationGenerator Q) (fockRotationGenerator_skew Q) .fock M hM

theorem sectorAverage_posSemidef (Q k : ℕ)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) (hM : M.PosSemidef) :
    (sectorAverage Q k M).PosSemidef :=
  rotationAverage_posSemidef (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.sector k) M hM

 

theorem spinRotationAverage (Q n : ℕ) (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    rotationAverage (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.spin n) M =
      (M.trace / (n+1 : ℂ)) • 1 := by
  have he := spin_intertwiner_trace_scalar
    (rotationAverage (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.spin n) M)
    (fun s => (rotationAverage_commutes_generator (fockRotationGenerator Q)
      (fockRotationGenerator_skew Q) (.spin n) M s).symm)
  rw [rotationAverage_trace] at he
  exact he

 
def congruenceLinear {ι κ : Type*} [Fintype ι] (C : Matrix κ ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun M := C * M * Cᴴ
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

 

theorem congruenceLinear_commutator {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (C : Matrix κ ι ℂ)
    (hX : Xᴴ = -X) (hY : Yᴴ = -Y) (hC : Y*C = C*X)
    (M : Matrix ι ι ℂ) :
    congruenceLinear C (X*M-M*X) = Y * congruenceLinear C M - congruenceLinear C M * Y := by
  have hC' : Cᴴ * Y = X * Cᴴ := by
    have hh := congrArg Matrix.conjTranspose hC
    simpa only [Matrix.conjTranspose_mul, hX, hY, Matrix.mul_neg, Matrix.neg_mul,
      neg_inj] using hh
  change C * (X*M-M*X) * Cᴴ = Y*(C*M*Cᴴ) - (C*M*Cᴴ)*Y
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Y C, hC, Matrix.mul_assoc, hC']

 

theorem sectorAverage_spin_sandwich {Q k n : ℕ}
    (C : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s) * C = C * spinGenerator n s)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    sectorAverage Q k (C*M*Cᴴ) = (M.trace / (n+1 : ℂ)) • (C*Cᴴ) := by
  have hc := rotationAverage_covariance (fockRotationGenerator Q)
    (fockRotationGenerator_skew Q) (i:=.spin n) (j:=.sector k)
    (congruenceLinear C) (fun s M => congruenceLinear_commutator _ _ C
      (spinGenerator_skew n s) (fockRotationGenerator_skew Q s (.sector k)) (hC s) M) M
  change C * rotationAverage (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.spin n) M * Cᴴ =
    rotationAverage (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.sector k) (C*M*Cᴴ) at hc
  change rotationAverage (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.sector k) (C*M*Cᴴ) = _
  rw [← hc, spinRotationAverage]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

 

theorem fockAverage_spin_sandwich {Q k n : ℕ}
    (C : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s) * C = C * spinGenerator n s)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    fockAverage Q (exteriorLift Q k (C*M*Cᴴ)) =
      (M.trace / (n+1 : ℂ)) • exteriorLift Q k (C*Cᴴ) := by
  rw [fockAverage_exteriorLift, sectorAverage_spin_sandwich C hC]
  exact (exteriorLiftLinear Q k).map_smul _ _

end LaughlinFock
end

end OAI
