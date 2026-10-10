import OAI.Analysis.Nuclearity.QuotientCPMap

namespace OAI

/-! The unital extension of a completely positive contraction on a nonunital
C*-algebra. Matrix Schwarz supplies the positive square defect. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {A B : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]

def unitizedCPLinear (φ : A →L[ℂ] B) : Unitization ℂ A →L[ℂ] B where
  toFun x := φ x.snd + x.fst • (1 : B)
  map_add' x y := by simp [add_smul]; abel
  map_smul' c x := by simp [smul_add, smul_smul]
  cont := (φ.continuous.comp Unitization.continuous_snd).add
    (Unitization.continuous_fst.smul continuous_const)

@[simp] theorem unitizedCPLinear_inr (φ : A →L[ℂ] B) (a : A) :
    unitizedCPLinear φ (Unitization.inr a) = φ a := by simp [unitizedCPLinear]

@[simp] theorem unitizedCPLinear_one (φ : A →L[ℂ] B) :
    unitizedCPLinear φ 1 = 1 := by simp [unitizedCPLinear]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma unitizedCPLinear_product_defect (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ)
    (x y : Unitization ℂ A) :
    unitizedCPLinear φ (star x * y) -
        star (unitizedCPLinear φ x) * unitizedCPLinear φ y =
      φ (star x.snd * y.snd) - star (φ x.snd) * φ y.snd := by
  simp only [unitizedCPLinear, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, Unitization.snd_mul, Unitization.snd_star,
    Unitization.fst_mul, Unitization.fst_star, map_add, map_smul,
    completelyPositive_map_star hφ, star_add, star_smul, star_one,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add, smul_smul]
  rw [mul_comm y.fst (star x.fst)]
  abel

local instance unitizedCPOrder : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder _
local instance unitizedCPOrdered : StarOrderedRing (Unitization ℂ A) := CStarAlgebra.spectralOrderedRing _
local instance unitizedMatrixAOrder {n : ℕ} : PartialOrder (CStarMatrix (Fin n) (Fin n) A) :=
  CStarAlgebra.spectralOrder _
local instance unitizedMatrixAOrdered {n : ℕ} : StarOrderedRing (CStarMatrix (Fin n) (Fin n) A) :=
  CStarAlgebra.spectralOrderedRing _
local instance unitizedMatrixBOrder {n : ℕ} : PartialOrder (CStarMatrix (Fin n) (Fin n) B) :=
  CStarAlgebra.spectralOrder _
local instance unitizedMatrixBOrdered {n : ℕ} : StarOrderedRing (CStarMatrix (Fin n) (Fin n) B) :=
  CStarAlgebra.spectralOrderedRing _

lemma unitizedCPLinear_matrix_defect (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ)
    {n : ℕ} (Y : CStarMatrix (Fin n) (Fin n) (Unitization ℂ A)) :
    let Z : CStarMatrix (Fin n) (Fin n) A := CStarMatrix.ofMatrix (fun i j => (Y i j).snd)
    matrixLinearMap (unitizedCPLinear φ) (star Y * Y) -
        star (matrixLinearMap (unitizedCPLinear φ) Y) * matrixLinearMap (unitizedCPLinear φ) Y =
      matrixLinearMap φ (star Z * Z) - star (matrixLinearMap φ Z) * matrixLinearMap φ Z := by
  dsimp only
  ext i j
  simp only [CStarMatrix.sub_apply, matrixLinearMap_apply, CStarMatrix.mul_apply,
    CStarMatrix.star_apply, map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact unitizedCPLinear_product_defect φ hφ (Y k i) (Y k j)

lemma matrix_cpc_schwarz (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ)
    (hn : ‖φ‖ ≤ 1) {n : ℕ} (Z : CStarMatrix (Fin n) (Fin n) A) :
    star (matrixLinearMap φ Z) * matrixLinearMap φ Z ≤ matrixLinearMap φ (star Z * Z) := by
  have hcp : CompletelyPositive (matrixLinearMap (n := Fin n) φ) :=
    matrixLinearMap_completelyPositive φ hφ
  have hnorm : ‖matrixLinearMap (n := Fin n) φ‖ ≤ 1 :=
    matrixLinearMap_norm_le_one φ hφ hn
  exact completelyPositive_schwarz_nonunital_domain hcp hnorm Z

/-- A cpc map has the canonical unital completely positive extension. -/
theorem unitizedCPLinear_cp (φ : A →L[ℂ] B) (hφ : CompletelyPositive φ) (hn : ‖φ‖ ≤ 1) :
    CompletelyPositive (unitizedCPLinear φ) := by
  intro n M hM
  let : Module ℝ (CStarMatrix (Fin n) (Fin n) (Unitization ℂ A)) :=
    Module.compHom _ Complex.ofRealHom
  let Y := CFC.sqrt M
  have hY : star Y * Y = M := by
    rw [(CFC.sqrt_nonneg M).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self M hM]
  let Z : CStarMatrix (Fin n) (Fin n) A := CStarMatrix.ofMatrix (fun i j => (Y i j).snd)
  have hs := matrix_cpc_schwarz φ hφ hn Z
  have hd := unitizedCPLinear_matrix_defect φ hφ Y
  change 0 ≤ matrixLinearMap (unitizedCPLinear φ) M
  rw [← hY]
  have hp : 0 ≤ matrixLinearMap (unitizedCPLinear φ) (star Y * Y) -
      star (matrixLinearMap (unitizedCPLinear φ) Y) * matrixLinearMap (unitizedCPLinear φ) Y := by
    rw [hd]
    exact sub_nonneg.mpr hs
  exact (star_mul_self_nonneg _).trans (sub_nonneg.mp hp)

end WeakPureInfiniteness

end

end OAI
