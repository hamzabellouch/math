import OAI.Analysis.Mahler.SpecialMassHypotheses
import Mathlib.Analysis.Matrix.PosDef

namespace OAI

namespace SymmetricMahler
open Real Complex Matrix Set Finset
open scoped Topology
open MahlerConformal
variable {n N : ℕ}

noncomputable def specialRowFactor (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Fin n → ℂ) (j : Fin N) : ℂ :=
  (m : ℂ)*inverseF (complexRow A j z)^(m-1)*deriv inverseF (complexRow A j z)

noncomputable def specialDerivative (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Fin n → ℂ) : (Fin n → ℂ) →L[ℂ] (Fin N → ℂ) :=
  ContinuousLinearMap.pi fun j => specialRowFactor A m z j • complexRow A j

/-- The actual holomorphic derivative, with its full m and h' factors. -/
theorem hasFDerivAt_specialMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    {z : Fin n → ℂ} (hz : z ∈ complexStripDomain A) :
    HasFDerivAt (specialMap A m) (specialDerivative A m z) z := by
  apply hasFDerivAt_pi.mpr
  intro j
  have hh : HasDerivAt inverseF (deriv inverseF (complexRow A j z)) (complexRow A j z) :=
    (hasDerivAt_inverseF (hz j)).differentiableAt.hasDerivAt
  have h := (hh.pow m).hasFDerivAt.comp z (complexRow A j).hasFDerivAt
  have hc : (ContinuousLinearMap.toSpanSingleton ℂ (specialRowFactor A m z j)).comp (complexRow A j) =
      specialRowFactor A m z j • complexRow A j := by
    ext v
    simp [smul_eq_mul,mul_comm]
  change HasFDerivAt (fun x => inverseF (complexRow A j x)^m)
    (specialRowFactor A m z j • complexRow A j) z
  rw [← hc]
  simpa only [Function.comp_def,Pi.pow_apply,specialRowFactor] using h

noncomputable def specialJacobianMatrix (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Fin n → ℂ) : Matrix (Fin N) (Fin n) ℂ := fun j k => specialRowFactor A m z j*(A j k : ℂ)

lemma specialJacobianMatrix_derivative (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Fin n → ℂ) (j : Fin N) (k : Fin n) :
    specialDerivative A m z (Pi.single k 1) j = specialJacobianMatrix A m z j k := by
  simp [specialDerivative,specialJacobianMatrix,complexRow_apply,Pi.single_apply]

lemma specialRowFactor_normSq (A : Matrix (Fin N) (Fin n) ℝ) {m : ℕ} (hm : 1 ≤ m)
    (z : Fin n → ℂ) (j : Fin N) :
    Complex.normSq (specialRowFactor A m z j) =
      hessianWeight m (inverseF (complexRow A j z)) (deriv inverseF (complexRow A j z)) := by
  have he : ((2*(m-1) : ℕ) : ℝ) = 2*(m : ℝ)-2 := by
    rw [Nat.cast_mul,Nat.cast_sub hm]
    norm_num
    ; ring
  unfold specialRowFactor hessianWeight
  rw [Complex.normSq_mul,Complex.normSq_mul,Complex.normSq_natCast,
    map_pow,Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,← pow_mul,
    ← Real.rpow_natCast,he]
  ring

theorem specialJacobian_gram (A : Matrix (Fin N) (Fin n) ℝ) {m : ℕ} (hm : 1 ≤ m)
    (z : Fin n → ℂ) :
    (specialJacobianMatrix A m z).conjTranspose * specialJacobianMatrix A m z =
      (weightedGram A (fun j => hessianWeight m (inverseF (complexRow A j z))
        (deriv inverseF (complexRow A j z)))).map (algebraMap ℝ ℂ) := by
  ext i k
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,specialJacobianMatrix,map_mul,
    Matrix.map_apply,weightedGram_apply,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← specialRowFactor_normSq A hm z j]
  change star (specialRowFactor A m z j*(A j i : ℂ)) *
      (specialRowFactor A m z j*(A j k : ℂ)) =
      (A j i : ℂ)*(Complex.normSq (specialRowFactor A m z j) : ℂ)*(A j k : ℂ)
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
  ring

end SymmetricMahler

end OAI
