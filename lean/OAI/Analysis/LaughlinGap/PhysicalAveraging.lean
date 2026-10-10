import Mathlib
import OAI.Analysis.LaughlinGap.CovariantFamily
import OAI.Analysis.LaughlinGap.IrrepAveraging
import OAI.Analysis.LaughlinGap.ThreeSpin

namespace OAI

/-! Physical Averaging. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin

noncomputable def fockLowering (Q : ℕ) : FockMatrix (Q+1) :=
  secondQuantization (loweringMatrix (standardLadderSystem Q))

noncomputable def physicalPair (Q p : ℕ) : FockMatrix (Q+1) :=
  (1/Real.sqrt 2) • combination (productFamily annihilation annihilation) (physicalPairTensor Q p)

@[simp] lemma complexify_physicalPair (Q p : ℕ) :
    complexify (physicalPair Q p) = Occupation.localPair (Q+1) Q p := by
  rw [physicalPair, map_smul, complexify_combination]
  simp only [productFamily, map_mul, complexify_annihilation, Fintype.sum_prod_type,
    physicalPairTensor, Occupation.orderedPair_contraction]
  have he : (1/Real.sqrt 2 : ℝ) • ((Real.sqrt 2 : ℂ) • Occupation.localPair (Q+1) Q p) =
      ((1/Real.sqrt 2)*Real.sqrt 2 : ℝ) • Occupation.localPair (Q+1) Q p := by
    rw [mul_smul]; rfl
  rw [he, one_div_mul_cancel (by positivity : Real.sqrt 2 ≠ 0), one_smul]

lemma physicalPair_embedding {Q : ℕ} (hQ : 2 ≤ Q) (p : Fin (2*Q-2+1)) :
    physicalPair Q p.val = (1/Real.sqrt 2) •
      embeddingFamily (pairInclusion hQ) (productFamily annihilation annihilation) p := by
  simp only [embeddingFamily, pairInclusion_apply, Pi.single_apply,
    ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

theorem physicalPair_covariant {Q : ℕ} (hQ : 2 ≤ Q) :
    Covariant (fockLowering Q) (loweringMatrix (standardLadderSystem (2*Q-2)))
      (fun p : Fin (2*Q-2+1) => physicalPair Q p.val) := by
  have ha := annihilation_covariant (loweringMatrix (standardLadderSystem Q))
  have hp := (ha.product ha).embedding (pairInclusion hQ)
  have he : (fun p : Fin (2*Q-2+1) => physicalPair Q p.val) =
      (fun p => (1/Real.sqrt 2) • embeddingFamily (pairInclusion hQ)
        (productFamily annihilation annihilation) p) := funext (physicalPair_embedding hQ)
  rw [he]
  exact hp.smul (1/Real.sqrt 2)

noncomputable def physicalHamiltonian (Q : ℕ) : FockMatrix (Q+1) :=
  ∑ p : Fin (2*Q-1), (physicalPair Q p.val).transpose * physicalPair Q p.val

@[simp] lemma complexify_physicalHamiltonian (Q : ℕ) :
    complexify (physicalHamiltonian Q) = Occupation.physicalOccupationHamiltonian Q := by
  simp only [physicalHamiltonian, map_sum, map_mul, complexify_transpose,
    complexify_physicalPair, Occupation.physicalOccupationHamiltonian, Occupation.pairHamiltonian,
    Occupation.physicalPair_contraction]

lemma lift_identity {ι κ : Type*} (B : ι → Matrix κ κ ℝ) [Fintype ι] [DecidableEq ι]
    [Fintype κ] : lift B 1 = ∑ i, (B i).transpose * B i := by
  simp [lift, Matrix.one_apply, ite_smul]

lemma physicalPair_sum {Q : ℕ} (hQ : 2 ≤ Q) :
    (∑ p : Fin (2*Q-2+1), (physicalPair Q p.val).transpose * physicalPair Q p.val) =
      physicalHamiltonian Q := by
  let e : Fin (2*Q-2+1) ≃ Fin (2*Q-1) := finCongr (by omega)
  exact e.sum_comp (fun p => (physicalPair Q p.val).transpose * physicalPair Q p.val)

lemma physicalPair_single {Q : ℕ} (hQ : 2 ≤ Q) (p : Fin (2*Q-2+1)) :
    average (rotationCommutant (fockLowering Q))
      ((physicalPair Q p.val).transpose * physicalPair Q p.val) =
      (1/(2*Q-1 : ℕ) : ℝ) • physicalHamiltonian Q := by
  let B := fun p : Fin (2*Q-2+1) => physicalPair Q p.val
  have hc : combination B (Pi.single p 1) = physicalPair Q p.val := by
    simp [combination, B, Pi.single_apply, ite_smul]
  rw [← hc, ← lift_rankOne B, (physicalPair_covariant hQ).average_lift,
    standardSpin_average, Matrix.trace_vecMulVec]
  simp only [dotProduct_single_one, Pi.single_eq_same, map_smul]
  rw [lift_identity, physicalPair_sum hQ]
  rw [show 2*Q-2+1=2*Q-1 by omega]

lemma physicalPair_single_val {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-1) :
    average (rotationCommutant (fockLowering Q))
      ((physicalPair Q p).transpose * physicalPair Q p) =
      (1/(2*Q-1 : ℕ) : ℝ) • physicalHamiltonian Q :=
  physicalPair_single hQ ⟨p,by omega⟩

lemma physicalHamiltonian_mem {Q : ℕ} (hQ : 2 ≤ Q) :
    physicalHamiltonian Q ∈ rotationCommutant (fockLowering Q) := by
  have h := average_mem (rotationCommutant (fockLowering Q))
    ((physicalPair Q 0).transpose * physicalPair Q 0)
  rw [physicalPair_single_val hQ (by omega)] at h
  have hd : ((2*Q-1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  have he : ((2*Q-1 : ℕ) : ℝ) • ((1/(2*Q-1 : ℕ) : ℝ) • physicalHamiltonian Q) =
      physicalHamiltonian Q := by rw [smul_smul, mul_one_div_cancel hd, one_smul]
  exact he ▸ (rotationCommutant (fockLowering Q)).smul_mem h ((2*Q-1 : ℕ) : ℝ)

noncomputable def physicalTriple (Q : ℕ) :
    (Fin (2*Q-2+1) × Fin (Q+1)) → FockMatrix (Q+1) :=
  productFamily (fun p => physicalPair Q p.val) annihilation

theorem physicalTriple_covariant {Q : ℕ} (hQ : 2 ≤ Q) :
    Covariant (fockLowering Q) (loweringMatrix (tensorSpin (2*Q-2) Q)) (physicalTriple Q) :=
  (physicalPair_covariant hQ).product (annihilation_covariant _)

end LaughlinGap.RealOccupation

end

end OAI
