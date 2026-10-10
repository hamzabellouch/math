import Mathlib
import OAI.Analysis.LaughlinGap.IntertwinerAveraging
import OAI.Analysis.LaughlinGap.RealPositivity

namespace OAI

/-! Three Bounds. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma combination_one_bessel {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : ι → ℝ) (ha : dotProduct a a = 1) (B : ι → Matrix κ κ ℝ) :
    ((∑ i, (B i).transpose * B i) - (combination B a).transpose * combination B a).PosSemidef := by
  let S : Matrix Unit ι ℝ := fun _ => a
  have hS : S * S.transpose = 1 := by
    ext i j
    change (∑ k, a k * a k) = 1
    exact ha
  simpa [S] using combination_bessel S hS B

omit [Fintype ι] [DecidableEq ι] in
lemma highestCombination_range [Fintype ι] [DecidableEq ι] {n m z : ℕ} (hz : z ≤ min n m)
    (B : (Fin (n+1) × Fin (m+1)) → Matrix ι ι ℝ) :
    combination B (highestTensor n m z) =
      ∑ p : Fin (z+1), highestCoefficient n m z p.val •
        B (⟨p.val, by omega⟩,⟨z-p.val,by omega⟩) := by
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk]
  let f : Fin (z+1) → Fin (n+1) × Fin (m+1) :=
    fun p => (⟨p.val,by omega⟩, ⟨z-p.val,by omega⟩)
  symm
  apply Finset.sum_bij_ne_zero (fun p _ _ => f p)
  · intro p hp hn; exact Finset.mem_univ _
  · intro p hp hn q hq hnq he
    exact Fin.ext (congrArg (fun a : Fin (n+1) × Fin (m+1) => a.1.val) he)
  · intro a ha hn
    have he : a.1.val+a.2.val=z := by
      by_contra he
      simp [highestTensor, he] at hn
    let p : Fin (z+1) := ⟨a.1.val,by omega⟩
    have hf : f p = a := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        dsimp [f,p]
        omega
    refine ⟨p,Finset.mem_univ _,?_,hf⟩
    simpa only [← hf, highestTensor, show (f p).1.val+(f p).2.val=z by dsimp [f]; omega,
      ite_true] using hn
  · intro p hp hn
    simp only [highestTensor, show (f p).1.val+(f p).2.val=z by dsimp [f]; omega, ite_true]
    rfl

noncomputable def threeSpinLift {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) : FockMatrix (Q+1) :=
  lift (physicalTriple Q) (tensorProjection (show z ≤ min (2*Q-2) Q by omega))

lemma threeSpinLift_positive {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (threeSpinLift hQ hz).PosSemidef := by
  apply lift_positive
  rw [tensorProjection_eq]
  apply Matrix.posSemidef_sum
  intro l hl
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star
    (coupledTensor (2*Q-2) Q z l.val)

lemma threeSpinLift_average_highest {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    average (rotationCommutant (fockLowering Q))
      ((combination (physicalTriple Q) (highestTensor (2*Q-2) Q z)).transpose *
        combination (physicalTriple Q) (highestTensor (2*Q-2) Q z)) =
      (1/((2*Q-2)+Q-2*z+1 : ℕ) : ℝ) • threeSpinLift hQ hz := by
  let hz' : z ≤ min (2*Q-2) Q := by omega
  have he : (coupledEmbedding hz').toLinearMap (Pi.single (0 : Fin ((2*Q-2)+Q-2*z+1)) 1) =
      highestTensor (2*Q-2) Q z := by
    rw [coupledEmbedding_apply]
    simp [Pi.single_apply, ite_smul]
  rw [← lift_rankOne, (physicalTriple_covariant hQ).average_lift, ← he,
    equal_copy_average]
  simp only [ite_true, map_smul]
  simp only [threeSpinLift, tensorProjection, LadderMap.comp, LadderMap.transpose,
    LinearMap.toMatrix'_comp, toMatrix_transposeMap, LadderMap.matrix]

lemma average_mono (S : StarSubalgebra ℝ (Matrix ι ι ℝ))
    {A B : Matrix ι ι ℝ} (h : A ≤ B) : average S A ≤ average S B := by
  have hh := average_positive S (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h))
  rw [map_sub] at hh
  exact sub_nonneg.mp hh.nonneg

lemma threeSpinLift_le {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    threeSpinLift hQ hz ≤
      (threeBodyDimensionRatio Q z * (z+1 : ℕ)) • physicalHamiltonian Q := by
  let hz' : z ≤ min (2*Q-2) Q := by omega
  let a : Fin (z+1) → ℝ := fun p => highestCoefficient (2*Q-2) Q z p.val
  let B : Fin (z+1) → FockMatrix (Q+1) := fun p =>
    annihilation ⟨z-p.val,by omega⟩ * physicalPair Q p.val
  have hn : dotProduct a a = 1 := by
    simp only [a, dotProduct, ← sq]
    rw [Fin.sum_univ_eq_sum_range (fun p => highestCoefficient (2*Q-2) Q z p ^ 2)]
    exact highestCoefficient_sum_sq hz' 
  have hc : combination B a = combination (physicalTriple Q) (highestTensor (2*Q-2) Q z) := by
    rw [highestCombination_range hz']
    rfl
  have hb := (combination_one_bessel a hn B).nonneg
  have hbs : (combination B a).transpose * combination B a ≤
      ∑ p : Fin (z+1), (physicalPair Q p.val).transpose * physicalPair Q p.val := by
    apply (sub_nonneg.mp hb).trans
    apply Finset.sum_le_sum
    intro p hp
    exact sub_nonneg.mp (annihilation_square_le ⟨z-p.val,by omega⟩ (physicalPair Q p.val)).nonneg
  have ha := average_mono (rotationCommutant (fockLowering Q)) hbs
  rw [hc, threeSpinLift_average_highest hQ hz, map_sum] at ha
  have hf (p : Fin (z+1)) : average (rotationCommutant (fockLowering Q))
      ((physicalPair Q p.val).transpose * physicalPair Q p.val) =
      (1/(2*Q-1 : ℕ) : ℝ) • physicalHamiltonian Q :=
    physicalPair_single_val hQ (by omega)
  simp only [hf, ← Finset.sum_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at ha
  have hd : (0 : ℝ) < ((2*Q-2)+Q-2*z+1 : ℕ) := by positivity
  have hb' := smul_le_smul_of_nonneg_left ha hd.le
  have hr : ((2*Q-2+Q-2*z+1 : ℕ) : ℝ) /
      ((2*Q-1 : ℕ) : ℝ) = threeBodyDimensionRatio Q z := by
    rw [threeBodyDimensionRatio, Nat.cast_add, Nat.cast_sub (by omega : 2*z ≤ 2*Q-2+Q),
      Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ 2*Q), Nat.cast_sub (by omega : 1 ≤ 2*Q)]
    push_cast
    ring
  simp only [smul_smul, mul_one_div_cancel hd.ne', one_smul] at hb'
  convert hb' using 1
  congr 1
  rw [← hr]
  push_cast
  ring

lemma physicalHamiltonian_positive (Q : ℕ) : (physicalHamiltonian Q).PosSemidef :=
  Matrix.posSemidef_sum _ (fun _ _ => transpose_square_positive _)

lemma threeTailTerm_le {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) (hz16 : 16 ≤ z) :
    -(threeBodyTailTerm Q z) • physicalHamiltonian Q ≤
      (threeBodyGramCoefficient Q z) • threeSpinLift (hQ.trans' (by omega : 2 ≤ 4)) hz := by
  let hQ' : 2 ≤ Q := by omega
  have heq : (-1 : ℝ)^z * fallingRatio Q z *
      (3*(z:ℝ)-1-(z:ℝ)*((z:ℝ)+1)/(Q:ℝ)) = threeBodyGramCoefficient Q z := rfl
  rcases Nat.even_or_odd z with he | ho
  · have hq : 0 ≤ threeBodyGramCoefficient Q z := by
      rw [threeBodyGramCoefficient, he.neg_one_pow, one_mul]
      exact mul_nonneg (fallingRatio_nonneg Q z) (threeBodyBracket_nonneg hQ hz hz16)
    have ht : threeBodyTailTerm Q z = 0 := by
      simp [threeBodyTailTerm, (Nat.not_odd_iff_even.mpr he)]
    rw [ht, neg_zero, zero_smul]
    exact smul_nonneg hq (threeSpinLift_positive hQ' hz).nonneg
  · have h17 : 17 ≤ z := by
      have hn : z ≠ 16 := by rintro rfl; norm_num at ho
      omega
    have hq : threeBodyGramCoefficient Q z ≤ 0 := by
      rw [threeBodyGramCoefficient, ho.neg_one_pow, neg_one_mul, neg_mul]
      exact neg_nonpos.mpr (mul_nonneg (fallingRatio_nonneg Q z) (threeBodyBracket_nonneg hQ hz hz16))
    have hh := smul_le_smul_of_nonneg_left (threeSpinLift_le hQ' hz)
      (abs_nonneg (threeBodyGramCoefficient Q z))
    have hhh := neg_le_neg hh
    simp only [smul_smul, ← neg_smul, abs_of_nonpos hq, neg_neg] at hhh
    convert hhh using 1
    congr 1
    rw [threeBodyTailTerm, ite_eq_left ⟨h17,ho,hz⟩, abs_of_nonpos hq]
    push_cast
    ring

noncomputable def threeTailLift {Q : ℕ} (hQ : 2 ≤ Q) : FockMatrix (Q+1) :=
  ∑ z : Fin (Q+1), if 16 ≤ z.val then
    (threeBodyGramCoefficient Q z.val) • threeSpinLift hQ (Nat.le_of_lt_succ z.isLt) else 0

theorem threeTailLift_le {Q : ℕ} (hQ : 4 ≤ Q) :
    -(threeBodyTail Q) • physicalHamiltonian Q ≤ threeTailLift (by omega : 2 ≤ Q) := by
  have hh : (∑ z : Fin (Q+1), -(threeBodyTailTerm Q z.val) • physicalHamiltonian Q) ≤
      threeTailLift (by omega : 2 ≤ Q) := by
    unfold threeTailLift
    apply Finset.sum_le_sum
    intro z hz
    by_cases he : 16 ≤ z.val
    · rw [ite_eq_left he]
      exact threeTailTerm_le hQ (Nat.le_of_lt_succ z.isLt) he
    · have ht : threeBodyTailTerm Q z.val = 0 := by
        simp [threeBodyTailTerm, show ¬ 17 ≤ z.val by omega]
      simp [he,ht]
  convert hh using 1
  rw [← Finset.sum_smul, Finset.sum_neg_distrib,
    Fin.sum_univ_eq_sum_range (fun z => threeBodyTailTerm Q z)]
  rfl

end LaughlinGap.RealOccupation

end

end OAI
