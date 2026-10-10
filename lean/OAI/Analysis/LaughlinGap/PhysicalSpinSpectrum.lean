import Mathlib
import OAI.Analysis.LaughlinGap.WedgeIdentification

namespace OAI

/-! Physical Spin Spectrum. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct ComplexOrder
open Occupation

noncomputable def physicalThreeFamily {Q : ℕ} (hQ : 2 ≤ Q)
    (i : CoupledIndex (2*Q-2) Q) :
    EuclideanSpace ℂ (Fin (2*Q-1) × Fin (Q+1)) :=
  WithLp.toLp 2 (physicalThreeVector hQ i.1.val i.2.val)

theorem physicalThreeFamily_orthonormal {Q : ℕ} (hQ : 2 ≤ Q) :
    Orthonormal ℂ (physicalThreeFamily hQ) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have h := (orthonormal_iff_ite.mp (coupledFamily_orthonormal (2*Q-2) Q)) i j
  simp only [coupledFamily, EuclideanSpace.inner_toLp_toLp, star_trivial] at h
  simp only [physicalThreeFamily, EuclideanSpace.inner_toLp_toLp,
    physicalThreeVector, dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [(physicalThreeIndexEquiv hQ).sum_comp (fun a =>
    coupledTensor (2*Q-2) Q j.1.val j.2.val a *
      coupledTensor (2*Q-2) Q i.1.val i.2.val a)]
  rw [show (∑ a, coupledTensor (2*Q-2) Q j.1.val j.2.val a *
      coupledTensor (2*Q-2) Q i.1.val i.2.val a) =
      if i=j then 1 else 0 from h]
  split_ifs <;> rfl

noncomputable def physicalThreeBasis {Q : ℕ} (hQ : 2 ≤ Q) :
    OrthonormalBasis (CoupledIndex (2*Q-2) Q) ℂ
      (EuclideanSpace ℂ (Fin (2*Q-1) × Fin (Q+1))) := by
  letI : Nonempty (CoupledIndex (2*Q-2) Q) := ⟨⟨0,0⟩⟩
  have hc : Fintype.card (CoupledIndex (2*Q-2) Q) =
      Module.finrank ℂ (EuclideanSpace ℂ (Fin (2*Q-1) × Fin (Q+1))) := by
    rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, coupledIndex_card]
    congr 1
    omega
  let b := basisOfOrthonormalOfCardEqFinrank (physicalThreeFamily_orthonormal hQ) hc
  exact b.toOrthonormalBasis (by simpa [b] using physicalThreeFamily_orthonormal hQ)

@[simp] lemma physicalThreeBasis_apply {Q : ℕ} (hQ : 2 ≤ Q)
    (i : CoupledIndex (2*Q-2) Q) :
    physicalThreeBasis hQ i = physicalThreeFamily hQ i := by
  simp [physicalThreeBasis]

noncomputable def physicalThreeRankOne {Q : ℕ} (hQ : 2 ≤ Q) (z l : ℕ) :
    Matrix (Fin (2*Q-1) × Fin (Q+1)) (Fin (2*Q-1) × Fin (Q+1)) ℂ :=
  Matrix.vecMulVec (physicalThreeVector hQ z l) (star (physicalThreeVector hQ z l))

theorem physicalThreeRankOne_positive {Q : ℕ} (hQ : 2 ≤ Q) (z l : ℕ) :
    (physicalThreeRankOne hQ z l).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

noncomputable def physicalThreeProjection {Q : ℕ} (hQ : 2 ≤ Q) (z : ℕ) :
    Matrix (Fin (2*Q-1) × Fin (Q+1)) (Fin (2*Q-1) × Fin (Q+1)) ℂ :=
  ∑ l : Fin ((2*Q-2)+Q-2*z+1), physicalThreeRankOne hQ z l.val

lemma physicalThreeProjection_positive {Q : ℕ} (hQ : 2 ≤ Q) (z : ℕ) :
    (physicalThreeProjection hQ z).PosSemidef := by
  apply Matrix.posSemidef_sum
  exact fun l _ => physicalThreeRankOne_positive hQ z l.val

theorem physicalTripleGram_spectral {Q : ℕ} (hQ : 2 ≤ Q) :
    (tripleWedgeMatrix (physicalPairForms Q)).conjTranspose *
      tripleWedgeMatrix (physicalPairForms Q) - 1 =
    ∑ i : CoupledIndex (2*Q-2) Q,
      (threeBodyGramCoefficient Q i.1.val : ℂ) •
        physicalThreeRankOne hQ i.1.val i.2.val := by
  classical
  ext a b
  have he := congrFun (orderedThreeGram_defect_expansion hQ
    (Pi.single (physicalThreeIndexEquiv hQ b) 1)) (physicalThreeIndexEquiv hQ a)
  have hid : (Pi.single (physicalThreeIndexEquiv hQ b) (1 : ℝ) :
      (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) (physicalThreeIndexEquiv hQ a) = if a=b then 1 else 0 := by
    simp [Pi.single_apply]
  simp only [Pi.sub_apply, hid, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct_single_one] at he
  rw [Matrix.sub_apply, physicalTripleGram_entry hQ, Matrix.one_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, physicalThreeRankOne,
    Matrix.vecMulVec_apply, Pi.star_apply, physicalThreeVector,
    Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum]
  have hcast : (if a=b then (1 : ℂ) else 0) = ↑(if a=b then (1:ℝ) else 0) := by
    split_ifs <;> rfl
  rw [hcast, ← Complex.ofReal_sub, he]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem physicalTripleGram_spin_blocks {Q : ℕ} (hQ : 2 ≤ Q) :
    (tripleWedgeMatrix (physicalPairForms Q)).conjTranspose *
      tripleWedgeMatrix (physicalPairForms Q) - 1 =
    ∑ z : Fin (min (2*Q-2) Q+1),
      (threeBodyGramCoefficient Q z.val : ℂ) • physicalThreeProjection hQ z.val := by
  rw [physicalTripleGram_spectral hQ, Fintype.sum_sigma]
  simp only [physicalThreeProjection, Finset.smul_sum]

lemma physicalThreeVector_inner {Q : ℕ} (hQ : 2 ≤ Q)
    (i j : CoupledIndex (2*Q-2) Q) :
    dotProduct (star (physicalThreeVector hQ i.1.val i.2.val))
      (physicalThreeVector hQ j.1.val j.2.val) = if i=j then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (physicalThreeFamily_orthonormal hQ)) i j
  simpa only [physicalThreeFamily, EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using h

lemma physicalThreeRankOne_mul {Q : ℕ} (hQ : 2 ≤ Q)
    (i j : CoupledIndex (2*Q-2) Q) :
    physicalThreeRankOne hQ i.1.val i.2.val * physicalThreeRankOne hQ j.1.val j.2.val =
      if i=j then physicalThreeRankOne hQ i.1.val i.2.val else 0 := by
  classical
  simp only [physicalThreeRankOne, Matrix.vecMulVec_mul_vecMulVec,
    physicalThreeVector_inner hQ]
  split_ifs with h
  · subst j
    simp
  · simp

theorem physicalThreeProjection_idempotent {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    physicalThreeProjection hQ z * physicalThreeProjection hQ z =
      physicalThreeProjection hQ z := by
  classical
  let z' : Fin (min (2*Q-2) Q+1) := ⟨z, by omega⟩
  have hr (l k : Fin ((2*Q-2)+Q-2*z+1)) :
      physicalThreeRankOne hQ z l.val * physicalThreeRankOne hQ z k.val =
      if l=k then physicalThreeRankOne hQ z l.val else 0 := by
    simpa using physicalThreeRankOne_mul hQ ⟨z',l⟩ ⟨z',k⟩
  simp only [physicalThreeProjection, Matrix.sum_mul, Matrix.mul_sum, hr]
  simp

theorem physicalThreeProjection_orthogonal {Q z w : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hw : w ≤ Q) (hne : z ≠ w) :
    physicalThreeProjection hQ z * physicalThreeProjection hQ w = 0 := by
  classical
  let z' : Fin (min (2*Q-2) Q+1) := ⟨z, by omega⟩
  let w' : Fin (min (2*Q-2) Q+1) := ⟨w, by omega⟩
  have hr (l : Fin ((2*Q-2)+Q-2*z+1)) (k : Fin ((2*Q-2)+Q-2*w+1)) :
      physicalThreeRankOne hQ z l.val * physicalThreeRankOne hQ w k.val = 0 := by
    have hh : (Sigma.mk z' l : CoupledIndex (2*Q-2) Q) ≠ ⟨w',k⟩ := by
      intro he
      exact hne (congrArg (fun i : CoupledIndex (2*Q-2) Q => i.1.val) he)
    exact (physicalThreeRankOne_mul hQ ⟨z',l⟩ ⟨w',k⟩).trans (ite_eq_right hh)
  simp only [physicalThreeProjection, Matrix.sum_mul, Matrix.mul_sum, hr,
    Finset.sum_const_zero]

theorem physicalThreeProjection_wedge_null {Q z : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hn : z=0 ∨ z=1 ∨ z=3) :
    tripleWedgeMatrix (physicalPairForms Q) * physicalThreeProjection hQ z = 0 := by
  simp only [physicalThreeProjection, physicalThreeRankOne, Matrix.mul_sum,
    Matrix.mul_vecMulVec]
  apply Finset.sum_eq_zero
  intro l hl
  rw [physicalTripleWedge_null hQ hz (by omega : l.val ≤ (2*Q-2)+Q-2*z) hn]
  simp

end LaughlinGap.Spin

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder
open Spin

noncomputable def physicalSpinThreeLift {Q : ℕ} (hQ : 2 ≤ Q) (z : ℕ) :
    Module.End ℂ (Hilbert (Q+1)) :=
  exteriorLift (tripleWedgeMatrix (physicalPairForms Q) * physicalThreeProjection hQ z *
    (tripleWedgeMatrix (physicalPairForms Q)).conjTranspose)

theorem physicalSpinThreeLift_positive {Q : ℕ} (hQ : 2 ≤ Q) (z : ℕ) :
    (physicalSpinThreeLift hQ z).IsPositive := by
  apply exteriorLift_positive
  exact (physicalThreeProjection_positive hQ z).mul_mul_conjTranspose_same _

theorem physical_spin_square {Q : ℕ} (hQ : 2 ≤ Q) :
    physicalOccupationHamiltonian Q * physicalOccupationHamiltonian Q =
      physicalOccupationHamiltonian Q +
      (∑ z : Fin (min (2*Q-2) Q+1),
        (threeBodyGramCoefficient Q z.val : ℂ) • physicalSpinThreeLift hQ z.val) +
      exteriorLift (pairWedgeMatrix (physicalPairForms Q) *
        (pairWedgeMatrix (physicalPairForms Q)).conjTranspose) := by
  rw [physical_normal_ordered_square hQ, physicalTripleGram_spin_blocks hQ]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    map_sum, map_smul, physicalSpinThreeLift]

end LaughlinGap.Occupation

end

end OAI
