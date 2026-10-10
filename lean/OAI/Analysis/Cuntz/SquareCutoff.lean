import OAI.Analysis.Cuntz.Regularization
import OAI.Analysis.Cuntz.Squares
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

namespace OAI

noncomputable section

/-! Intertwining functional calculus and cutoffs of adjoint squares. -/

open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] matrixRealFunctionalCalculus productMatrixRealFunctionalCalculus

section Rectangular
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Real functional calculus commutes with genuine diagonal blocks. -/
theorem cfc_cuntzBlock (a : CStarMatrix ι ι A) (b : CStarMatrix κ κ A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f (CStarMatrix.ofMatrix (cuntzBlock a b)) =
      CStarMatrix.ofMatrix (cuntzBlock (CStarMatrix.ofMatrix.symm (cfc f a))
        (CStarMatrix.ofMatrix.symm (cfc f b))) := by
  let φ := cuntzBlockHom (A := A) (ι := ι) (κ := κ)
  have h := φ.map_cfc f (a,b) (hf := hf.continuousOn)
    (ha := by exact Prod.ext ha.isSelfAdjoint hb.isSelfAdjoint)
    (hφa := (cuntzBlock_nonneg _ _ ha hb).isSelfAdjoint)
  rw [cfc_map_prod (S := ℂ) f a b (hf := hf.continuousOn)
    (ha := ha.isSelfAdjoint) (hb := hb.isSelfAdjoint)
    (hab := by exact Prod.ext ha.isSelfAdjoint hb.isSelfAdjoint)] at h
  exact h.symm

/-- Intertwining positives also intertwines their continuous real functions.
The proof uses block commutation, so no polar decomposition is assumed. -/
theorem cfc_matrix_intertwine (a : CStarMatrix ι ι A) (b : CStarMatrix κ κ A)
    (x : Matrix ι κ A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : CStarMatrix.ofMatrix.symm a * x = x * CStarMatrix.ofMatrix.symm b)
    (f : ℝ → ℝ) (hf : Continuous f) :
    CStarMatrix.ofMatrix.symm (cfc f a) * x = x * CStarMatrix.ofMatrix.symm (cfc f b) := by
  let D : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A := CStarMatrix.ofMatrix (cuntzBlock a b)
  let X : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A := CStarMatrix.ofMatrix (Matrix.fromBlocks 0 x 0 0)
  have hc : Commute D X := by
    have hc' :
        (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a) 0 0 (CStarMatrix.ofMatrix.symm b) *
          Matrix.fromBlocks 0 x 0 0 : Matrix (ι ⊕ κ) (ι ⊕ κ) A) =
        Matrix.fromBlocks 0 x 0 0 *
          Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a) 0 0 (CStarMatrix.ofMatrix.symm b) := by
      simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hx]
    exact hc'
  have h := (hc.cfc_real f).eq
  rw [show cfc f D = CStarMatrix.ofMatrix (cuntzBlock
      (CStarMatrix.ofMatrix.symm (cfc f a)) (CStarMatrix.ofMatrix.symm (cfc f b))) from
    cfc_cuntzBlock a b ha hb f hf] at h
  have h' := congrArg (fun z : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A =>
    (CStarMatrix.ofMatrix.symm z).submatrix Sum.inl Sum.inr) h
  change (cuntzBlock (CStarMatrix.ofMatrix.symm (cfc f a)) (CStarMatrix.ofMatrix.symm (cfc f b)) * Matrix.fromBlocks 0 x 0 0).submatrix Sum.inl Sum.inr =
    (Matrix.fromBlocks 0 x 0 0 * cuntzBlock (CStarMatrix.ofMatrix.symm (cfc f a)) (CStarMatrix.ofMatrix.symm (cfc f b))).submatrix Sum.inl Sum.inr at h'
  ext i j
  simpa [cuntzBlock, Matrix.fromBlocks_multiply, Matrix.submatrix] using congrFun (congrFun h' i) j

end Rectangular

/-- A continuous cutoff factor, regular at zero for a strictly positive threshold. -/
def cutoffSquareFactor (ε t : ℝ) : ℝ := Real.sqrt (max (t-ε) 0 / max t ε)

theorem cutoffSquareFactor_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (cutoffSquareFactor ε) := by
  apply Continuous.sqrt
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact (hε.trans_le (le_max_right t ε)).ne'

theorem cutoffSquareFactor_identity {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    cutoffSquareFactor ε t * t * cutoffSquareFactor ε t = max (t-ε) 0 := by
  have hd : 0 < max t ε := hε.trans_le (le_max_right _ _)
  have hs := Real.mul_self_sqrt (div_nonneg (le_max_right (t-ε) 0) hd.le)
  change Real.sqrt _ * t * Real.sqrt _ = _
  rw [mul_right_comm, hs]
  rcases le_total t ε with h | h
  · simp [max_eq_right (sub_nonpos.mpr h)]
  · rw [max_eq_left h, div_mul_cancel₀ _ (hε.trans_le h).ne']

/-- The actual cutoff factors as g(a) a g(a). -/
theorem cutoffSquareFactor_cfc {a : A} (ha : 0 ≤ a) {ε : ℝ} (hε : 0 < ε) :
    cfc (cutoffSquareFactor ε) a * a * cfc (cutoffSquareFactor ε) a =
      cuntzCutoff a ε := by
  have hf : ContinuousOn (cutoffSquareFactor ε) (spectrum ℝ a) := (cutoffSquareFactor_continuous hε).continuousOn
  have he : cfc (fun t : ℝ => cutoffSquareFactor ε t * t * cutoffSquareFactor ε t) a =
      cfc (cutoffSquareFactor ε) a * a * cfc (cutoffSquareFactor ε) a := by
    rw [cfc_mul (fun t : ℝ => cutoffSquareFactor ε t * t) (cutoffSquareFactor ε) a
      (hf.mul continuousOn_id) hf, cfc_mul (cutoffSquareFactor ε) (fun t : ℝ => t) a
      hf continuousOn_id, cfc_id' ℝ a ha.isSelfAdjoint]
  rw [← he]
  apply cfc_congr
  intro t ht
  exact cutoffSquareFactor_identity hε t

/-- Matching positive cutoffs of unequal rectangular Gram matrices are
Cuntz equivalent, proved by an exact rectangular factorization. -/
theorem cuntzEquivalent_cutoff_rectangular_gram {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (x : Matrix ι κ A) (ha : 0 ≤ CStarMatrix.ofMatrix (x*x.conjTranspose))
    (hb : 0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x)) {ε : ℝ} (hε : 0 < ε) :
    CuntzEquivalent
      (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix (x*x.conjTranspose)) ε))
      (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix (x.conjTranspose*x)) ε)) := by
  classical
  let a := CStarMatrix.ofMatrix (x*x.conjTranspose)
  let b := CStarMatrix.ofMatrix (x.conjTranspose*x)
  let L := cfc (cutoffSquareFactor ε) a
  let R := cfc (cutoffSquareFactor ε) b
  have hL : star L = L := (cfc_predicate _ _ : IsSelfAdjoint L).star_eq
  have hR : star R = R := (cfc_predicate _ _ : IsSelfAdjoint R).star_eq
  have hx : CStarMatrix.ofMatrix.symm L * x = x * CStarMatrix.ofMatrix.symm R :=
    cfc_matrix_intertwine a b x ha hb (Matrix.mul_assoc _ _ _) _
      (cutoffSquareFactor_continuous hε)
  let y := CStarMatrix.ofMatrix.symm L * x
  have hy : y = x * CStarMatrix.ofMatrix.symm R := hx
  have hl : y*y.conjTranspose = CStarMatrix.ofMatrix.symm (cuntzCutoff a ε) := by
    dsimp only [y]
    rw [Matrix.conjTranspose_mul]
    change CStarMatrix.ofMatrix.symm L * x * (x.conjTranspose * CStarMatrix.ofMatrix.symm (star L)) = _
    rw [hL]
    have he := cutoffSquareFactor_cfc ha hε
    change L * a * L = _ at he
    have he' := congrArg CStarMatrix.ofMatrix.symm he
    change CStarMatrix.ofMatrix.symm L * (x*x.conjTranspose) * CStarMatrix.ofMatrix.symm L = _ at he'
    simpa only [Matrix.mul_assoc] using he'
  have hr : y.conjTranspose*y = CStarMatrix.ofMatrix.symm (cuntzCutoff b ε) := by
    rw [hy, Matrix.conjTranspose_mul]
    change CStarMatrix.ofMatrix.symm (star R) * x.conjTranspose * (x * CStarMatrix.ofMatrix.symm R) = _
    rw [hR]
    have he := cutoffSquareFactor_cfc hb hε
    change R * b * R = _ at he
    have he' := congrArg CStarMatrix.ofMatrix.symm he
    change CStarMatrix.ofMatrix.symm R * (x.conjTranspose*x) * CStarMatrix.ofMatrix.symm R = _ at he'
    simpa only [Matrix.mul_assoc] using he'
  rw [← hl, ← hr]
  exact cuntzEquivalent_rectangular_gram y

end Kaplansky

end

end OAI
