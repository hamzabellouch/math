import OAI.Analysis.PureInfiniteness.UltrapowerMatrixCut
import OAI.Analysis.WeakInfiniteness.RectangularCStar
import OAI.Analysis.JiangSu.Nonunital.MatrixDiagonal

namespace OAI

/-! The row with an exact cut diagonal Gram matrix used in KR02 Remark 7.5.
The original positive elements may be arbitrary elements of the norm
ultrapower, as required when iterating the abelianization argument. -/

noncomputable section
open scoped NNReal ENNReal

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem ultrapower_cut_gram_row (hP : MainGap.PropertyP A)
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]
    (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∀ f : Fin n → NormUltra.QuotientAlgebra (fun _ : ℕ => A) U,
      (∀ i, 0 ≤ f i) → (∀ i, ‖f i‖ ≤ 1) →
      ∃ d : Fin n → NormUltra.QuotientAlgebra (fun _ : ℕ => A) U,
      (∀ i, ‖d i‖ ≤ C) ∧
      ∃ h : CStarMatrix (Fin 1) (Fin n) (NormUltra.QuotientAlgebra (fun _ : ℕ => A) U),
        (∀ i, h 0 i = CFC.sqrt (f i) * d i) ∧ ‖h‖ ≤ 1 ∧
        h.conjTranspose * h = NonunitalGamma.diagonalHom (fun i => MainGap.cut (f i) δ) := by
  classical
  obtain ⟨C, hC, hdiag⟩ := ultrapower_matrix_cut_diagonalization hP U 1 δ hδ
  refine ⟨C, hC, ?_⟩
  intro n f hfp hfn
  let M (i j : Fin n) := CFC.sqrt (f i) * CFC.sqrt (f j)
  have hM (i : Fin n) : M i i = f i := CFC.sqrt_mul_sqrt_self _ (hfp i)
  obtain ⟨d, hdn, hdd, hdo⟩ := hdiag n M
    (fun i => by rw [hM]; exact hfp i) (fun i => by rw [hM]; exact hfn i)
  let h : CStarMatrix (Fin 1) (Fin n) (NormUltra.QuotientAlgebra (fun _ : ℕ => A) U) :=
    CStarMatrix.ofMatrix (fun _ i => CFC.sqrt (f i) * d i)
  have hgram : h.conjTranspose * h =
      NonunitalGamma.diagonalHom (fun i => MainGap.cut (f i) δ) := by
    ext i j
    change (∑ k : Fin 1, star (h k i) * h k j) =
      if i = j then MainGap.cut (f i) δ else 0
    simp only [Fin.sum_univ_one]
    change star (CFC.sqrt (f i) * d i) * (CFC.sqrt (f j) * d j) =
      if i = j then MainGap.cut (f i) δ else 0
    rw [star_mul, (CFC.sqrt_nonneg (f i)).isSelfAdjoint.star_eq]
    split_ifs with hij
    · subst j
      have hi := hdd i
      rw [hM] at hi
      calc
        _ = star (d i) * (CFC.sqrt (f i) * CFC.sqrt (f i)) * d i := by
          simp only [mul_assoc]
        _ = star (d i) * f i * d i := by rw [CFC.sqrt_mul_sqrt_self _ (hfp i)]
        _ = _ := hi
    · simpa only [M, mul_assoc] using hdo i j hij
  refine ⟨d, hdn, h, fun _ => rfl, ?_, hgram⟩
  have hnorm : ‖h‖ ^ 2 ≤ 1 := by
    rw [← rectangular_norm_initial, hgram]
    exact NonunitalGamma.diagonalHom_norm_le_one _ fun i =>
      (MainGap.norm_cut_le (hfp i) δ.2).trans (hfn i)
  nlinarith [norm_nonneg h]

end WeakPureInfiniteness

end

end OAI
