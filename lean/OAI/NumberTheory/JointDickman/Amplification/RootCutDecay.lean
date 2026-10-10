import OAI.NumberTheory.JointDickman.Probability.IndependentRootCutNorm

namespace OAI

/-! # A vanishing cut-norm error from the per-candidate weight cap -/

namespace JointDickman
open Finset
open PublishedInputs

theorem independent_candidate_cutNorm_small {ι Ω κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (row col : ι → κ) (w Y : ι → Ω → ℝ)
    (hw : ∀ i x, 0 ≤ w i x) (hwone : ∀ i, (∑ x, w i x) = 1)
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/2)
    (hY : ∀ i x, 0 ≤ Y i x ∧ Y i x ≤ δ^2) :
    finiteExpectation (siteProductMass w) (fun x =>
      kernelCutNorm (candidateMatrix row col
        (fun i => Y i (x i)-finiteExpectation (w i) (Y i)))) ≤
      δ*(3*Real.log 2+4*(∑ i, finiteExpectation (w i) (Y i))/(Fintype.card κ : ℝ)) := by
  have hsmall : 2*(1/δ)*δ^2 ≤ 1 := by
    have he : 2*(1/δ)*δ^2 = 2*δ := by field_simp
    rw [he]
    linarith only [hδsmall]
  have h := independent_candidate_cutNorm row col w Y hw hwone (sq_nonneg δ) hY
    (one_div_pos.mpr hδ) hsmall
  have hM : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hM0 : (Fintype.card κ : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hM)
  have hinv : 1/(Fintype.card κ : ℝ) ≤ 1 :=
    (div_le_one (lt_of_lt_of_le zero_lt_one hM)).mpr hM
  apply h.trans
  calc
    _ = δ*((2+1/(Fintype.card κ : ℝ))*Real.log 2+
        4*(∑ i, finiteExpectation (w i) (Y i))/(Fintype.card κ : ℝ)) := by
      field_simp
    _ ≤ _ := by
      gcongr
      linarith only [hinv]

end JointDickman

end OAI
