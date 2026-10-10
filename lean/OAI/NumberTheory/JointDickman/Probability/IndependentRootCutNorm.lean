import OAI.NumberTheory.JointDickman.Amplification.CandidateMatrix

namespace OAI

/-! # Expected cut norm of independent centered candidate weights -/

namespace JointDickman
open Finset
open PublishedInputs

theorem independent_candidate_cutMaximum {ι Ω κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (row col : ι → κ) (w Y : ι → Ω → ℝ)
    (hw : ∀ i x, 0 ≤ w i x) (hwone : ∀ i, (∑ x, w i x) = 1)
    {a : ℝ} (ha : 0 ≤ a) (hY : ∀ i x, 0 ≤ Y i x ∧ Y i x ≤ a)
    {t : ℝ} (ht : 0 < t) (hsmall : 2*t*a ≤ 1) :
    finiteExpectation (siteProductMass w) (fun x =>
      kernelCutMaximum (candidateMatrix row col
        (fun i => Y i (x i)-finiteExpectation (w i) (Y i)))) ≤
      (Real.log (Fintype.card (EdgeCutTest κ))+
        4*t^2*a*(∑ i, finiteExpectation (w i) (Y i)))/t := by
  have hdom : ∀ x : ι → Ω,
      kernelCutMaximum (candidateMatrix row col
        (fun i => Y i (x i)-finiteExpectation (w i) (Y i))) ≤
      finiteFamilyMaximum (fun s : EdgeCutTest κ => fun x : ι → Ω =>
        ∑ i, edgeCutCoefficient row col s i*(Y i (x i)-finiteExpectation (w i) (Y i))) x := by
    intro x
    exact candidateMatrix_cutMaximum_le row col _
  exact (finiteExpectation_mono (siteProductMass w) (siteProductMass_nonneg w hw) hdom).trans
    (independent_root_maximum w Y hw hwone ha hY (edgeCutCoefficient row col)
      (edgeCutCoefficient_bound row col) ht hsmall)

theorem card_edgeCutTest (κ : Type*) [Fintype κ] [DecidableEq κ] :
    Fintype.card (EdgeCutTest κ) = 2^(Fintype.card κ+Fintype.card κ+1) := by
  simp [EdgeCutTest,pow_add,mul_assoc]

theorem log_card_edgeCutTest (κ : Type*) [Fintype κ] [DecidableEq κ] :
    Real.log (Fintype.card (EdgeCutTest κ)) =
      (2*(Fintype.card κ : ℝ)+1)*Real.log 2 := by
  rw [card_edgeCutTest,Nat.cast_pow,Real.log_pow]
  push_cast
  ring

theorem independent_candidate_cutNorm {ι Ω κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (row col : ι → κ) (w Y : ι → Ω → ℝ)
    (hw : ∀ i x, 0 ≤ w i x) (hwone : ∀ i, (∑ x, w i x) = 1)
    {a : ℝ} (ha : 0 ≤ a) (hY : ∀ i x, 0 ≤ Y i x ∧ Y i x ≤ a)
    {t : ℝ} (ht : 0 < t) (hsmall : 2*t*a ≤ 1) :
    finiteExpectation (siteProductMass w) (fun x =>
      kernelCutNorm (candidateMatrix row col
        (fun i => Y i (x i)-finiteExpectation (w i) (Y i)))) ≤
      ((2*(Fintype.card κ : ℝ)+1)*Real.log 2+
        4*t^2*a*(∑ i, finiteExpectation (w i) (Y i)))/(t*Fintype.card κ) := by
  have h := div_le_div_of_nonneg_right
    (independent_candidate_cutMaximum row col w Y hw hwone ha hY ht hsmall)
    (Nat.cast_nonneg (Fintype.card κ) : (0 : ℝ) ≤ _)
  rw [log_card_edgeCutTest,div_div] at h
  convert h using 1
  unfold kernelCutNorm finiteExpectation
  simp only [mul_div_assoc,sum_div]

end JointDickman

end OAI
