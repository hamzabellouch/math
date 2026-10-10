import OAI.Combinatorics.ContingencyTables.Sampling.ExactRareMeasureBound
import OAI.Combinatorics.ContingencyTables.Sampling.ExactRareCost

namespace OAI

/-! # Absorbing the actual public correction cost by its branch probability -/

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms CompletionCounts Polynomial
open scoped BigOperators Classical
noncomputable section

lemma exact_scale_absorbed {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : Polynomial ℕ) (A : ℕ) :
    p.eval (A*exactBoxScale r c) ≤ 2^(correctionPrecision r c)*
      (p.eval A*2^((40*p.natDegree)^2)) := by
  apply RareBranchRuntime.polynomial_tabulation_bound
  change ((dimensionAllowance (I := Fin m) (J := Fin n))^3*smallBinaryLength r c)^2 ≤
    (dimensionAllowance (I := Fin m) (J := Fin n))^6*(smallBinaryLength r c)^2
  rw [mul_pow,←pow_mul]

theorem exact_public_correction_bound (print : Polynomial ℕ) : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ), (∑ i,r i)=∑ j,c j →
    let B := print.eval (ExactPrintCost.matrixSize (n := n) r)
    ExactPublicCost.budget r c 1 B B+1 ≤
      2^(correctionPrecision r c)*p.eval (Algorithms.samplingSize n r 0) := by
  obtain ⟨p,hp⟩ := ExactRareCost.public_polynomial
  obtain ⟨q,a,hq⟩ := exact_rare_measure_bound
  obtain ⟨g,hg⟩ := exact_gate_measure_polynomial
  let H := a+g+91*X^2+print.comp (25*X^3)+1
  let P := p.comp (X+q)
  refine ⟨C (2^((40*P.natDegree)^2))*(P.comp H),?_⟩
  intro m n r c htotal
  let B := print.eval (ExactPrintCost.matrixSize (n := n) r)
  let S := Algorithms.samplingSize n r 0
  let E := exactBoxScale r c
  let W := H.eval S*E
  have hE : 1 ≤ E := exactBoxScale_pos r c
  have hHW : H.eval S ≤ W := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (H.eval S) hE
  have ha : a.eval S ≤ H.eval S := by simp only [H,eval_add,eval_one]; omega
  have hrare : exactRareMeasure (List.ofFn r,List.ofFn c) ≤ q.eval W :=
    (hq m n r c htotal).trans (polynomial_eval_monotone q (Nat.mul_le_mul_right E ha))
  have hscalar : weight (Algorithms.encodeMargins r c)+
      ExactGateCost.measure (List.ofFn r,List.ofFn c)+B ≤ H.eval S := by
    have hw := exact_public_weight r c htotal
    have hgate := hg m n r c htotal
    have hprint : print.eval (ExactPrintCost.matrixSize (n := n) r) ≤ print.eval (25*S^3) :=
      polynomial_eval_monotone print (exact_matrix_size (n := n) r)
    simp only [H,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_comp,eval_one]
    unfold B S at *
    omega
  have hmeasure : ExactRareCost.publicMeasure (Algorithms.encodeMargins r c) B ≤ (X+q).eval W := by
    change weight (Algorithms.encodeMargins r c)+
      (ExactGateCost.measure (ProfilePrograms.exactParsedMargins (Algorithms.encodeMargins r c))+
        exactRareMeasure (ProfilePrograms.exactParsedMargins (Algorithms.encodeMargins r c)))+B ≤ _
    rw [exactParsedMargins_spec]
    simp only [eval_add,eval_X]
    omega
  have hcost : ExactPublicCost.budget r c 1 B B+1 ≤ P.eval W := by
    have ht := (hp (Algorithms.encodeMargins r c) B).trans (polynomial_eval_monotone p hmeasure)
    simpa only [ExactPublicCost.budget,ExactTablePrefix.input,P,eval_comp] using ht
  have habsorb := exact_scale_absorbed r c P (H.eval S)
  apply hcost.trans (habsorb.trans_eq ?_)
  simp only [eval_mul,eval_C,eval_comp]
  ring

end
end ContingencyTables.SmallGraphProfiles

end OAI
