import OAI.Analysis.Laughlin.FourBody.MultiplicityHaar
import OAI.Analysis.Laughlin.FourBody.TraceReadout

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem trace_sandwich_list_sum {I J : Type*} [Fintype I] [Fintype J]
    (V W : Matrix I J ℝ) (l : List (Matrix I I ℝ)) :
    Matrix.trace (Vᵀ*l.sum*W) = (l.map (fun M => Matrix.trace (Vᵀ*M*W))).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons,List.map_cons,Matrix.mul_add,Matrix.add_mul,Matrix.trace_add,ih]

theorem negative_list_sum {I : Type*} (l : List I) (a b : I → ℝ)
    (h : ∀ i ∈ l, a i = -b i) : (l.map a).sum = -(l.map b).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,h i (by simp),ih (fun j hj => h j (by simp [hj]))]
    ring

theorem source_fourBody_rows_support : ∀ row ∈ Certificate.rows, ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
    e.1+e.2.1+(f.1+f.2.1-row.1) ≤ 23 := by decide

theorem source_physical_fourBody_trace_identity (Q D : ℕ) (hQ : 25 ≤ Q) (hD : D+2 ≤ Q)
    (r s : OddPairLabel D) :
    Matrix.trace ((retainedFourReal Q D hD r)ᵀ * physicalFourBodyMatrix Q * retainedFourReal Q D hD s) =
      physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s) := by
  unfold physicalFourBodyMatrix physicalFourError
  rw [trace_sandwich_list_sum]
  simp only [List.map_map,Function.comp_def]
  apply negative_list_sum
  intro row hrow
  unfold fourErrorRow
  rw [trace_sandwich_list_sum]
  simp only [List.map_map,Function.comp_def]
  apply negative_list_sum
  intro e he
  rw [trace_sandwich_list_sum]
  simp only [List.map_map,Function.comp_def]
  apply negative_list_sum
  intro f hf
  exact fourBodyTermMatrix_trace Q D row.1 hD r s e f
    (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)
    (by have := source_fourBody_rows_support row hrow e he f hf; omega)

theorem trace_real_sandwich_complex {I J : Type*} [Fintype I] [Fintype J]
    (V W : Matrix I J ℝ) (M : Matrix I I ℝ) :
    Matrix.trace ((V.map Complex.ofReal)ᴴ*M.map Complex.ofReal*W.map Complex.ofReal) =
      Complex.ofReal (Matrix.trace (Vᵀ*M*W)) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.transpose_apply,Matrix.map_apply,Complex.star_def,Complex.conj_ofReal,
    Complex.ofReal_sum,Complex.ofReal_mul]

theorem physical_fourBody_haar_multiplicity (Q D : ℕ) (hQ : 25 ≤ Q) (hD : D+2 ≤ Q)
    (r s : OddPairLabel D) :
    (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) *
        retainedFourInclusion Q D hD s =
      ((physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s) : ℂ) / (4*Q-1-2*D : ℕ)) • 1 := by
  rw [fourBody_haar_multiplicity_block,← retainedFourReal_complex Q D hD r,
    ← retainedFourReal_complex Q D hD s,trace_real_sandwich_complex,
    source_physical_fourBody_trace_identity Q D hQ hD]

end Laughlin.Spin

end OAI
