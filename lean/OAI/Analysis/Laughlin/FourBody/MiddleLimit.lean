import OAI.Analysis.Laughlin.FourBody.ErrorMatrix
import OAI.Analysis.Laughlin.FourBody.WedgeCompression

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix Topology
open Filter Spin

noncomputable def fourDimensionRatio (Q D : ℕ) : ℝ :=
  (4*(Q : ℝ)-1-2*(D : ℝ))/(2*(Q : ℝ)-1)

theorem fourDimensionRatio_tendsto (D : ℕ) : Tendsto (fun Q => fourDimensionRatio Q D) atTop (𝓝 2) := by
  have hi : Tendsto (fun Q : ℕ => (Q : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hn := (tendsto_const_nhds (x := (4 : ℝ))).sub (hi.const_mul (1+2*(D : ℝ)))
  have hd := (tendsto_const_nhds (x := (2 : ℝ))).sub hi
  have hh := hn.div hd (by norm_num : (2 : ℝ)-0 ≠ 0)
  have he : (fun Q : ℕ => fourDimensionRatio Q D) =ᶠ[atTop]
      (fun Q => (4-(1+2*(D : ℝ))*(Q : ℝ)⁻¹)/(2-(Q : ℝ)⁻¹)) := by
    filter_upwards [eventually_ge_atTop 1] with Q hQ
    have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
    unfold fourDimensionRatio
    field_simp
    ring
  apply Tendsto.congr' he.symm
  norm_num at hh
  apply hh.congr
  intro Q
  rfl

noncomputable def finiteFourMiddle (Q D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ :=
  Matrix.diagonal (fun i : Fin ((D+1)/2) => (if Certificate.copyLabel i=1 then fourDimensionRatio Q D else 0) + (3/10^6 : ℝ)) -
    Matrix.of (fun i j : Fin ((D+1)/2) => physicalFourError Q D (Certificate.copyLabel i) (Certificate.copyLabel j))

noncomputable def limitFourMiddle (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ :=
  Certificate.certificateDiagonal D - physicalLimitError D

theorem finiteFourMiddle_tendsto (D : ℕ) (i j : Fin ((D+1)/2)) :
    Tendsto (fun Q => finiteFourMiddle Q D i j) atTop (𝓝 (limitFourMiddle D i j)) := by
  have he := physicalFourError_certificate_tendsto D i j
  rw [← physicalLimitError_eq D] at he
  unfold finiteFourMiddle limitFourMiddle
  apply Tendsto.sub _ he
  by_cases hij : i=j
  · subst j
    by_cases hi : Certificate.copyLabel i=1
    · simpa [Matrix.diagonal_apply,hi,Certificate.certificateDiagonal,Matrix.map_apply] using
        (fourDimensionRatio_tendsto D).add_const (3/10^6 : ℝ)
    · simp [hi,Certificate.certificateDiagonal,Matrix.map_apply]
  · simp [hij,Certificate.certificateDiagonal,Matrix.map_apply]

end Laughlin.Fock

end OAI
