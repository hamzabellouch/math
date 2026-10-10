import OAI.Analysis.Cotype.PatternProjections
import OAI.Analysis.Cotype.CoefficientCompactness

namespace OAI

noncomputable section

namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {n m k : ℕ} {T : X →L[ℝ] Y} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T n m Dg Df)

def normalizedMatrix (hn : m+m ≤ n) (S : SignMatrix m) : ℝ :=
  d.gamma⁻¹ * oddPart (matrixTwist (d.patternPairing hn)) S

def normalizedPrimal (hn : m+1 ≤ n) (s : Cube m) : ℝ :=
  d.gamma⁻¹ * oddPart (vectorTwist (d.patternPrimal hn)) s

def normalizedDual (hn : 1+m ≤ n) (s : Cube m) : ℝ :=
  d.gamma⁻¹ * oddPart (vectorTwist (d.patternDual hn)) s

theorem normalizedPrimal_coefficient (hn : m+1 ≤ n) (i : Fin m) :
    fourier (d.normalizedPrimal hn) (unitIndex i) = 1/(2*24*Dg*Real.sqrt m) := by
  unfold normalizedPrimal
  rw [fourier_const_mul, vectorTwist_first_coefficient (d.patternPrimal hn)
    ((1/(2*24*Dg*Real.sqrt m))*d.gamma) (fun s i => by rw [d.patternPrimal_moment]; ring)]
  rw [mul_left_comm, inv_mul_cancel₀ (ne_of_gt d.gamma_pos), mul_one]

theorem normalizedDual_coefficient (hn : 1+m ≤ n) (i : Fin m) :
    fourier (d.normalizedDual hn) (unitIndex i) = 1/(2*24*Df*Real.sqrt m) := by
  unfold normalizedDual
  rw [fourier_const_mul, vectorTwist_first_coefficient (d.patternDual hn)
    ((1/(2*24*Df*Real.sqrt m))*d.gamma) (fun s i => by rw [d.patternDual_moment]; ring)]
  rw [mul_left_comm, inv_mul_cancel₀ (ne_of_gt d.gamma_pos), mul_one]

theorem normalizedMatrix_row (hn : m+m ≤ n) (hd : 1+m ≤ n) (i : Fin m) (S : SignMatrix m) :
    rowProjection (d.normalizedMatrix hn) i S =
      (1/(2*24*Dg*Real.sqrt m)) * d.normalizedDual hd (fun j => S (i,j)) := by
  calc
    _ = d.gamma⁻¹ * rowProjection (oddPart (matrixTwist (d.patternPairing hn))) i S := by
      simp only [rowProjection, normalizedMatrix, ← average_mul_left]
      congr 1; funext σ; ring
    _ = _ := by
      rw [rowProjection_oddPart, matrixTwist_row_projection (d.patternPairing hn) (d.patternDual hd)
        (1/(2*24*Dg*Real.sqrt m)) (fun S δ i => d.patternPairing_primal_moment hn hd S δ i)]
      unfold normalizedDual
      ring

theorem normalizedMatrix_column (hn : m+m ≤ n) (hp : m+1 ≤ n) (j : Fin m) (S : SignMatrix m) :
    columnProjection (d.normalizedMatrix hn) j S =
      (1/(2*24*Df*Real.sqrt m)) * d.normalizedPrimal hp (fun i => S (i,j)) := by
  calc
    _ = d.gamma⁻¹ * columnProjection (oddPart (matrixTwist (d.patternPairing hn))) j S := by
      simp only [columnProjection, normalizedMatrix, ← average_mul_left]
      congr 1; funext τ; ring
    _ = _ := by
      rw [columnProjection_oddPart, matrixTwist_column_projection (d.patternPairing hn) (d.patternPrimal hp)
        (1/(2*24*Df*Real.sqrt m)) (fun S ε j => d.patternPairing_dual_moment hn hp S ε j)]
      unfold normalizedPrimal
      ring

variable (d : GrowthPairingData T (k+m+m) m Dg Df)

private theorem normalized_value_bound {x : ℝ}
    (hx : |x| ≤ walshNorm k T)
    (hslow : walshNorm k T ≤ 2 * walshNorm (k+m+m) T) : |d.gamma⁻¹ * x| ≤ 4 := by
  rw [abs_mul, abs_of_pos (inv_pos.mpr d.gamma_pos)]
  have hw : walshNorm k T ≤ 4*d.gamma := by linarith [d.gamma_half]
  calc
    _ ≤ d.gamma⁻¹ * (4*d.gamma) :=
      mul_le_mul_of_nonneg_left (hx.trans hw) (le_of_lt (inv_pos.mpr d.gamma_pos))
    _ = 4 := by rw [mul_left_comm, inv_mul_cancel₀ (ne_of_gt d.gamma_pos), mul_one]

theorem normalized_scalar_admissible (hm : 0 < m)
    (hn : m+m ≤ k+m+m) (hp : m+1 ≤ k+m+m) (hd : 1+m ≤ k+m+m)
    (hslow : walshNorm k T ≤ 2 * walshNorm (k+m+m) T) :
    ScalarAdmissible m (1/(2*24*Dg*Real.sqrt m)) (1/(2*24*Df*Real.sqrt m))
      (d.normalizedMatrix hn) (d.normalizedPrimal hp) (d.normalizedDual hd) := by
  refine ⟨?_,?_,?_,?_,?_,?_,d.normalizedPrimal_coefficient hp,
    d.normalizedDual_coefficient hd,d.normalizedMatrix_row hn hd,d.normalizedMatrix_column hn hp⟩
  · intro S; unfold normalizedMatrix; rw [oddPart_isOdd]; ring
  · intro s; unfold normalizedPrimal; rw [oddPart_isOdd]; ring
  · intro s; unfold normalizedDual; rw [oddPart_isOdd]; ring
  · intro S
    apply d.normalized_value_bound (hslow := hslow)
    rw [oddPart_matrixTwist]
    apply abs_average_le_const
    intro ε
    apply abs_average_le_const
    intro δ
    exact d.patternPairing_odd_bound hn _ ε δ
  · intro s
    apply d.normalized_value_bound (hslow := hslow)
    rw [oddPart_vectorTwist]
    apply abs_average_le_const
    intro ε
    exact d.patternPrimal_odd_bound hm hp _ ε
  · intro s
    apply d.normalized_value_bound (hslow := hslow)
    rw [oddPart_vectorTwist]
    apply abs_average_le_const
    intro δ
    exact d.patternDual_odd_bound hm hd _ δ

end GrowthPairingData
end Cotype

end

end OAI
