import OAI.Analysis.Cotype.PatternNormalization

namespace OAI

noncomputable section

namespace Cotype
variable {m : ℕ}

def rowProjection (F : SignMatrix m → ℝ) (i : Fin m) (S : SignMatrix m) : ℝ :=
  average (fun σ : Cube m => sign (σ i) * F (xorCube (rowCube σ) S))

theorem rowProjection_oddPart (F : SignMatrix m → ℝ) (i : Fin m) (S : SignMatrix m) :
    rowProjection (oddPart F) i S = rowProjection F i S := by
  have hn : average (fun σ : Cube m => sign (σ i) * F (negateCube (xorCube (rowCube σ) S))) =
      -rowProjection F i S := by
    rw [← average_negate (fun σ : Cube m => sign (σ i) * F (negateCube (xorCube (rowCube σ) S)))]
    have he (σ : Cube m) : negateCube (xorCube (rowCube (negateCube σ)) S) =
        xorCube (rowCube σ) S := by
      change negateCube (xorCube (negateCube (rowCube σ)) S) = _
      rw [xorCube_negate_left, negateCube_negateCube]
    simp only [he, negateCube, sign_not, neg_mul]
    simp [rowProjection, average]
  simp only [rowProjection, oddPart, ← mul_div_assoc, mul_sub, average_div_real, average_sub_real]
  rw [hn]
  unfold rowProjection
  ring

theorem row_twist_change (Φ : SignMatrix m → Cube m → Cube m → ℝ)
    (S : SignMatrix m) (ε δ : Cube m) (i : Fin m) :
    average (fun σ : Cube m => sign (σ i) * Φ (dampedSample ε δ (xorCube (rowCube σ) S)) ε δ) =
    average (fun ξ : Cube m => (sign (ε i) * sign (ξ i)) * Φ (dampedSample ξ δ S) ε δ) := by
  rw [← average_translate ε (fun ξ : Cube m =>
    (sign (ε i) * sign (ξ i)) * Φ (dampedSample ξ δ S) ε δ)]
  congr 1
  funext σ
  have he : dampedSample (xorCube ε σ) δ S = dampedSample ε δ (xorCube (rowCube σ) S) := by
    funext ij
    simp [dampedSample, xorCube, rowCube, columnCube, Bool.xor_left_comm]
  rw [he]
  change _ = (sign (ε i) * sign (Bool.xor (ε i) (σ i))) * _
  rw [sign_xor, ← mul_assoc (sign (ε i)), sign_sq, one_mul]

theorem sign_coordinate_odd (ψ : Cube m → ℝ) (i : Fin m) (s : Cube m) :
    average (fun ξ : Cube m => sign (ξ i) * ψ (fun j => Bool.xor (ξ i) (s j))) = oddPart ψ s := by
  rw [average_coordinate i (fun b => sign b * ψ (fun j => Bool.xor b (s j)))]
  simp [oddPart, sub_eq_add_neg]
  rfl

theorem matrixTwist_row_projection (Φ : SignMatrix m → Cube m → Cube m → ℝ)
    (ψ : Cube m → Cube m → ℝ) (a : ℝ)
    (hm : ∀ S δ i, moment ℝ (fun ε => Φ S ε δ) i = a * ψ (fun j => S (i,j)) δ)
    (i : Fin m) (S : SignMatrix m) :
    rowProjection (matrixTwist Φ) i S = a * oddPart (vectorTwist ψ) (fun j => S (i,j)) := by
  calc
    _ = average (fun ε => average (fun δ => average (fun σ : Cube m =>
        sign (σ i) * Φ (dampedSample ε δ (xorCube (rowCube σ) S)) ε δ))) := by
      unfold rowProjection matrixTwist
      simp only [← average_mul_left]
      rw [average_comm]
      congr 1; funext ε; rw [average_comm]
    _ = average (fun ε => average (fun δ => average (fun ξ : Cube m =>
        (sign (ε i) * sign (ξ i)) * Φ (dampedSample ξ δ S) ε δ))) := by
      simp_rw [row_twist_change]
    _ = average (fun ξ : Cube m => average (fun δ : Cube m =>
        sign (ξ i) * moment ℝ (fun ε => Φ (dampedSample ξ δ S) ε δ) i)) := by
      rw [average_comm]
      simp_rw [average_comm (fun ε ξ : Cube m =>
        (sign (ε i) * sign (ξ i)) * Φ (dampedSample ξ _ S) ε _)]
      rw [average_comm]
      congr 1; funext ξ
      congr 1; funext δ
      simp only [moment, smul_eq_mul, ← average_mul_left]
      congr 1; funext ε; ring
    _ = average (fun ξ : Cube m => average (fun δ : Cube m =>
        sign (ξ i) * (a * ψ (fun j => dampedSample ξ δ S (i,j)) δ))) := by simp_rw [hm]
    _ = a * average (fun δ : Cube m => average (fun ξ : Cube m =>
        sign (ξ i) * ψ (fun j => Bool.xor (ξ i) ((xorCube δ (fun j => S (i,j))) j)) δ)) := by
      rw [average_comm]
      simp only [← average_mul_left]
      congr 1; funext δ
      congr 1; funext ξ
      dsimp [dampedSample, rowCube, columnCube, xorCube]
      ring
    _ = _ := by
      have he (δ : Cube m) : average (fun ξ : Cube m => sign (ξ i) *
          ψ (fun j => Bool.xor (ξ i) ((xorCube δ (fun j => S (i,j))) j)) δ) =
          oddPart (fun s => ψ s δ) (xorCube δ (fun j => S (i,j))) :=
        sign_coordinate_odd (fun s => ψ s δ) i _
      simp_rw [he]
      rw [oddPart_vectorTwist]

def columnProjection (F : SignMatrix m → ℝ) (j : Fin m) (S : SignMatrix m) : ℝ :=
  average (fun τ : Cube m => sign (τ j) * F (xorCube (columnCube τ) S))

theorem columnProjection_oddPart (F : SignMatrix m → ℝ) (j : Fin m) (S : SignMatrix m) :
    columnProjection (oddPart F) j S = columnProjection F j S := by
  exact rowProjection_oddPart (fun R => F (transposeCube R)) j (transposeCube S)

theorem matrixTwist_transpose_swap (Φ : SignMatrix m → Cube m → Cube m → ℝ) (S : SignMatrix m) :
    matrixTwist (fun R ε δ => Φ (transposeCube R) δ ε) S = matrixTwist Φ (transposeCube S) := by
  unfold matrixTwist
  rw [average_comm]
  congr 1; funext ε
  congr 1; funext δ
  have he : transposeCube (dampedSample δ ε S) = dampedSample ε δ (transposeCube S) := by
    funext ij
    simp [transposeCube, dampedSample, xorCube, rowCube, columnCube, Bool.xor_left_comm]
  exact congrArg (fun R => Φ R ε δ) he

theorem matrixTwist_column_projection (Φ : SignMatrix m → Cube m → Cube m → ℝ)
    (φ : Cube m → Cube m → ℝ) (b : ℝ)
    (hm : ∀ S ε j, moment ℝ (fun δ => Φ S ε δ) j = b * φ (fun i => S (i,j)) ε)
    (j : Fin m) (S : SignMatrix m) :
    columnProjection (matrixTwist Φ) j S = b * oddPart (vectorTwist φ) (fun i => S (i,j)) := by
  have h := matrixTwist_row_projection (fun R ε δ => Φ (transposeCube R) δ ε) φ b
    (fun R δ i => hm (transposeCube R) δ i) j (transposeCube S)
  simp only [rowProjection, matrixTwist_transpose_swap] at h
  exact h

end Cotype

end

end OAI
