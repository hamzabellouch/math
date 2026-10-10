import OAI.Probability.InvariantIsing.Cavity.CavityCompressionFactors
import OAI.Probability.InvariantIsing.Cavity.CavityFrameOrbit

namespace OAI

/-! A uniform bound for the actual random cavity coefficients.  It
depends only on the fixed cavity dimensions and spectral values. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_frame_entry_bound {s d : ℕ} (B : Matrix (Fin s) (Fin d) ℝ)
    (hB : B.transpose * B = 1) (i : Fin s) (j : Fin d) : |B i j| ≤ 1 := by
  have hn := (cavity_orthonormal_of_gram B hB).norm_eq_one j
  have hi := PiLp.norm_apply_le (WithLp.toLp 2 (fun i : Fin s => B i j) :
    EuclideanSpace ℝ (Fin s)) i
  simpa only [PiLp.toLp_apply, Real.norm_eq_abs, hn] using hi

lemma cavity_frame_block_mass_bound {s d n : ℕ} (D : Matrix (Fin s) (Fin s) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (T : Matrix (Fin s) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hT : T.transpose * T = 1) :
    cavityMatrixMass (B.transpose * D * T) ≤ (d : ℝ)*n*cavityMatrixMass D := by
  have hb (i : Fin d) (j : Fin n) : |(B.transpose * D * T) i j| ≤ cavityMatrixMass D := by
    have hh := cavity_bilinear_abs_bound D (fun l => B l i) (fun l => T l j)
      zero_le_one zero_le_one (fun l => cavity_frame_entry_bound B hB l i)
      (fun l => cavity_frame_entry_bound T hT l j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simpa only [one_mul, mul_one] using hh
  change (∑ i, ∑ j, |(B.transpose * D * T) i j|) ≤ (d : ℝ)*n*cavityMatrixMass D
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin n, cavityMatrixMass D :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring

lemma cavity_matrix_mass_sub_le {d n : ℕ} (A B : Matrix (Fin d) (Fin n) ℝ) :
    cavityMatrixMass (A-B) ≤ cavityMatrixMass A+cavityMatrixMass B := by
  unfold cavityMatrixMass
  simp only [Matrix.sub_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => abs_sub _ _))

theorem cavity_small_factor_size_bound {s d n : ℕ} (D : Matrix (Fin s) (Fin s) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (T : Matrix (Fin s) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hT : T.transpose * T = 1) :
    let A := cavitySmallFactorBlocks D A₀ B T
    cavityFactorSize A.1 A.2.1 A.2.2 ≤
      ((d : ℝ)*d+d*n+n*n)*cavityMatrixMass D+cavityMatrixMass A₀ := by
  intro A
  have hK : cavityMatrixMass (B.transpose * D * B-A₀) ≤
      (d : ℝ)*d*cavityMatrixMass D+cavityMatrixMass A₀ :=
    (cavity_matrix_mass_sub_le (B.transpose * D * B) A₀).trans
      (add_le_add (cavity_frame_block_mass_bound D B B hB hB) le_rfl)
  have hL := cavity_frame_block_mass_bound D B T hB hT
  have hC := cavity_frame_block_mass_bound D T T hT hT
  dsimp only [A, cavitySmallFactorBlocks, cavityFactorSize]
  nlinarith

theorem cavity_compression_factor_size_bound {N m d n : ℕ}
    (g : Fin (N+n) → Fin m) (e : Fin (m*n) ≃ Fin (d+n))
    (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (U : Orthogonal (N+n)) :
    let A := cavityCompressionFactorBlocks e lam lam₀ B₀ (cavityCompressionGrams g U)
    cavityFactorSize A.1 A.2.1 A.2.2 ≤
      ((d : ℝ)*d+d*n+n*n)*cavityMatrixMass (cavityRepeatedSpectrum (n := n) lam)+
        cavityMatrixMass (Matrix.diagonal lam₀) := by
  intro A
  apply cavity_small_factor_size_bound
  · exact cavityConcreteComplement_gram g e B₀ U
  · rw [cavitySpectralStack_gram, cavityCompressionGrams_sum]
    intro a
    simpa only [cavityCompressionGrams, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (cavitySpectralImage g (cavityColumns U) a)

end InvariantIsing

end

end OAI
