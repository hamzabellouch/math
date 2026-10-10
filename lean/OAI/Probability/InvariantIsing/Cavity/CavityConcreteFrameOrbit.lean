import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalBase
import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalFrameOrbit

namespace OAI

/-! The actual base interaction and special axes belong jointly to a
single prescribed Haar orbit, not merely to separate marginal orbits. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityReservoirRotation_leftRows {N n d : ℕ} (V : Orthogonal N)
    (F : Matrix (Fin (N + n)) (Fin d) ℝ) :
    cavityReservoirRows
      ((cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * F) =
      (V : Matrix (Fin N) (Fin N) ℝ).transpose * cavityReservoirRows F := by
  ext i j
  change (∑ k : Fin (N + n),
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      k (i.castAdd n) * F k j) =
    ∑ k : Fin N, (V : Matrix (Fin N) (Fin N) ℝ) k i * F (k.castAdd n) j
  simp only [Fin.sum_univ_add, cavityReservoirRotation_first,
    cavityReservoirRotation_lowerLeft, zero_mul, Finset.sum_const_zero, add_zero]

def cavityPhysicalSpecial {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (U : Orthogonal (N + n)) : Matrix (Fin N) (Fin d) ℝ :=
  cavityReservoirRows ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
    (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns U)) *
      B (cavityCompressionGrams g U)))

lemma measurable_cavityPhysicalSpecial {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : Measurable B) : Measurable (cavityPhysicalSpecial g B) := by
  let : OpensMeasurableSpace (Matrix (Fin (N + n)) (Fin (m * n)) ℝ ×
      Matrix (Fin (m * n)) (Fin d) ℝ) := inferInstanceAs
    (OpensMeasurableSpace ((Fin (N + n) → Fin (m * n) → ℝ) × (Fin (m * n) → Fin d → ℝ)))
  let : OpensMeasurableSpace (Orthogonal (N + n) × Matrix (Fin (N + n)) (Fin d) ℝ) :=
    inferInstanceAs (OpensMeasurableSpace (Orthogonal (N + n) × (Fin (N + n) → Fin d → ℝ)))
  have hX : Measurable (fun U : Orthogonal (N + n) =>
      cavitySpectralImage g (cavityColumns U)) := measurable_pi_iff.mpr
    (fun a => (measurable_cavitySpectralImage g a).comp (measurable_cavityColumns N n))
  have hW := (measurable_cavityEigenspaceFrame (N + n) m n).comp hX
  have hBU := hB.comp (measurable_cavityCompressionGrams g)
  have hmul : Continuous (fun p : Matrix (Fin (N + n)) (Fin (m * n)) ℝ ×
      Matrix (Fin (m * n)) (Fin d) ℝ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hWB := hmul.measurable.comp (hW.prodMk hBU)
  have hleft : Continuous (fun p : Orthogonal (N + n) × Matrix (Fin (N + n)) (Fin d) ℝ =>
      (p.1 : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * p.2) :=
    (continuous_subtype_val.comp continuous_fst).matrix_transpose.matrix_mul continuous_snd
  have h := hleft.measurable.comp (measurable_id.prodMk hWB)
  apply Measurable.of_eval_matrix
  intro i j
  exact h.eval_matrix

lemma cavityPhysicalSpecial_reservoir {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (U : Orthogonal (N + n)) (V : Orthogonal N) :
    cavityPhysicalSpecial g B (U * cavityReservoirRotation (n := n) V) =
      (V : Matrix (Fin N) (Fin N) ℝ).transpose * cavityPhysicalSpecial g B U := by
  have hc : cavityColumns (U * cavityReservoirRotation (n := n) V) = cavityColumns U :=
    cavityReservoirRotation_cavityColumns _ V
  unfold cavityPhysicalSpecial
  rw [hc, cavityCompressionGrams_reservoir]
  change cavityReservoirRows
    ((((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *
      (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).transpose) * _) = _
  rw [Matrix.transpose_mul, Matrix.mul_assoc, cavityReservoirRotation_leftRows]

theorem cavityPhysicalBaseSpecial_mem_orbit {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N + n) // g i = a} ≃ Fin (k a + n))
    (e : ((a : Fin m) × Fin (k a)) ⊕ Fin d ≃ Fin N)
    (U : Orthogonal (N + n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g U)).transpose * B (cavityCompressionGrams g U) = 1)
    (hBT : (B (cavityCompressionGrams g U)).transpose *
      cavitySpectralStack (cavityCompressionGrams g U) = 0)
    (hA : ∀ a, (cavityCompressionGrams g U a).PosDef) :
    ∃ V : Orthogonal N, cavityPhysicalBase g lam B (Matrix.diagonal lam₀) U =
      (V : Matrix (Fin N) (Fin N) ℝ) *
        Matrix.diagonal (fun j => Sum.elim (fun a => lam a.1) lam₀ (e.symm j)) *
          (V : Matrix (Fin N) (Fin N) ℝ).transpose ∧
      cavityPhysicalSpecial g B U = (V : Matrix (Fin N) (Fin N) ℝ) * cavityCanonicalSpecial e := by
  classical
  let A := cavityColumns U
  let X := cavitySpectralImage g A
  choose R hRG hRX hRS hRP using fun a => cavityRetainedFrame_exists g A a (ek a) (hA a)
  have hcross : ∀ a b, a ≠ b → (R a).transpose * R b = 0 := by
    intro a b hab
    exact cavitySpectralSupport_crossGram g a b hab (R a) (R b) (hRS a) (hRS b)
  have hperp : ∀ a b, (R a).transpose * cavityNormalizeFrame (X b) = 0 := by
    intro a b
    by_cases hab : a = b
    · subst b
      have h := congrArg Matrix.transpose (hRX a)
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
    · exact cavitySpectralSupport_crossGram g a b hab (R a) _ (hRS a)
        (cavityNormalizeFrame_spectral_support g A b)
  apply cavityBaseReplacement_physical_joint_orbit e U _ (cavityRetainedStack k R)
    (cavityEigenspaceFrame X) _ (B (cavityCompressionGrams g U))
    (cavitySpectralStack (cavityCompressionGrams g U)) (fun a => lam a.1) lam₀
  · exact cavityRetainedStack_gram k R hRG hcross
  · exact cavityEigenspaceFrame_gram X hA (cavitySpectralImage_crossGram g A)
  · exact cavityRetainedStack_perp k R X hperp
  · exact hB
  · exact hBT
  · change cavityEigenspaceFrame X * cavitySpectralStack (fun a => (X a).transpose * X a) = A
    rw [cavityEigenspaceFrame_stack X hA]
    exact cavitySpectralImage_sum g A
  · exact cavityRetainedStack_eigen g lam k R hRS
  · exact cavityEigenspaceFrame_eigen _ X lam (cavitySpectralImage_eigen g A lam)
  · exact cavityRetainedStack_complete g A k R hRP

end InvariantIsing

end

end OAI
