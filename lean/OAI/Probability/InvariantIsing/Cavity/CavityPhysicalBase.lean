import OAI.Probability.InvariantIsing.Cavity.CavityReservoirRotation
import OAI.Probability.InvariantIsing.Cavity.CavityConcreteBase
import OAI.Probability.InvariantIsing.Cavity.CavityOrbitFactorizationAE

namespace OAI

/-! Measurable base interaction built from the actual cavity columns. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

def cavityColumns {N n : ℕ} (U : Orthogonal (N + n)) :
    Matrix (Fin (N + n)) (Fin n) ℝ :=
  fun i j => (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j)

def cavityCompressionGrams {N n m : ℕ} (g : Fin (N + n) → Fin m)
    (U : Orthogonal (N + n)) : Fin m → Matrix (Fin n) (Fin n) ℝ :=
  fun a => (cavitySpectralImage g (cavityColumns U) a).transpose *
    cavitySpectralImage g (cavityColumns U) a

def cavityPhysicalBase {N n m d : ℕ} (g : Fin (N + n) → Fin m) (lam : Fin m → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) (U : Orthogonal (N + n)) :
    Matrix (Fin N) (Fin N) ℝ :=
  ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
    cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i)))
      (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns U)))
      (cavityRepeatedSpectrum (n := n) lam) (B (cavityCompressionGrams g U)) A₀ *
    (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).submatrix
      (Fin.castAdd n) (Fin.castAdd n)

lemma measurable_cavityColumns (N n : ℕ) :
    Measurable (cavityColumns : Orthogonal (N + n) → Matrix (Fin (N + n)) (Fin n) ℝ) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact (Matrix.measurable_apply (i := i) (j := Fin.natAdd N j)).comp measurable_subtype_coe

lemma measurable_cavityCompressionGrams {N n m : ℕ} (g : Fin (N + n) → Fin m) :
    Measurable (cavityCompressionGrams g) := by
  apply measurable_pi_iff.mpr
  intro a
  have hX := (measurable_cavitySpectralImage g a).comp (measurable_cavityColumns N n)
  exact ((continuous_id.matrix_transpose.matrix_mul continuous_id).measurable).comp hX

lemma measurable_cavityPhysicalBase {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (lam : Fin m → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : Measurable B) (A₀ : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (cavityPhysicalBase g lam B A₀) := by
  let : OpensMeasurableSpace (Matrix (Fin (N + n)) (Fin (m * n)) ℝ ×
      Matrix (Fin (m * n)) (Fin d) ℝ) := inferInstanceAs
    (OpensMeasurableSpace ((Fin (N + n) → Fin (m * n) → ℝ) × (Fin (m * n) → Fin d → ℝ)))
  let : OpensMeasurableSpace (Orthogonal (N + n) ×
      Matrix (Fin (N + n)) (Fin (N + n)) ℝ) := inferInstanceAs
    (OpensMeasurableSpace (Orthogonal (N + n) × (Fin (N + n) → Fin (N + n) → ℝ)))
  have hX : Measurable (fun U : Orthogonal (N + n) =>
      cavitySpectralImage g (cavityColumns U)) := measurable_pi_iff.mpr
    (fun a => (measurable_cavitySpectralImage g a).comp (measurable_cavityColumns N n))
  have hW := (measurable_cavityEigenspaceFrame (N + n) m n).comp hX
  have hBU := hB.comp (measurable_cavityCompressionGrams g)
  have hrep : Continuous (fun p : Matrix (Fin (N + n)) (Fin (m * n)) ℝ ×
      Matrix (Fin (m * n)) (Fin d) ℝ =>
      cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i))) p.1
        (cavityRepeatedSpectrum (n := n) lam) p.2 A₀) := by
    unfold cavityBaseReplacement
    exact (continuous_const.sub ((continuous_fst.matrix_mul continuous_const).matrix_mul
      continuous_fst.matrix_transpose)).add
        (((continuous_fst.matrix_mul continuous_snd).matrix_mul continuous_const).matrix_mul
          (continuous_fst.matrix_mul continuous_snd).matrix_transpose)
  have hJ := hrep.measurable.comp (hW.prodMk hBU)
  have hconj : Continuous (fun p : Orthogonal (N + n) ×
      Matrix (Fin (N + n)) (Fin (N + n)) ℝ =>
      (p.1 : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * p.2 *
        (p.1 : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)) :=
    (((continuous_subtype_val.comp continuous_fst).matrix_transpose.matrix_mul
      continuous_snd).matrix_mul (continuous_subtype_val.comp continuous_fst))
  have h := hconj.measurable.comp (measurable_id.prodMk hJ)
  apply Measurable.of_eval_matrix
  intro i j
  exact h.eval_matrix

lemma cavityCompressionGrams_reservoir {N n m : ℕ} (g : Fin (N + n) → Fin m)
    (U : Orthogonal (N + n)) (V : Orthogonal N) :
    cavityCompressionGrams g (U * cavityReservoirRotation (n := n) V) =
      cavityCompressionGrams g U := by
  unfold cavityCompressionGrams
  have hc : cavityColumns (U * cavityReservoirRotation (n := n) V) = cavityColumns U :=
    cavityReservoirRotation_cavityColumns _ V
  rw [hc]

lemma cavityPhysicalBase_reservoir {N n m d : ℕ} (g : Fin (N + n) → Fin m)
    (lam : Fin m → ℝ)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (U : Orthogonal (N + n)) (V : Orthogonal N) :
    cavityPhysicalBase g lam B A₀ (U * cavityReservoirRotation (n := n) V) =
      (V : Matrix (Fin N) (Fin N) ℝ).transpose * cavityPhysicalBase g lam B A₀ U *
        (V : Matrix (Fin N) (Fin N) ℝ) := by
  have hc : cavityColumns (U * cavityReservoirRotation (n := n) V) = cavityColumns U :=
    cavityReservoirRotation_cavityColumns _ V
  unfold cavityPhysicalBase
  rw [hc, cavityCompressionGrams_reservoir]
  let J := cavityBaseReplacement (Matrix.diagonal (fun i => lam (g i)))
    (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns U)))
    (cavityRepeatedSpectrum (n := n) lam) (B (cavityCompressionGrams g U)) A₀
  change (((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).transpose *
    J * ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) *
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ))).submatrix
      (Fin.castAdd n) (Fin.castAdd n) =
    (V : Matrix (Fin N) (Fin N) ℝ).transpose *
      ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * J *
        (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).submatrix
          (Fin.castAdd n) (Fin.castAdd n) * (V : Matrix (Fin N) (Fin N) ℝ)
  rw [Matrix.transpose_mul]
  simpa only [Matrix.mul_assoc] using cavityReservoirRotation_conjugate V
    ((U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose * J *
      (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ))

theorem cavityPhysicalBase_mem_orbit {N n m d : ℕ}
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
          (V : Matrix (Fin N) (Fin N) ℝ).transpose := by
  exact cavityConcreteBase_spectral_orbit g k ek e U lam lam₀
    (B (cavityCompressionGrams g U)) (cavitySpectralStack (cavityCompressionGrams g U))
    hB hBT rfl hA

end InvariantIsing

end

end OAI
