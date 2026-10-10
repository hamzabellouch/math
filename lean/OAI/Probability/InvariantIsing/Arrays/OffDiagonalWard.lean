import OAI.Probability.InvariantIsing.Core.PairGibbs

namespace OAI

/-! Exact two-replica off-diagonal Haar Ward identity. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma abs_crossCoordinateProduct_le {N : ℕ} (i j : Fin N)
    (U : Orthogonal N) (σ τ : Spin N) :
    |spinCoordinate U σ i * spinCoordinate U τ j| ≤ N := by
  have hi := spinCoordinate_sq_le U σ i
  have hj := spinCoordinate_sq_le U τ j
  rw [abs_mul]
  nlinarith [sq_nonneg (|spinCoordinate U σ i| - |spinCoordinate U τ j|),
    sq_abs (spinCoordinate U σ i), sq_abs (spinCoordinate U τ j)]

def offCoordinateProduct {N : ℕ} (i j : Fin N) (F : Spin N → Spin N → ℝ)
    (U : Orthogonal N) (x : Spin N × Spin N) : ℝ :=
  spinCoordinate U x.1 i * spinCoordinate U x.2 j * F x.1 x.2

def offCoordinateVariation {N : ℕ} (i j : Fin N) (F : Spin N → Spin N → ℝ)
    (U : Orthogonal N) (x : Spin N × Spin N) : ℝ :=
  (spinCoordinate U x.1 j * spinCoordinate U x.2 j -
    spinCoordinate U x.1 i * spinCoordinate U x.2 i) * F x.1 x.2

lemma hasDerivAt_offCoordinateProduct {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (F : Spin N → Spin N → ℝ) (U : Orthogonal N) (x : Spin N × Spin N) (t : ℝ) :
    HasDerivAt (fun s => offCoordinateProduct i j F (planeRotation i j s * U) x)
      (offCoordinateVariation i j F (planeRotation i j t * U) x) t := by
  have hd := ((hasDerivAt_planeRotation_coordinate i j i U (spinVector x.1) t).mul
    (hasDerivAt_planeRotation_coordinate i j j U (spinVector x.2) t)).mul_const (F x.1 x.2)
  convert hd using 1
  · rfl
  · simp only [offCoordinateVariation, spinCoordinate, ite_true, hij, Ne.symm hij,
      ite_false, sub_zero, zero_sub]
    ring

/-- Exact finite off-diagonal rotation identity. The spin test is fixed during
rotation; in the main application it is a function of the rotation-invariant
total overlap. Arbitrary deterministic nonzero positive priors are allowed. -/
theorem offDiagonal_coordinate_ward_identity {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ σ τ, |F σ τ| ≤ B) :
    (∫ U,
      gibbsPairAverage w (orbitHamiltonian eig c U)
        (fun σ τ => (spinCoordinate U σ j * spinCoordinate U τ j -
          spinCoordinate U σ i * spinCoordinate U τ i) * F σ τ) +
      (eig i - eig j) *
        (gibbsPairAverage w (orbitHamiltonian eig c U)
          (fun σ τ => spinCoordinate U σ i * spinCoordinate U τ j * F σ τ *
            (coordinateProduct i j U σ + coordinateProduct i j U τ)) -
          2 * gibbsPairAverage w (orbitHamiltonian eig c U)
            (fun σ τ => spinCoordinate U σ i * spinCoordinate U τ j * F σ τ) *
            gibbsAverage w (orbitHamiltonian eig c U) (coordinateProduct i j U)) ∂μ) = 0 := by
  let R := planeRotation i j
  let H : Orthogonal N → Spin N × Spin N → ℝ := fun U x =>
    orbitHamiltonian eig c U x.1 + orbitHamiltonian eig c U x.2
  let A := offCoordinateProduct i j F
  let dH : ℝ → Orthogonal N → Spin N × Spin N → ℝ := fun t U x =>
    (eig i - eig j) * (coordinateProduct i j (R t * U) x.1 +
      coordinateProduct i j (R t * U) x.2)
  let dA : ℝ → Orthogonal N → Spin N × Spin N → ℝ := fun t U =>
    offCoordinateVariation i j F (R t * U)
  have hR : R 0 = 1 := planeRotation_zero i j
  have hP (σ : Spin N) : Measurable (fun U : Orthogonal N => coordinateProduct i j U σ) :=
    (measurable_spinCoordinate σ i).mul (measurable_spinCoordinate σ j)
  have hAm (x : Spin N × Spin N) : Measurable (fun U : Orthogonal N => A U x) :=
    ((measurable_spinCoordinate x.1 i).mul (measurable_spinCoordinate x.2 j)).mul_const _
  have hHm (x : Spin N × Spin N) : Measurable (fun U => H U x) :=
    (measurable_orbitHamiltonian eig c x.1).add (measurable_orbitHamiltonian eig c x.2)
  have hdHm (x : Spin N × Spin N) : Measurable (fun U => dH 0 U x) := by
    simp only [dH, hR, one_mul]
    exact ((hP x.1).add (hP x.2)).const_mul _
  have hdAm (x : Spin N × Spin N) : Measurable (fun U => dA 0 U x) := by
    simp only [dA, hR, one_mul, offCoordinateVariation]
    exact (((measurable_spinCoordinate x.1 j).mul (measurable_spinCoordinate x.2 j)).sub
      ((measurable_spinCoordinate x.1 i).mul (measurable_spinCoordinate x.2 i))).mul_const _
  have hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x,
      HasDerivAt (fun s => H (R s * U) x) (dH t U x) t := by
    intro U t _ x
    have h1 := (hasDerivAt_planeRotation_energy i j U eig x.1 t).add_const (fieldEnergy c x.1)
    have h2 := (hasDerivAt_planeRotation_energy i j U eig x.2 t).add_const (fieldEnergy c x.2)
    convert h1.add h2 using 1
    · rfl
    · dsimp only [dH, R, coordinateProduct, spinCoordinate]
      ring
  have hAd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x,
      HasDerivAt (fun s => A (R s * U) x) (dA t U x) t := by
    intro U t _ x
    exact hasDerivAt_offCoordinateProduct i j hij F U x t
  have hAb : ∀ U x, |A U x| ≤ N * B := by
    intro U x
    rw [show A U x = spinCoordinate U x.1 i * spinCoordinate U x.2 j * F x.1 x.2 from rfl,
      abs_mul]
    exact mul_le_mul (abs_crossCoordinateProduct_le i j U x.1 x.2) (hF x.1 x.2)
      (abs_nonneg _) (Nat.cast_nonneg _)
  have hHb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x,
      |dH t U x| ≤ |eig i - eig j| * (2 * N) := by
    intro U t _ x
    dsimp only [dH]
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hs := (abs_add_le _ _).trans (add_le_add
      (abs_coordinateProduct_le i j (R t * U) x.1)
      (abs_coordinateProduct_le i j (R t * U) x.2))
    linarith
  have hAdb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x, |dA t U x| ≤ 2 * N * B := by
    intro U t _ x
    dsimp only [dA, offCoordinateVariation]
    rw [abs_mul]
    apply mul_le_mul _ (hF x.1 x.2) (abs_nonneg _) (by positivity)
    have hs := (abs_sub _ _).trans (add_le_add
      (abs_crossCoordinateProduct_le j j (R t * U) x.1 x.2)
      (abs_crossCoordinateProduct_le i i (R t * U) x.1 x.2))
    linarith
  have hwrd := integral_gibbs_rotation_identity μ R hR (GibbsReference_pair hw)
    H A hHm hAm dH dA hdHm hdAm hHd hAd
    (N * B) (|eig i - eig j| * (2 * N)) (2 * N * B) (by positivity) hAb hHb hAdb
  simp only [dH, dA, H, A, hR, one_mul, offCoordinateProduct] at hwrd
  convert hwrd using 1
  congr 1
  funext U
  unfold offCoordinateVariation offCoordinateProduct
  rw [gibbsAverage_pair w (orbitHamiltonian eig c U)
    (fun σ τ => (spinCoordinate U σ j * spinCoordinate U τ j -
      spinCoordinate U σ i * spinCoordinate U τ i) * F σ τ)]
  have hfactor : (fun x : Spin N × Spin N =>
      spinCoordinate U x.1 i * spinCoordinate U x.2 j * F x.1 x.2 *
        ((eig i - eig j) * (coordinateProduct i j U x.1 + coordinateProduct i j U x.2))) =
      (fun x => (eig i - eig j) *
        (spinCoordinate U x.1 i * spinCoordinate U x.2 j * F x.1 x.2 *
          (coordinateProduct i j U x.1 + coordinateProduct i j U x.2))) := by
    funext x
    ring
  rw [hfactor, gibbsAverage_const_mul, gibbsAverage_const_mul,
    gibbsAverage_pair_sum hw]
  rw [gibbsAverage_pair w (orbitHamiltonian eig c U)
    (fun σ τ => spinCoordinate U σ i * spinCoordinate U τ j * F σ τ *
      (coordinateProduct i j U σ + coordinateProduct i j U τ)),
    gibbsAverage_pair w (orbitHamiltonian eig c U)
      (fun σ τ => spinCoordinate U σ i * spinCoordinate U τ j * F σ τ)]
  ring

end InvariantIsing

end

end OAI
