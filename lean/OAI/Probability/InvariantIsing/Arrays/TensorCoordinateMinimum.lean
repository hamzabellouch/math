import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFrozenFluctuation
import OAI.Probability.InvariantIsing.Spectral.SpectralGG
import OAI.Probability.InvariantIsing.Pressure.PressureCoordinateMinimum

namespace OAI

/-! Actual finite tensor coordinates at a penalized pressure minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma tensorFrozenCGF_mean_bounds {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ) :
    let Q := (tensorFrozenLaw μ n b j).prod gaussianCoordinates
    0 ≤ (∫ p, tensorFrozenCGF eig c I degree amplitude n r h j t p ∂Q) ∧
      (∫ p, tensorFrozenCGF eig c I degree amplitude n r h j t p ∂Q) ≤ t ^ 2 / 2 := by
  let U : TensorFrozenData N n j → SpecialOrthogonal N := fun ω => ω.1.1
  have hU : Measurable U := measurable_fst.fst
  have hb := randomCoefficient_cgf_mean_bounds
    (P := tensorFrozenLaw μ n b j) (measurable_tensorFrozenReference eig c I degree amplitude n r h j)
    (spectralPerturbationCoefficients U I (degree j) n (r j))
    (measurable_spectralPerturbationFields U hU I (degree j) n (r j))
    (fun ω x => jointSpectralMonomialCoefficients_variance_le_one
      (specialRotation (U ω)) I (degree j) n (r j) x) t
  simpa only [tensorFrozenCGF, spectralPerturbationCoefficients, U, mul_one] using hb

/-- The coordinate pressure is the actual root/cascade pressure averaged
over the rotation, with precisely one Gaussian amplitude replaced. -/
def tensorGaussianCoordinatePressure {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (amplitude : Fin N → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin N → ℕ) (h : ℕ → ℝ) (j : Fin N) (w : ℝ) : ℝ :=
  ∫ p, tensorDisorderPressure eig c I degree
    (Function.update amplitude j (perturbationAmplitude N j * w)) n p
    ∂(μ.prod (tensorRootTreeLaw I degree n b
      (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0)))

/-- Applying the proved frozen-Gaussian mean estimate to the actual
coordinate pressure requires only its already established second moments. -/
lemma tensorGaussianCoordinatePressure_cost {N m : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (amplitude : Fin N → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin N → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hb : CascadeExponents n b) (j : Fin N) (w : ℝ)
    (hF : ∀ a : ℝ, a = perturbationAmplitude N j * w ∨ a = 0 →
      MemLp (tensorDisorderPressure eig c I degree (Function.update amplitude j a) n) 2
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0)))) :
    let M := tensorGaussianCoordinatePressure μ eig c I degree amplitude n b r h j
    0 ≤ M w - M 0 ∧ M w - M 0 ≤ (perturbationAmplitude N j * w) ^ 2 / (2 * N) := by
  intro M
  have hm := tensorFrozenCGF_mean hN μ eig c I degree amplitude n b r h hh h0 hb j
    (perturbationAmplitude N j * w) hF
  have hc := tensorFrozenCGF_mean_bounds μ eig c I degree amplitude n b r h j
    (perturbationAmplitude N j * w)
  have he : (∫ p, tensorFrozenCGF eig c I degree amplitude n r h j
      (perturbationAmplitude N j * w) p ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates) =
      (N : ℝ) * (M w - M 0) := by
    simpa only [M, tensorGaussianCoordinatePressure, mul_zero] using hm
  dsimp only at hc
  rw [he] at hc
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨(mul_nonneg_iff_of_pos_left hn).mp hc.1, ?_⟩
  apply (le_div_iff₀ (show 0 < 2 * (N : ℝ) by positivity)).mpr
  nlinarith [hc.2]

/-- At a deterministic minimum of the actual Gaussian coordinate, its
Gibbs energy concentrates around the derivative of the quadratic penalty. -/
theorem tensorGaussianCoordinate_energy_at_minimum {N m : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (amplitude : Fin N → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin N → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hb : CascadeExponents n b) (j : Fin N)
    (w s K B : ℝ) (hw : w ∈ Set.Icc (1 : ℝ) 2)
    (he : perturbationScale N ≤ 1 / 8) (hs : 0 < s) (hs' : s ≤ 1 / 4) (hK : 0 < K)
    (hF : ∀ v : ℝ, |v| ≤ 2 →
      MemLp (tensorDisorderPressure eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j * v)) n) 2
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))))
    (hv : ∀ v : ℝ, |v| ≤ 2 →
      variance (tensorDisorderPressure eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j * v)) n)
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) ≤ B)
    (hmin : ∀ v ∈ Set.Icc (1 : ℝ) 2,
      -tensorGaussianCoordinatePressure μ eig c I degree amplitude n b r h j w +
        perturbationWeight j * (w - 3 / 2) ^ 2 ≤
      -tensorGaussianCoordinatePressure μ eig c I degree amplitude n b r h j v +
        perturbationWeight j * (v - 3 / 2) ^ 2) :
    let a := perturbationAmplitude N j
    let c₀ := N * perturbationWeight j / a ^ 2
    let Q := (tensorFrozenLaw μ n b j).prod gaussianCoordinates
    let A := fun ω : TensorFrozenData N n j =>
      jointSpectralMonomialCoefficients (specialRotation ω.1.1) I (degree j) n (r j)
    let ν := tensorFrozenReference eig c I degree amplitude n r h j
    let E := fun p : TensorFrozenData N n j × (ℕ → ℝ) => ∫ x,
      |cylinderField (A p.1 x) p.2 - 2 * c₀ * (a * w - a * (3 / 2))|
        ∂(ν p.1).tilted (fun x => a * w * cylinderField (A p.1 x) p.2)
    Integrable E Q ∧ (∫ p, E p ∂Q) ≤
      (2 * c₀ + K ^ 2) / (2 * K) + c₀ * (a * s) + 4 * (2 * N * Real.sqrt B) / (a * s) := by
  intro a c₀ Q A ν E
  let M := tensorGaussianCoordinatePressure μ eig c I degree amplitude n b r h j
  let L := fun t => ∫ p, tensorFrozenCGF eig c I degree amplitude n r h j t p ∂Q
  have ha : 0 < a := perturbationAmplitude_pos hN j
  have hwa : |w| ≤ 2 := abs_le.mpr ⟨by linarith [hw.1], hw.2⟩
  have hFa (v : ℝ) (hva : |v| ≤ 2) : ∀ t : ℝ, t = a * v ∨ t = 0 →
      MemLp (tensorDisorderPressure eig c I degree (Function.update amplitude j t) n) 2
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) := by
    intro t ht
    rcases ht with rfl | rfl
    · exact hF v hva
    · simpa only [mul_zero] using hF 0 (by norm_num)
  have hmean (v : ℝ) (hva : |v| ≤ 2) : L (a * v) = N * (M v - M 0) := by
    simpa only [L, M, Q, tensorGaussianCoordinatePressure, mul_zero] using
      tensorFrozenCGF_mean hN μ eig c I degree amplitude n b r h hh h0 hb j (a * v) (hFa v hva)
  have hc₀ := tensorGaussianCoordinatePressure_cost hN μ eig c I degree amplitude n b r h hh h0 hb j
    (3 / 2) (hFa (3 / 2) (by norm_num))
  have hcw := tensorGaussianCoordinatePressure_cost hN μ eig c I degree amplitude n b r h hh h0 hb j
    w (hFa w hwa)
  have hpen := gaussianCoordinate_minimum_penalty hN j M w hwa ⟨hc₀.1, hcw.2⟩
    (hmin (3 / 2) (by constructor <;> norm_num))
  obtain ⟨hlo, hhi⟩ := gaussianCoordinate_minimum_interior j hpen he hs'
  have hlocal := pressureCoordinate_minimum_rescale (Nat.cast_nonneg N) ha hw hlo hhi
    (fun v hv => hmean v (abs_le.mpr ⟨by linarith [hv.1], hv.2⟩)) hmin
  have hconc (t : ℝ) (ht : t ∈ ({a * w - a * s, a * w, a * w + a * s} : Set ℝ)) :
      (∫ p, |tensorFrozenCGF eig c I degree amplitude n r h j t p - L t| ∂Q) ≤
        2 * N * Real.sqrt B := by
    have hti : t ∈ Set.Icc (a * w - a * s) (a * w + a * s) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl <;> constructor <;> nlinarith [mul_pos ha hs]
    have htv : t / a ∈ Set.Icc (1 : ℝ) 2 := by
      constructor
      · apply (le_div_iff₀ ha).mpr
        nlinarith [hti.1]
      · apply (div_le_iff₀ ha).mpr
        nlinarith [hti.2]
    have hta : |t / a| ≤ 2 := abs_le.mpr ⟨by linarith [htv.1], htv.2⟩
    have htF : ∀ q : ℝ, q = t ∨ q = 0 →
        MemLp (tensorDisorderPressure eig c I degree (Function.update amplitude j q) n) 2
          (μ.prod (tensorRootTreeLaw I degree n b
            (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) := by
      simpa only [mul_div_cancel₀ _ ha.ne'] using hFa (t / a) hta
    have htV : ∀ q : ℝ, q = t ∨ q = 0 →
        variance (tensorDisorderPressure eig c I degree (Function.update amplitude j q) n)
          (μ.prod (tensorRootTreeLaw I degree n b
            (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) ≤ B := by
      intro q hq
      rcases hq with hq | hq
      · rw [hq]
        simpa only [a, mul_div_cancel₀ _ ha.ne'] using hv (t / a) hta
      · rw [hq]
        simpa only [mul_zero] using hv 0 (by norm_num)
    exact (tensorFrozenCGF_centered_L1_bound hN μ eig c I degree amplitude n b r h hh h0 hb j
      t B htF htV).2
  exact randomCoefficient_energy_at_minimum
    (P := tensorFrozenLaw μ n b j) (measurable_tensorFrozenReference eig c I degree amplitude n r h j) A
    (measurable_spectralPerturbationFields (fun ω : TensorFrozenData N n j => ω.1.1)
      measurable_fst.fst I (degree j) n (r j))
    (fun ω x => jointSpectralMonomialCoefficients_variance_le_one (specialRotation ω.1.1)
      I (degree j) n (r j) x) (mul_pos ha hs) hK hlocal hconc

end InvariantIsing

end

end OAI
