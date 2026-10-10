import OAI.Probability.InvariantIsing.Arrays.TensorCoordinateMinimum
import OAI.Probability.InvariantIsing.Arrays.TensorFiniteGG

namespace OAI

/-! GG error rates at actual finite Gaussian-coordinate pressure minima. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem tensorGaussianGG_at_minimum {N m q : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (amplitude : Fin N → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin N → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hb : CascadeExponents n b) (j : Fin N)
    (w L : ℝ) (hw : w ∈ Set.Icc (1 : ℝ) 2)
    (he : perturbationScale N ≤ 1 / 8) (hs : contactStep N ≤ 1 / 4)
    (hamp : amplitude j = perturbationAmplitude N j * w)
    (hF : ∀ v : ℝ, |v| ≤ 2 →
      MemLp (tensorDisorderPressure eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j * v)) n) 2
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))))
    (hv : ∀ v : ℝ, |v| ≤ 2 →
      variance (tensorDisorderPressure eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j * v)) n)
        (μ.prod (tensorRootTreeLaw I degree n b
          (fun i => tensorPathProfile I degree n r h (i + 1)) (tensorPathProfile I degree n r h 0))) ≤ L / N)
    (hmin : ∀ v ∈ Set.Icc (1 : ℝ) 2,
      -tensorGaussianCoordinatePressure μ eig c I degree amplitude n b r h j w +
        perturbationWeight j * (w - 3 / 2) ^ 2 ≤
      -tensorGaussianCoordinatePressure μ eig c I degree amplitude n b r h j v +
        perturbationWeight j * (v - 3 / 2) ^ 2)
    (C : ℝ) (hC : 0 ≤ C)
    (D : SpecialOrthogonal N → (Fin (q + 1) → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) (hDb : ∀ U σ, |D U σ| ≤ C)
    (center δ : Fin m → ℝ)
    (hδ : ∀ a, tensorNamespacedObservableAverage μ eig c I degree amplitude n b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center a|) ≤ δ a) :
    |tensorSpectralGGResidual μ eig c I degree amplitude n b r h j D| ≤
      contactGGRate N j L C + 2 * C * ∑ a, (degree j a : ℝ) * δ a := by
  let a := perturbationAmplitude N j
  let c₀ := N * perturbationWeight j / a ^ 2
  let θ := 1 / perturbationScale N
  let G := (2 * c₀ + θ ^ 2) / (2 * θ) + c₀ * (a * contactStep N) +
    4 * (2 * N * Real.sqrt (L / N)) / (a * contactStep N)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he' : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs' : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have hθ : 0 < θ := one_div_pos.mpr he'
  have ha : 0 < a := perturbationAmplitude_pos hN j
  have hc₀ : 0 < c₀ := div_pos (mul_pos hn (perturbationWeight_pos j)) (sq_pos_of_pos ha)
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hE := tensorGaussianCoordinate_energy_at_minimum hN μ eig c I degree amplitude n b r h hh h0 hb j
    w (contactStep N) θ (L / N) hw he hs' hs hθ hF hv hmin
  have hamp' : 0 < |amplitude j| := by
    rw [hamp, abs_mul, abs_of_pos ha]
    exact mul_pos ha (abs_pos.mpr (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hw.1)))
  have hEa :
      let A := spectralPerturbationCoefficients (fun ω : TensorFrozenData N n j => ω.1.1)
        I (degree j) n (r j)
      let ν := tensorFrozenReference eig c I degree amplitude n r h j
      let E := fun p : TensorFrozenData N n j × (ℕ → ℝ) => ∫ x,
        |cylinderField (A p.1 x) p.2 - 2 * c₀ * (a * w - a * (3 / 2))|
        ∂(ν p.1).tilted (fun x => amplitude j * cylinderField (A p.1 x) p.2)
      Integrable E ((tensorFrozenLaw μ n b j).prod gaussianCoordinates) ∧
        (∫ p, E p ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates) ≤ G := by
    simpa only [hamp, spectralPerturbationCoefficients, a, c₀, G] using hE
  have hgg := tensorFiniteGG_individualDiagonal_bound μ eig c I degree amplitude n b r h hh h0 j
    (2 * c₀ * (a * w - a * (3 / 2))) G C hC hamp' D hD hDb center δ hδ hEa
  have hampl : a ≤ |amplitude j| := by
    rw [hamp, abs_mul, abs_of_pos ha, abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hw.1)]
    nlinarith [hw.1]
  calc
    _ ≤ 2 * C * (G / |amplitude j| + ∑ a, (degree j a : ℝ) * δ a) := hgg
    _ ≤ 2 * C * (G / a + ∑ a, (degree j a : ℝ) * δ a) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (div_le_div_of_nonneg_left hG ha hampl) le_rfl) (mul_nonneg (by norm_num) hC)
    _ = _ := by unfold contactGGRate; dsimp only [G, c₀, θ, a]; ring

end InvariantIsing

end

end OAI
