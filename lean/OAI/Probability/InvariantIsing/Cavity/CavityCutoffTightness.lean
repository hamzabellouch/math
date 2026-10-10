import OAI.Probability.InvariantIsing.Cavity.CavityFullCutoff

namespace OAI

/-! Removing the actual special-coordinate cutoff from bounded tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavitySpecialCutoff {N n m d depth : ℕ} (g : Fin (N + n) → Fin m)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (R : ℝ) (U : SpecialOrthogonal (N + n)) : Set (Spin (N + n) × LabeledLeaf depth) :=
  {x | ‖cavityFullSpecialCoordinates g (B U) U x.1‖ ≤ R}

lemma measurableSet_cavitySpecialCutoff {N n m d depth : ℕ}
    (g : Fin (N + n) → Fin m)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : Measurable B) (R : ℝ) :
    MeasurableSet {p : SpecialOrthogonal (N + n) × (Spin (N + n) × LabeledLeaf depth) |
      p.2 ∈ cavitySpecialCutoff g B R p.1} := by
  have hm : Measurable (fun p : SpecialOrthogonal (N + n) ×
      (Spin (N + n) × LabeledLeaf depth) =>
      cavityFullSpecialCoordinates g (B p.1) p.1 p.2.1) := by
    apply measurable_from_prod_countable_left
    intro x
    exact measurable_cavityFullSpecialCoordinates g B hB x.1
  exact measurableSet_le hm.norm measurable_const

theorem cavity_full_special_cutoff_error {N n m d depth : ℕ}
    (μ : Measure (SpecialOrthogonal (N + n))) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin (N + n) → ℝ) (g : Fin (N + n) → Fin m)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hmB : Measurable B) (R : ℝ)
    (F : SpecialOrthogonal (N + n) → (Fin 2 → Spin (N + n) × LabeledLeaf depth) → ℝ)
    (hmF : Measurable (Function.uncurry F))
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ U σ, |F U σ| ≤ M) :
    |cavityFullCutoffDisorderTest μ T eig (cavitySpectralGroup g) u
        (cavitySpecialCutoff g B R) F - cavityFullDisorderTest μ T eig (cavitySpectralGroup g) u F| ≤
      4 * M * cavityFullDisorderTest μ T eig (cavitySpectralGroup g) u
        (fun U σ => if R < ‖cavityFullSpecialCoordinates g (B U) U (σ 0).1‖ then 1 else 0) := by
  simpa only [cavitySpecialCutoff, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] using
    cavity_full_cutoff_error μ T eig (cavitySpectralGroup g) u hu
      (cavitySpecialCutoff g B R) (measurableSet_cavitySpecialCutoff g B hmB R) F hmF hM hF

theorem cavity_full_special_cutoff_tightness {n m d depth : ℕ}
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k + n)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k + n)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (T : ℕ → LabeledTree depth) (eig : (k : ℕ) → Fin (N k + n) → ℝ)
    (g : (k : ℕ) → Fin (N k + n) → Fin m)
    (u : ℕ → ℕ → ℝ) (hu : ∀ k j, |u k j| ≤ 2)
    (B : (k : ℕ) → SpecialOrthogonal (N k + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hmB : ∀ k, Measurable (B k)) (hB : ∀ k U, (B k U).transpose * B k U = 1)
    (good : (k : ℕ) → Set (SpecialOrthogonal (N k + n)))
    (hgood : ∀ k, MeasurableSet (good k))
    (hp : Tendsto (fun k => (μ k).real (good k)) atTop (𝓝 1))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ k U, U ∈ good k → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g k) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
    (F : (k : ℕ) → SpecialOrthogonal (N k + n) →
      (Fin 2 → Spin (N k + n) × LabeledLeaf depth) → ℝ)
    (hmF : ∀ k, Measurable (Function.uncurry (F k)))
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ k U σ, |F k U σ| ≤ M) :
    ∀ ε > 0, ∃ R > 0, ∀ᶠ k in atTop,
      |cavityFullCutoffDisorderTest (μ k) (T k) (eig k) (cavitySpectralGroup (g k)) (u k)
          (cavitySpecialCutoff (g k) (B k) R) (F k) -
        cavityFullDisorderTest (μ k) (T k) (eig k) (cavitySpectralGroup (g k)) (u k) (F k)| < ε := by
  intro ε hε
  have hden : 0 < 4 * M + 1 := by positivity
  obtain ⟨R, hR, ht⟩ := cavity_full_special_tightness N hN μ T eig g u hu B hmB hB
    good hgood hp hL hbound (ε / (4 * M + 1)) (div_pos hε hden)
  refine ⟨R, hR, ?_⟩
  filter_upwards [ht] with k hk
  apply (cavity_full_special_cutoff_error (μ k) (T k) (eig k) (g k) (u k) (hu k)
    (B k) (hmB k) R (F k) (hmF k) hM (hF k)).trans_lt
  have hη : 0 < ε / (4 * M + 1) := div_pos hε hden
  have hmul := mul_le_mul_of_nonneg_left hk.le (show 0 ≤ 4 * M by positivity)
  have hid : (4 * M + 1) * (ε / (4 * M + 1)) = ε := mul_div_cancel₀ ε hden.ne'
  nlinarith

end InvariantIsing

end

end OAI
