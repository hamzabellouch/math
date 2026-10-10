import OAI.Probability.InvariantIsing.Cavity.CavityGeometricTail

namespace OAI

/-! Tightness of the actual full-model special coordinates.  The only
compression input is a good event whose probability tends to one. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_tightness_of_square_tail (tail : ℕ → ℝ → ℝ) (error : ℕ → ℝ)
    {C : ℝ} (he : Tendsto error atTop (𝓝 0))
    (hb : ∀ k R, 0 < R → tail k R ≤ error k + C / R ^ 2) :
    ∀ ε > 0, ∃ R > 0, ∀ᶠ k in atTop, tail k R < ε := by
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_gt (max 1 (2 * C / ε))
  have hr1 : (1 : ℝ) < r := (le_max_left _ _).trans_lt hr
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr1
  have hrC : 2 * C / ε < (r : ℝ) := (le_max_right _ _).trans_lt hr
  have hCr : C / (r : ℝ) ^ 2 < ε / 2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hr0)).mpr
    have hmul : 2 * C < (r : ℝ) * ε := (div_lt_iff₀ hε).mp hrC
    have hsq : (r : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq hε.le]
  refine ⟨r, hr0, ?_⟩
  filter_upwards [he.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))] with k hk
  exact (hb k r hr0).trans_lt (by linarith)

theorem cavity_full_special_tightness {n m d depth : ℕ}
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k + n)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k + n)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (T : ℕ → LabeledTree depth) (eig : (k : ℕ) → Fin (N k + n) → ℝ)
    (g : (k : ℕ) → Fin (N k + n) → Fin m)
    (u : ℕ → ℕ → ℝ) (hu : ∀ k j, |u k j| ≤ 2)
    (B : (k : ℕ) → SpecialOrthogonal (N k + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hmB : ∀ k, Measurable (B k))
    (hB : ∀ k U, (B k U).transpose * B k U = 1)
    (good : (k : ℕ) → Set (SpecialOrthogonal (N k + n)))
    (hgood : ∀ k, MeasurableSet (good k))
    (hp : Tendsto (fun k => (μ k).real (good k)) atTop (𝓝 1))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ k U, U ∈ good k → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g k) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L) :
    ∀ ε > 0, ∃ R > 0, ∀ᶠ k in atTop,
      cavityFullDisorderTest (μ k) (T k) (eig k) (cavitySpectralGroup (g k)) (u k)
        (fun U σ => if R < ‖cavityFullSpecialCoordinates (g k) (B k U) U (σ 0).1‖
          then 1 else 0) < ε := by
  have he : Tendsto (fun k => (μ k).real (good k)ᶜ) atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp
    simpa only [measureReal_compl (hgood _), probReal_univ, sub_self] using ht
  exact cavity_tightness_of_square_tail _ _ he
    (fun k R hR => cavity_full_geometric_tail (hN k) (μ k) (T k) (eig k) (g k)
      (u k) (hu k) (B k) (hmB k) (hB k) (good k) (hgood k) hL hR (hbound k))

end InvariantIsing

end

end OAI
