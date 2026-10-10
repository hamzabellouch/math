import OAI.Probability.InvariantIsing.Cavity.CavityCutoffTightness

namespace OAI

/-! Uniform removal of the physical cutoff along any divergent sequence
of radii, allowing the labeled-tree depth to vary with system size. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_full_cutoff_sequence {n m d : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ k, 0 < N k + n)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k + n)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (T : (k : ℕ) → LabeledTree (depth k)) (eig : (k : ℕ) → Fin (N k + n) → ℝ)
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
      (Fin 2 → Spin (N k + n) × LabeledLeaf (depth k)) → ℝ)
    (hmF : ∀ k, Measurable (Function.uncurry (F k)))
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ k U σ, |F k U σ| ≤ M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ k in atTop,
      |cavityFullDisorderTest (μ k) (T k) (eig k) (cavitySpectralGroup (g k)) (u k) (F k) -
        cavityFullCutoffDisorderTest (μ k) (T k) (eig k) (cavitySpectralGroup (g k)) (u k)
          (cavitySpecialCutoff (g k) (B k) (b j)) (F k)| < ε := by
  have he : Tendsto (fun k => (μ k).real (good k)ᶜ) atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp
    simpa only [measureReal_compl (hgood _), probReal_univ, sub_self] using ht
  have hscaled : Tendsto (fun k => 4*M*(μ k).real (good k)ᶜ) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (4*M)
  have hinv := tendsto_inv_atTop_zero.comp hblim
  have hrad : Tendsto (fun j => 4*M*L^2*((m:ℝ)*n)/(b j)^2) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0), mul_zero]
      using (hinv.pow 2).const_mul (4*M*L^2*((m:ℝ)*n))
  intro ε hε
  filter_upwards [hrad.eventually (Iio_mem_nhds (show (0:ℝ) < ε/2 by positivity))] with j hj
  filter_upwards [hscaled.eventually (Iio_mem_nhds (show (0:ℝ) < ε/2 by positivity))] with k hk
  have hcut := cavity_full_special_cutoff_error (μ k) (T k) (eig k) (g k) (u k)
    (hu k) (B k) (hmB k) (b j) (F k) (hmF k) hM (hF k)
  rw [abs_sub_comm] at hcut
  have htail := cavity_full_geometric_tail (hN k) (μ k) (T k) (eig k) (g k)
    (u k) (hu k) (B k) (hmB k) (hB k) (good k) (hgood k) hL (hb j) (hbound k)
  have hmul := mul_le_mul_of_nonneg_left htail (show 0 ≤ 4*M by positivity)
  have heq : 4*M*((μ k).real (good k)ᶜ + L^2*((m:ℝ)*n)/(b j)^2) =
      (4*M)*(μ k).real (good k)ᶜ + 4*M*L^2*((m:ℝ)*n)/(b j)^2 := by ring
  rw [heq] at hmul
  exact (hcut.trans hmul).trans_lt (by linarith)

end InvariantIsing

end

end OAI
