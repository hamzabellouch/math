import OAI.Probability.InvariantIsing.Cavity.CavityTreeFullRegular
import OAI.Probability.InvariantIsing.Cavity.CavityFullCutoffSequence

namespace OAI

/-! Removal of the original special-coordinate cutoff after averaging
over the actual random tree, uniformly in its depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_full_tree_cutoff_sequence {n m d : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ k, 0 < N k + n)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k + n)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (θ : (k : ℕ) → Measure (LabeledTree (depth k))) [∀ k, IsProbabilityMeasure (θ k)]
    (eig : (k : ℕ) → Fin (N k + n) → ℝ)
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
    (F : (k : ℕ) → (Fin 2 → Spin (N k + n) × LabeledLeaf (depth k)) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ k σ, |F k σ| ≤ M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ k in atTop,
      |(∫ T, cavityFullTest (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k) (F k) ∂θ k) -
        ∫ T, cavityFullCutoffDisorderTest (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k)
          (cavitySpecialCutoff (g k) (B k) (b j)) (fun _ => F k) ∂θ k| < ε := by
  have he : Tendsto (fun k => (μ k).real (good k)ᶜ) atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp
    simpa only [measureReal_compl (hgood _),probReal_univ,sub_self] using ht
  have hscaled : Tendsto (fun k => 4*M*(μ k).real (good k)ᶜ) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (4*M)
  have hinv := tendsto_inv_atTop_zero.comp hblim
  have hrad : Tendsto (fun j => 4*M*L^2*((m:ℝ)*n)/(b j)^2) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,div_eq_mul_inv,inv_pow,zero_pow (by decide : 2 ≠ 0),mul_zero]
      using (hinv.pow 2).const_mul (4*M*L^2*((m:ℝ)*n))
  intro ε hε
  filter_upwards [hrad.eventually (Iio_mem_nhds (show (0:ℝ) < ε/2 by positivity))] with j hj
  filter_upwards [hscaled.eventually (Iio_mem_nhds (show (0:ℝ) < ε/2 by positivity))] with k hk
  let O := fun T : LabeledTree (depth k) =>
    cavityFullTest (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k) (F k)
  let C := fun T : LabeledTree (depth k) =>
    cavityFullCutoffDisorderTest (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k)
      (cavitySpecialCutoff (g k) (B k) (b j)) (fun _ => F k)
  have hmF : Measurable (Function.uncurry (fun _ : SpecialOrthogonal (N k+n) => F k)) :=
    (measurable_of_countable (F k)).comp measurable_snd
  have hOm : Measurable O := measurable_cavityFullTest_tree _ _ _ _ _
  have hCm : Measurable C := measurable_cavityFullCutoffDisorderTest_tree _ _ _ _ _
    (measurableSet_cavitySpecialCutoff (g k) (B k) (hmB k) (b j)) _ hmF
  have hOi : Integrable O (θ k) := integrable_of_measurable_abs_le hOm (fun T =>
    cavityFullDisorderTest_abs_le (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k)
      (fun _ => F k) hmF hM (fun _ => hF k))
  have hCi : Integrable C (θ k) := integrable_of_measurable_abs_le hCm (fun T =>
    cavityFullCutoffDisorderTest_abs_le (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k)
      _ _ hM (fun _ => hF k))
  have hbound T : |O T-C T| ≤
      (4*M)*(μ k).real (good k)ᶜ + 4*M*L^2*((m:ℝ)*n)/(b j)^2 := by
    have hcut := cavity_full_special_cutoff_error (μ k) T (eig k) (g k) (u k)
      (hu k) (B k) (hmB k) (b j) (fun _ => F k) hmF hM (fun _ => hF k)
    rw [abs_sub_comm] at hcut
    have htail := cavity_full_geometric_tail (hN k) (μ k) T (eig k) (g k)
      (u k) (hu k) (B k) (hmB k) (hB k) (good k) (hgood k) hL (hb j) (hbound k)
    have hmul := mul_le_mul_of_nonneg_left htail (show 0 ≤ 4*M by positivity)
    have heq : 4*M*((μ k).real (good k)ᶜ + L^2*((m:ℝ)*n)/(b j)^2) =
        (4*M)*(μ k).real (good k)ᶜ + 4*M*L^2*((m:ℝ)*n)/(b j)^2 := by ring
    rw [heq] at hmul
    exact hcut.trans hmul
  change |(∫ T, O T ∂θ k)-(∫ T, C T ∂θ k)| < ε
  rw [← integral_sub hOi hCi]
  have hh := norm_integral_le_of_norm_le_const (μ := θ k) (f := fun T => O T-C T)
    (C := (4*M)*(μ k).real (good k)ᶜ + 4*M*L^2*((m:ℝ)*n)/(b j)^2)
    (ae_of_all _ fun T => by simpa only [Real.norm_eq_abs] using hbound T)
  have hh' : |∫ T, O T-C T ∂θ k| ≤
      (4*M)*(μ k).real (good k)ᶜ + 4*M*L^2*((m:ℝ)*n)/(b j)^2 := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh
  exact hh'.trans_lt (by linarith)

end InvariantIsing

end

end OAI
