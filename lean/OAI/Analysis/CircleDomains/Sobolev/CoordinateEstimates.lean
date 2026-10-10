import OAI.Analysis.CircleDomains.Sobolev.OriginalDomainMetric
import OAI.Analysis.CircleDomains.Sobolev.SmoothFiniteTransfer
import OAI.Analysis.CircleDomains.Sobolev.EnergyLocalization

namespace OAI

/-!
# Actual coordinate energies on the completed surface

The metric trace estimate controls the sum of the actual scalar
coordinate energies. Exact agreement near the retained core then gives
localized estimates against the original domain, even though the original
coordinates need not extend into the filled holes.
-/

open Set Filter MeasureTheory Finset Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def gradientEnergy (f : (ℝ × ℝ) → ℝ) (g : (ℝ × ℝ) → PlanarMetric) (z : ℝ × ℝ) : ℝ :=
  covectorEnergy ![(planarGradient f z).1, (planarGradient f z).2] (g z)

theorem gradientEnergy_nonneg (f : (ℝ × ℝ) → ℝ) {g : (ℝ × ℝ) → PlanarMetric}
    (hg : ∀ z, (g z).PosDef) (z : ℝ × ℝ) : 0 ≤ gradientEnergy f g z :=
  covectorEnergy_nonneg _ (hg z)

theorem gradientEnergy_spherical (f : (ℝ × ℝ) → ℝ) (z : ℝ × ℝ) :
    gradientEnergy f (fun z => sphericalMetricFactor z • 1) z =
      (planarGradient f z).1 ^ 2 + (planarGradient f z).2 ^ 2 := by
  unfold gradientEnergy
  rw [covectorEnergy_eq_matrixEnergy,
    matrixEnergy_pos_smul _ Matrix.PosDef.one (sphericalMetricFactor_pos z),
    ← covectorEnergy_eq_matrixEnergy, covectorEnergy_identity]

theorem coordinateGram_energy_eq_sum
    (f : ℕ → (ℝ × ℝ) → ℝ) (n : ℕ) (g : (ℝ × ℝ) → PlanarMetric) (z : ℝ × ℝ) :
    matrixEnergy (coordinateGram f n z) (g z) =
      ∑ i ∈ range n, gradientEnergy (f i) g z :=
  gramEnergy_eq_sum_covectorEnergy _ _ n (g z)

theorem gradientEnergy_le_coordinateGram
    (f : ℕ → (ℝ × ℝ) → ℝ) {i n : ℕ} (hi : i < n)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : ∀ z, (g z).PosDef) (z : ℝ × ℝ) :
    gradientEnergy (f i) g z ≤ matrixEnergy (coordinateGram f n z) (g z) :=
  covectorEnergy_le_gramEnergy
    (fun j => (planarGradient (f j) z).1) (fun j => (planarGradient (f j) z).2) hi (hg z)

theorem continuousOn_matrixEnergy_local
    {X : Type*} [TopologicalSpace X] {D : Set X}
    {A g : X → PlanarMetric} (hA : ContinuousOn A D) (hg : ContinuousOn g D)
    (hPD : ∀ x ∈ D, (g x).PosDef) :
    ContinuousOn (fun x => matrixEnergy (A x) (g x)) D := by
  have hi : ContinuousOn (fun x => (g x).det⁻¹) D :=
    (continuous_id.matrix_det.comp_continuousOn hg).inv₀
      (fun x hx => (hPD x hx).det_pos.ne')
  have hiMat : ContinuousOn (fun x => (g x).det⁻¹ • (g x).adjugate) D :=
    hi.smul (continuous_id.matrix_adjugate.comp_continuousOn hg)
  have hm : ContinuousOn (fun x => ((g x).det⁻¹ • (g x).adjugate) * A x) D :=
    hiMat.mul hA
  have ht : ContinuousOn (fun x => Matrix.trace (((g x).det⁻¹ • (g x).adjugate) * A x)) D :=
    (continuous_id.matrix_trace : Continuous (Matrix.trace : PlanarMetric → ℝ)).comp_continuousOn hm
  simpa only [matrixEnergy, Matrix.inv_def, Ring.inverse_eq_inv, Pi.mul_def, Function.comp_apply, id_eq] using
    ht.mul (continuous_id.matrix_det.comp_continuousOn hg).sqrt

theorem continuousOn_gradientEnergy
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    {f : (ℝ × ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    ContinuousOn (gradientEnergy f g) Ω := by
  have hx : ContinuousOn (fun z => (planarGradient f z).1) Ω :=
    (hf.fderiv_of_isOpen (m := ∞) hΩ (by simp)).continuousOn.clm_apply continuousOn_const
  have hy : ContinuousOn (fun z => (planarGradient f z).2) Ω :=
    (hf.fderiv_of_isOpen (m := ∞) hΩ (by simp)).continuousOn.clm_apply continuousOn_const
  have hv : ContinuousOn (fun z => ![(planarGradient f z).1, (planarGradient f z).2]) Ω := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact hx
    · exact hy
  have hA : ContinuousOn (fun z => Matrix.vecMulVec
      ![(planarGradient f z).1, (planarGradient f z).2]
      ![(planarGradient f z).1, (planarGradient f z).2]) Ω := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (continuousOn_pi.mp hv i).mul (continuousOn_pi.mp hv j)
  change ContinuousOn (fun z => covectorEnergy
    ![(planarGradient f z).1, (planarGradient f z).2] (g z)) Ω
  simpa only [covectorEnergy_eq_matrixEnergy] using
    continuousOn_matrixEnergy_local hA hg.continuousOn (fun z _ => hPD z)

theorem integrableOn_gradientEnergy
    {Ω Q : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    {f : (ℝ × ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    IntegrableOn (gradientEnergy f g) Q :=
  ((continuousOn_gradientEnergy hΩ hf hg hPD).mono hQΩ).integrableOn_compact hQ


theorem integrable_gradientEnergy_spherical_of_memLp
    {μ : Measure (ℝ × ℝ)} {f : (ℝ × ℝ) → ℝ}
    (hf : MemLp (planarGradient f) 2 μ) :
    Integrable (gradientEnergy f (fun z => sphericalMetricFactor z • 1)) μ := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp_memLp' hf
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp_memLp' hf
  have hxx : MemLp (fun z => (planarGradient f z).1 * (planarGradient f z).1) 1 μ := hx.mul hx
  have hyy : MemLp (fun z => (planarGradient f z).2 * (planarGradient f z).2) 1 μ := hy.mul hy
  have hi := (memLp_one_iff_integrable.mp hxx).add (memLp_one_iff_integrable.mp hyy)
  refine hi.congr (Eventually.of_forall fun z => ?_)
  simpa only [pow_two, Pi.add_apply] using (gradientEnergy_spherical f z).symm

/-- Integrating the trace really gives the sum of all transferred
coordinate energies. -/
theorem integral_coordinateGram_eq_sum
    {Ω Q K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (f : ℕ → (ℝ × ℝ) → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω) (n : ℕ)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    (∫ z in Q \ K, matrixEnergy (coordinateGram f n z) (g z)) =
      ∑ i ∈ range n, ∫ z in Q \ K, gradientEnergy (f i) g z := by
  simp_rw [coordinateGram_energy_eq_sum]
  exact integral_finsetSum _ (fun i _ =>
    (integrableOn_gradientEnergy hΩ hQ hQΩ (hf i) hg hPD).mono_set sdiff_subset)

/-- Compare localized energy to the original domain, without evaluating
or integrating an original coordinate in the added holes. -/
theorem localized_energy_lt_source
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {Q G K E : Set X} (hQ : MeasurableSet Q) (hG : MeasurableSet G)
    (hK : MeasurableSet K) (hE : MeasurableSet E) (hEK : E ⊆ K)
    (hQKG : Q ∩ K ⊆ G) {f u T : X → ℝ}
    (hf : IntegrableOn f Q μ) (hu : IntegrableOn u G μ)
    (hT : IntegrableOn T (Q \ K) μ) (hu0 : ∀ x ∈ G, 0 ≤ u x)
    (hcore : ∀ x ∈ Q ∩ K, f x = u x) (htail : ∀ x ∈ Q \ K, f x ≤ T x)
    {ε : ℝ} (hε : (∫ x in Q \ K, T x ∂μ) < ε) :
    (∫ x in Q \ E, f x ∂μ) < (∫ x in G \ E, u x ∂μ) + ε := by
  have hdiff : (Q \ E) \ K = Q \ K := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · exact fun hx => ⟨⟨hx.1, fun he => hx.2 (hEK he)⟩, hx.2⟩
  have heq : (∫ x in (Q \ E) ∩ K, f x ∂μ) = ∫ x in (Q \ E) ∩ K, u x ∂μ :=
    setIntegral_congr_fun ((hQ.diff hE).inter hK)
      (fun x hx => hcore x ⟨hx.1.1, hx.2⟩)
  have hsplit := integral_inter_add_sdiff hK (hf.mono_set (s := Q \ E) sdiff_subset)
  rw [hdiff, heq] at hsplit
  have ht : (∫ x in Q \ K, f x ∂μ) < ε :=
    (setIntegral_mono_on (hf.mono_set sdiff_subset) hT (hQ.diff hK) htail).trans_lt hε
  have hc : (∫ x in (Q \ E) ∩ K, u x ∂μ) ≤ ∫ x in G \ E, u x ∂μ :=
    setIntegral_mono_set (hu.mono_set sdiff_subset)
      ((ae_restrict_mem (hG.diff hE)).mono (fun x hx => hu0 x hx.1))
      (Eventually.of_forall (fun x hx => ⟨hQKG ⟨hx.1.1, hx.2⟩, hx.1.2⟩))
  linarith

theorem integrableOn_coordinateGram_energy
    {Ω Q : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (f : ℕ → (ℝ × ℝ) → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω) (n : ℕ)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    IntegrableOn (fun z => matrixEnergy (coordinateGram f n z) (g z)) Q := by
  have hi := integrable_finsetSum (range n) (fun i _ =>
    integrableOn_gradientEnergy hΩ hQ hQΩ (hf i) hg hPD)
  exact hi.congr (Eventually.of_forall fun z => (coordinateGram_energy_eq_sum f n g z).symm)

/-- The localized estimate for each actual transferred coordinate. The
original right-hand side is integrated only over its original domain. -/
theorem localized_coordinate_energy_lt
    {Ω Q G K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hG : MeasurableSet G) (hK : IsClosed K) (hQKG : Q ∩ K ⊆ G)
    (f u : ℕ → (ℝ × ℝ) → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω)
    {n : ℕ} (hu : ∀ i < n, IntegrableOn
      (gradientEnergy (u i) (fun z => sphericalMetricFactor z • 1)) G)
    (hretain : ∀ᶠ z in 𝓝ˢ K, ∀ i < n, f i z = u i z)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef)
    (hmetric : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1)
    {ε : ℝ} (henergy : (∫ z in Q \ K, matrixEnergy (coordinateGram f n z) (g z)) < ε)
    {i : ℕ} (hi : i < n) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEK : E ⊆ K) :
    (∫ z in Q \ E, gradientEnergy (f i) g z) <
      (∫ z in G \ E, gradientEnergy (u i) (fun z => sphericalMetricFactor z • 1) z) + ε := by
  apply localized_energy_lt_source hQ.isClosed.measurableSet hG hK.measurableSet hE hEK hQKG
    (integrableOn_gradientEnergy hΩ hQ hQΩ (hf i) hg hPD) (hu i hi)
    ((integrableOn_coordinateGram_energy hΩ hQ hQΩ f hf n hg hPD).mono_set sdiff_subset)
    (fun z _ => gradientEnergy_nonneg _ (fun w => Matrix.PosDef.one.smul
      (sphericalMetricFactor_pos w)) z) ?_ (fun z _ => gradientEnergy_le_coordinateGram f hi hPD z)
    henergy
  intro z hz
  have heq : f i =ᶠ[𝓝 z] u i :=
    (hretain.filter_mono (nhds_le_nhdsSet hz.2)).mono (fun _ hx => hx i hi)
  have hgrad : planarGradient (f i) z = planarGradient (u i) z := by
    simp only [planarGradient, heq.fderiv_eq (𝕜 := ℝ)]
  simp only [gradientEnergy, hgrad, hmetric.self_of_nhdsSet z hz.2]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
