import Mathlib
import OAI.Geometry.CubicTorus.Regularity.FiberPoint

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

def normalFirstVariation (μ : FiniteMeasure NormalBundle) (a : WallVariation) : ℝ :=
  ∫ z, ⟪(z.2 : Cover), coordinateNormalVelocity a.coordinate a.function z.1 z.2⟫
    ∂(μ : Measure NormalBundle)

lemma integrable_normalFirstVariation (μ : FiniteMeasure NormalBundle) (a : WallVariation) :
    Integrable (fun z : NormalBundle ↦
      ⟪(z.2 : Cover), coordinateNormalVelocity a.coordinate a.function z.1 z.2⟫)
        (μ : Measure NormalBundle) :=
  (continuous_normalUnit.inner (𝕜 := ℝ)
    (continuous_coordinateNormalVelocity a.coordinate a.smooth)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma integral_inner_doubleVelocity_zero (μ : FiniteMeasure NormalBundle)
    (a b : WallVariation) (k : ℝ) :
    (∫ z, ⟪(z.2 : Cover), doubleVelocityCoefficient a b k 0 z.1 z.2⟫
      ∂(μ : Measure NormalBundle)) = normalFirstVariation μ a + k * normalFirstVariation μ b := by
  simp only [doubleVelocityCoefficient, coordinateMove, zero_mul, zero_smul, add_zero,
    inner_add_right, real_inner_smul_right]
  rw [integral_add (integrable_normalFirstVariation μ a)
    ((integrable_normalFirstVariation μ b).const_mul k), integral_const_mul]
  rfl

lemma integrable_doublePerturbation (a b : WallVariation) (μ : FiniteMeasure NormalBundle)
    (k t : ℝ) :
    Integrable (fun z : NormalBundle ↦ ‖(z.2 : Cover) +
      t • doubleVelocityCoefficient a b k t z.1 z.2‖) (μ : Measure NormalBundle) := by
  have hc : Continuous (fun z : NormalBundle ↦ (z.2 : Cover) +
      t • doubleVelocityCoefficient a b k t z.1 z.2) :=
    continuous_normalUnit.add
      ((continuous_const : Continuous (fun _ : NormalBundle ↦ t)).smul
        (continuous_doubleVelocityCoefficient a b k t))
  exact hc.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma doubleVelocityCoefficient_eventually_bounded (a b : WallVariation)
    {k : ℝ → ℝ} (hk : ContinuousAt k 0) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ z : NormalBundle,
      ‖doubleVelocityCoefficient a b (k t) t z.1 z.2‖ ≤
      2 * (a.bound : ℝ) + (|k 0| + 1) *
      (2 * (b.bound : ℝ) * (1 + 2 * (a.bound : ℝ))) := by
  have hb : ∀ᶠ t : ℝ in 𝓝 0, |k t| ≤ |k 0| + 1 :=
    (hk.abs.eventually (eventually_lt_nhds (by linarith : |k 0| < |k 0| + 1))).mono
      fun _ h ↦ h.le
  have ht : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ 1 :=
    (continuous_abs.continuousAt.eventually
      (eventually_lt_nhds (by norm_num : |(0 : ℝ)| < 1))).mono fun _ h ↦ h.le
  filter_upwards [ht, hb] with t ht hb z
  exact doubleVelocityCoefficient_norm_le a b ht hb _ z.2.property

theorem hasDerivAt_doubleNormalArea (a b : WallVariation) (μ : FiniteMeasure NormalBundle)
    {k : ℝ → ℝ} (hk : ContinuousAt k 0) :
    HasDerivAt (fun t : ℝ ↦ ∫ z, ‖doubleCofactor a b t (t * k t) z.1 z.2‖
      ∂(μ : Measure NormalBundle))
      (normalFirstVariation μ a + k 0 * normalFirstVariation μ b) 0 := by
  simp_rw [doubleCofactor_eq]
  rw [← integral_inner_doubleVelocity_zero]
  exact hasDerivAt_integral_norm_perturbation
    (fun z : NormalBundle ↦ (z.2 : Cover))
    (fun t z ↦ doubleVelocityCoefficient a b (k t) t z.1 z.2)
    (fun z ↦ z.2.property) (fun t ↦ integrable_doublePerturbation a b μ (k t) t)
    (Eventually.of_forall fun z ↦ continuousAt_doubleVelocityCoefficient a b hk _ _)
    (fun _ ↦ 2 * (a.bound : ℝ) + (|k 0| + 1) *
      (2 * (b.bound : ℝ) * (1 + 2 * (a.bound : ℝ)))) (integrable_const _)
    ((doubleVelocityCoefficient_eventually_bounded a b hk).mono
      fun _ ht ↦ Eventually.of_forall ht)

lemma doubleNormalArea_zero (a b : WallVariation) (μ : FiniteMeasure NormalBundle) :
    (∫ z, ‖doubleCofactor a b 0 0 z.1 z.2‖ ∂(μ : Measure NormalBundle)) = (μ.mass : ℝ) := by
  simp_rw [doubleCofactor, coordinateCofactor_eq, zero_smul, add_zero,
    fun z : NormalBundle ↦ z.2.property]
  simp only [integral_const, smul_eq_mul, mul_one]
  rfl

def volumeCorrectionCoefficient (a b : WallVariation) (E : Set Torus) (t : ℝ) : ℝ :=
  -directionalFlux E a.coordinate a.function / transportedFlux a b E t

lemma continuousAt_volumeCorrectionCoefficient (a b : WallVariation) (E : Set Torus)
    (hB : directionalFlux E b.coordinate b.function ≠ 0) :
    ContinuousAt (volumeCorrectionCoefficient a b E) 0 := by
  apply continuousAt_const.div (continuousAt_transportedFlux a b E)
  rwa [transportedFlux_zero]

lemma volume_doubleRegion_corrected (a b : WallVariation) {E : Set Torus}
    (hE : MeasurableSet E) (hB : directionalFlux E b.coordinate b.function ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      |t| * (a.bound : ℝ) < 1 ∧
      |t * volumeCorrectionCoefficient a b E t| * (b.bound : ℝ) < 1 ∧
      torusVolume (doubleRegion a b t (t * volumeCorrectionCoefficient a b E t) E) = torusVolume E := by
  have hc := continuousAt_volumeCorrectionCoefficient a b E hB
  have ht : ∀ᶠ t : ℝ in 𝓝 0, |t| * (a.bound : ℝ) < 1 :=
    (continuous_abs.mul continuous_const).continuousAt.eventually
      (eventually_lt_nhds (by simp : |(0 : ℝ)| * (a.bound : ℝ) < 1))
  have hs : ∀ᶠ t : ℝ in 𝓝 0,
      |t * volumeCorrectionCoefficient a b E t| * (b.bound : ℝ) < 1 :=
    ((continuousAt_id.mul hc).abs.mul continuousAt_const).eventually
      (eventually_lt_nhds (by simp : |(0 : ℝ) * volumeCorrectionCoefficient a b E 0| *
        (b.bound : ℝ) < 1))
  have hn : ∀ᶠ t : ℝ in 𝓝 0, transportedFlux a b E t ≠ 0 :=
    (continuousAt_transportedFlux a b E).eventually_ne (by rwa [transportedFlux_zero])
  filter_upwards [ht, hs, hn] with t ht hs hn
  refine ⟨ht, hs, ?_⟩
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change torusVolume.real _ = torusVolume.real E
  rw [volume_doubleRegion a b ht hs hE]
  unfold volumeCorrectionCoefficient
  field_simp [hn]
  ring

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

theorem isMinimizerAt_mixed_stationary {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (a b : WallVariation) (hB : directionalFlux E b.coordinate b.function ≠ 0) :
    normalFirstVariation μ a * directionalFlux E b.coordinate b.function =
      normalFirstVariation μ b * directionalFlux E a.coordinate a.function := by
  let k := volumeCorrectionCoefficient a b E
  have hlocal : IsLocalMin (fun t : ℝ ↦ ∫ z,
      ‖doubleCofactor a b t (t * k t) z.1 z.2‖ ∂(μ : Measure NormalBundle)) 0 := by
    filter_upwards [volume_doubleRegion_corrected a b hE hB] with t ht
    simp only [zero_mul, doubleNormalArea_zero, hμ.1]
    have hEa := measurableSet_coordinateRegion a.coordinate
      (a.smooth.differentiable (by simp)) a.derivative_bound ht.1 hE
    have hfa := finitePerimeter_coordinateRegion a.coordinate a.smooth a.periodic
      a.derivative_bound a.faces ht.1 hE hmin.1.2.ne
    have hfin := finitePerimeter_coordinateRegion b.coordinate b.smooth b.periodic
      b.derivative_bound b.faces ht.2.1 hEa hfa.2.ne
    have hleast := hmin.2.2 _ hfin (ht.2.2.trans hmin.2.1)
    have harea := perimeter_doubleRegion_le_normalArea a b ht.1 ht.2.1 hE hμ
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hleast.trans harea)
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun z ↦ norm_nonneg _)] using hh
  have hz := hlocal.hasDerivAt_eq_zero
    (hasDerivAt_doubleNormalArea a b μ (continuousAt_volumeCorrectionCoefficient a b E hB))
  dsimp only [k, volumeCorrectionCoefficient] at hz
  rw [transportedFlux_zero] at hz
  field_simp at hz
  nlinarith

theorem isMinimizerAt_exists_coordinate_multiplier {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (b : WallVariation) (hB : directionalFlux E b.coordinate b.function ≠ 0) :
    ∃ H : ℝ, ∀ a : WallVariation,
      normalFirstVariation μ a = H * directionalFlux E a.coordinate a.function := by
  refine ⟨normalFirstVariation μ b / directionalFlux E b.coordinate b.function, fun a ↦ ?_⟩
  have h := isMinimizerAt_mixed_stationary hmin hE hμ a b hB
  apply (mul_right_cancel₀ hB)
  calc
    normalFirstVariation μ a * directionalFlux E b.coordinate b.function =
        normalFirstVariation μ b * directionalFlux E a.coordinate a.function := h
    _ = _ := by field_simp

end CubicTorus

namespace CubicTorus

lemma fderiv_component {F : Cover → Cover} {x : Cover} (hF : DifferentiableAt ℝ F x)
    (i : Fin 3) (v : Cover) :
    fderiv ℝ (fun y ↦ F y i) x v = fderiv ℝ F x v i := by
  have hh := ((EuclideanSpace.proj i).hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ F y i) x = _ at hh
  rw [hh]
  rfl

lemma flux_sum_components (E : Set Torus) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) =
      ∑ i : Fin 3, directionalFlux E i (fun x ↦ F x i) := by
  unfold divergence directionalFlux
  simp_rw [← fderiv_component (hF.differentiable (by simp)).differentiableAt]
  exact integral_finsetSum _ (fun i _ ↦
    (integrableOn_directionalDeriv i ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF)).mono_set
      inter_subset_left)

lemma exists_positive_directionalFlux {E : Set Torus} (hP : 0 < perimeter E) :
    ∃ (i : Fin 3) (f : Cover → ℝ), ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ n x, f (x + latticeVector n) = f x) ∧ 0 < directionalFlux E i f := by
  have hh : ∃ F, AdmissibleField F ∧
      0 < ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
    by_contra! hn
    have : perimeter E ≤ 0 := iSup_le fun F ↦ iSup_le fun hF ↦ by
      exact (ENNReal.ofReal_eq_zero.2 (hn F hF)).le
    exact not_le_of_gt hP this
  obtain ⟨F, hF, hp⟩ := hh
  rw [flux_sum_components E hF.1] at hp
  have hi : ∃ i : Fin 3, 0 < directionalFlux E i (fun x ↦ F x i) := by
    by_contra! hn
    exact not_le_of_gt hp (Finset.sum_nonpos fun i _ ↦ hn i)
  obtain ⟨i, hi⟩ := hi
  refine ⟨i, fun x ↦ F x i, (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF.1, ?_, hi⟩
  intro n x
  dsimp only
  rw [hF.2.1]

def wallCutoff (i : Fin 3) (x : Cover) : ℝ := (1 - Real.cos (2 * Real.pi * x i)) / 2

lemma wallCutoff_contDiff (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (wallCutoff i) := by
  unfold wallCutoff
  fun_prop

lemma wallCutoff_periodic (i : Fin 3) (n : Fin 3 → ℤ) (x : Cover) :
    wallCutoff i (x + latticeVector n) = wallCutoff i x := by
  have he : 2 * Real.pi * (x + latticeVector n) i =
      2 * Real.pi * x i + (n i : ℝ) * (2 * Real.pi) := by
    simp only [PiLp.add_apply, latticeVector]
    ring
  simp only [wallCutoff, he, Real.cos_add_int_mul_two_pi]

lemma wallCutoff_face (i : Fin 3) (x : Cover) (hx : x i = 0 ∨ x i = 1) :
    wallCutoff i x = 0 := by
  rcases hx with hx | hx <;> simp [wallCutoff, hx, Real.cos_two_pi]

lemma wallCutoff_halfShift (i : Fin 3) (x : Cover) :
    wallCutoff i (x + (1 / 2 : ℝ) • EuclideanSpace.single i 1) = 1 - wallCutoff i x := by
  have he : 2 * Real.pi * (x + (1 / 2 : ℝ) • (EuclideanSpace.single i 1 : Cover)) i =
      2 * Real.pi * x i + Real.pi := by
    simp
    ring
  rw [wallCutoff, he, Real.cos_add_pi]
  unfold wallCutoff
  ring

lemma smooth_flux_translation {F : Cover → Cover}
    (hc : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    (a : Cover) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' ((fun z => z + quotientMap a) ⁻¹' E),
      divergence F x) =
    ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence (fun y => F (y - a)) x := by
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap a) ⁻¹' E) :=
    (continuous_add_const _).measurable hE
  rw [← setIntegral_lift (continuous_divergence hc) (divergence_periodic hp) hpre]
  have hGc : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ F (y - a)) :=
    hc.comp (contDiff_id.sub contDiff_const)
  have hGp : ∀ n x, F ((x + latticeVector n) - a) = F (x - a) := by
    intro n x
    rw [add_sub_right_comm, hp]
  rw [← setIntegral_lift (continuous_divergence hGc) (divergence_periodic hGp) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (fun y => F (y - a)) (representative (z + quotientMap a))) := by
    funext z
    simp only [sub_eq_add_neg, divergence_translate]
    have hq : quotientMap (representative (z + quotientMap a) + -a) =
        quotientMap (representative z) := by
      rw [quotientMap_add, quotientMap_representative, quotientMap_representative,
        quotientMap_neg]
      abel
    obtain ⟨n, hn⟩ := same_quotient_lattice hq
    rw [hn, divergence_periodic hp]
  rw [he]
  exact (measurePreserving_add_right torusVolume (quotientMap a)).setIntegral_preimage_emb
    (Homeomorph.addRight (quotientMap a)).measurableEmbedding
      (fun z => divergence (fun y => F (y - a)) (representative z)) E

lemma directionalFlux_translation (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x, f (x + latticeVector n) = f x)
    (a : Cover) {E : Set Torus} (hE : MeasurableSet E) :
    directionalFlux ((fun z ↦ z + quotientMap a) ⁻¹' E) i (fun x ↦ f (x + a)) =
      directionalFlux E i f := by
  have hFc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ f (x + a) • (EuclideanSpace.single i 1 : Cover)) :=
    (hf.comp (contDiff_id.add contDiff_const)).smul contDiff_const
  have hFp : ∀ n x, f ((x + latticeVector n) + a) • (EuclideanSpace.single i 1 : Cover) =
      f (x + a) • EuclideanSpace.single i 1 := by
    intro n x
    rw [add_right_comm, hp]
  have hh := smooth_flux_translation hFc hFp a hE
  simp only [sub_add_cancel] at hh
  simp_rw [divergence_smul_const (hf.differentiable (by simp)).differentiableAt] at hh
  unfold directionalFlux
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (divergence_smul_const
    ((hf.comp (contDiff_id.add contDiff_const)).differentiable (by simp)).differentiableAt
    (EuclideanSpace.single i 1)).symm

theorem exists_positive_wallVariation {E : Set Torus} (hE : MeasurableSet E)
    (hP : 0 < perimeter E) :
    ∃ (a : Cover) (D : WallVariation),
      0 < directionalFlux ((fun z ↦ z + quotientMap a) ⁻¹' E) D.coordinate D.function := by
  obtain ⟨i, f, hf, hp, hflux⟩ := exists_positive_directionalFlux hP
  let f₀ : Cover → ℝ := fun x ↦ wallCutoff i x * f x
  let f₁ : Cover → ℝ := fun x ↦ (1 - wallCutoff i x) * f x
  have hc₀ : ContDiff ℝ (⊤ : ℕ∞) f₀ := (wallCutoff_contDiff i).mul hf
  have hc₁ : ContDiff ℝ (⊤ : ℕ∞) f₁ := (contDiff_const.sub (wallCutoff_contDiff i)).mul hf
  have hp₀ : ∀ n x, f₀ (x + latticeVector n) = f₀ x := by
    intro n x
    dsimp only [f₀]
    rw [wallCutoff_periodic, hp]
  have hp₁ : ∀ n x, f₁ (x + latticeVector n) = f₁ x := by
    intro n x
    dsimp only [f₁]
    rw [wallCutoff_periodic, hp]
  have he : (fun x ↦ f₀ x + f₁ x) = f := by
    funext x
    dsimp only [f₀, f₁]
    ring
  have hs : 0 < directionalFlux E i f₀ + directionalFlux E i f₁ := by
    rw [← directionalFlux_add E i hc₀ hc₁, he]
    exact hflux
  by_cases hpos : 0 < directionalFlux E i f₀
  · have hface₀ : ∀ x, x i = 0 ∨ x i = 1 → f₀ x = 0 := by
      intro x hx
      simp [f₀, wallCutoff_face i x hx]
    obtain ⟨D, hi, hfD⟩ := exists_wallVariation_of_function i hc₀ hp₀ hface₀
    refine ⟨0, D, ?_⟩
    have hz : quotientMap 0 = 0 := by ext j; simp [quotientMap]
    simpa only [hi, hfD, hz, add_zero, preimage_id'] using hpos
  · have hpos₁ : 0 < directionalFlux E i f₁ := by linarith
    let a : Cover := (1 / 2 : ℝ) • EuclideanSpace.single i 1
    let g : Cover → ℝ := fun x ↦ f₁ (x + a)
    have hgc : ContDiff ℝ (⊤ : ℕ∞) g := hc₁.comp (contDiff_id.add contDiff_const)
    have hgp : ∀ n x, g (x + latticeVector n) = g x := by
      intro n x
      dsimp only [g]
      rw [add_right_comm, hp₁]
    have hgf : ∀ x, x i = 0 ∨ x i = 1 → g x = 0 := by
      intro x hx
      dsimp only [g, f₁, a]
      rw [wallCutoff_halfShift, wallCutoff_face i x hx]
      ring
    obtain ⟨D, hi, hfD⟩ := exists_wallVariation_of_function i hgc hgp hgf
    refine ⟨a, D, ?_⟩
    rw [hi, hfD]
    change 0 < directionalFlux ((fun z ↦ z + quotientMap a) ⁻¹' E) i (fun x ↦ f₁ (x + a))
    rwa [directionalFlux_translation i hc₁ hp₁ a hE]

end CubicTorus

namespace CubicTorus

theorem isMinimizerAt_exists_weakCMC {V : ℝ} (hV : V ∈ Ioo 0 1) {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E) :
    ∃ (a : Cover) (μ : FiniteMeasure NormalBundle) (H : ℝ),
      IsNormalMeasure ((fun z ↦ z + quotientMap a) ⁻¹' E) μ ∧
      ∀ D : WallVariation, normalFirstVariation μ D =
        H * directionalFlux ((fun z ↦ z + quotientMap a) ⁻¹' E) D.coordinate D.function := by
  obtain ⟨a, b, hb⟩ := exists_positive_wallVariation hE
    (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1)
  have hEa : MeasurableSet ((fun z ↦ z + quotientMap a) ⁻¹' E) :=
    hE.preimage (continuous_id.add continuous_const).measurable
  have hmina := isMinimizerAt_translation hmin (quotientMap a)
  obtain ⟨μ, hμ⟩ := exists_normalMeasure hEa hmina.1.2.ne
  obtain ⟨H, hH⟩ := isMinimizerAt_exists_coordinate_multiplier hmina hEa hμ b hb.ne'
  exact ⟨a, μ, H, hμ, hH⟩

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

def tangentialDivergence (F : Cover → Cover) (x n : Cover) : ℝ :=
  divergence F x - ⟪n, fderiv ℝ F x n⟫

lemma inner_coordinateNormalVelocity (i : Fin 3) (f : Cover → ℝ) (x : Cover)
    {n : Cover} (hn : ‖n‖ = 1) :
    ⟪n, coordinateNormalVelocity i f x n⟫ =
      fderiv ℝ f x (EuclideanSpace.single i 1) - n i * fderiv ℝ f x n := by
  simp only [coordinateNormalVelocity, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hn, one_pow, mul_one, inner_gradient_right,
    conj_trivial]
  congr 1
  simp [PiLp.inner_apply, EuclideanSpace.single]

lemma tangentialDivergence_eq_sum {F : Cover → Cover} {x n : Cover}
    (hF : DifferentiableAt ℝ F x) (hn : ‖n‖ = 1) :
    tangentialDivergence F x n = ∑ i : Fin 3,
      ⟪n, coordinateNormalVelocity i (fun y ↦ F y i) x n⟫ := by
  simp_rw [inner_coordinateNormalVelocity _ _ _ hn, fderiv_component hF]
  simp only [Finset.sum_sub_distrib, tangentialDivergence, divergence]
  congr 1
  simp [PiLp.inner_apply, mul_comm]

lemma continuous_tangentialDivergence {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (fun z : NormalBundle ↦ tangentialDivergence F z.1 z.2) := by
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((continuous_divergence hF).comp hx).sub
    (continuous_normalUnit.inner
      (((hF.continuous_fderiv (by simp)).comp hx).clm_apply continuous_normalUnit))

lemma integral_tangentialDivergence_eq_sum {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (μ : FiniteMeasure NormalBundle) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      ∑ i : Fin 3, ∫ z, ⟪(z.2 : Cover),
        coordinateNormalVelocity i (fun y ↦ F y i) z.1 z.2⟫ ∂(μ : Measure NormalBundle) := by
  have he (z : NormalBundle) := tangentialDivergence_eq_sum (x := (z.1 : Cover))
    (hF.differentiable (by simp)).differentiableAt z.2.property
  simp_rw [he]
  apply integral_finsetSum
  intro i _
  exact (continuous_normalUnit.inner (𝕜 := ℝ)
    (continuous_coordinateNormalVelocity i
      ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem tangent_firstVariation_of_coordinate {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x)
    (hw : ∀ i x, x i = 0 ∨ x i = 1 → F x i = 0) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  rw [integral_tangentialDivergence_eq_sum hF, flux_sum_components E hF,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hpc : ∀ m x, (fun y ↦ F y i) (x + latticeVector m) = F x i := by
    intro m x
    change (F (x + latticeVector m)) i = (F x) i
    rw [hp]
  obtain ⟨D, hi, hf⟩ := exists_wallVariation_of_function i hc hpc (hw i)
  simpa only [normalFirstVariation, hi, hf] using hH D

theorem weakCMC_identity {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x)
    (hw : ∀ i x, x i = 0 ∨ x i = 1 → F x i = 0) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle) := by
  rw [tangent_firstVariation_of_coordinate hH hF hp hw]
  obtain ⟨C, hC, hbound⟩ := periodic_bounded hF.continuous hp
  have h := normalMeasure_flux hμ hF hp (by linarith : 0 < C + 1)
    (fun x ↦ (hbound x).trans (by linarith : C ≤ C + 1))
  exact congrArg (fun r : ℝ ↦ H * r) h.symm

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma weakCMC_firstVariation_bound {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x)
    (hw : ∀ i x, x i = 0 ∨ x i = 1 → F x i = 0) :
    |∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)| ≤
      |H| * ∫ z, ‖F z.1‖ ∂(μ : Measure NormalBundle) := by
  rw [weakCMC_identity hμ hH hF hp hw, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hfc : Continuous (fun z : NormalBundle ↦ F z.1) :=
    hF.continuous.comp (continuous_subtype_val.comp continuous_fst)
  calc
    _ ≤ ∫ z, |⟪(z.2 : Cover), F z.1⟫| ∂(μ : Measure NormalBundle) :=
      abs_integral_le_integral_abs
    _ ≤ _ := by
      apply integral_mono
        ((continuous_normalUnit.inner (𝕜 := ℝ) hfc).abs.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        (hfc.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      intro z
      simpa only [z.2.property, one_mul] using abs_real_inner_le_norm (z.2 : Cover) (F z.1)

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology

lemma latticeVector_add (m n : Fin 3 → ℤ) : latticeVector (m + n) = latticeVector m + latticeVector n := by
  ext i
  simp [latticeVector]

lemma latticeVector_zero : latticeVector 0 = 0 := by
  ext i
  simp [latticeVector]

lemma finite_lattice_support_near {Y : Type*} [Zero Y] {f : Cover → Y}
    (hf : HasCompactSupport f) (a : Cover) :
    ∃ s : Finset (Fin 3 → ℤ), ∀ x ∈ Metric.ball a 1, ∀ n ∉ s,
      f (x + latticeVector n) = 0 := by
  classical
  obtain ⟨R, _, hR⟩ := hf.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt (R + ‖a‖ + 1)
  let S : Set (Fin 3 → ℤ) := {n | ∀ i, n i ∈ Icc (-(N : ℤ)) N}
  have hS : S.Finite := Set.Finite.pi' (fun _ ↦ Set.finite_Icc (-(N : ℤ)) N)
  refine ⟨hS.toFinset, ?_⟩
  intro x hx n hn
  by_contra hnonzero
  have hmem : x + latticeVector n ∈ tsupport f := subset_tsupport f hnonzero
  have hnx : ‖x‖ ≤ ‖a‖ + 1 := by
    have hh := norm_add_le (x - a) a
    rw [sub_add_cancel] at hh
    have hx' : ‖x - a‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    linarith
  have hln : ‖latticeVector n‖ < N := by
    have hh := norm_sub_le (x + latticeVector n) x
    rw [add_sub_cancel_left] at hh
    exact lt_of_le_of_lt (hh.trans (add_le_add (hR _ hmem) hnx)) (by linarith)
  apply hn
  rw [Set.Finite.mem_toFinset]
  intro i
  have hc : |(n i : ℝ)| < N := by
    have hh : |(n i : ℝ)| ≤ ‖latticeVector n‖ := by
      simpa only [latticeVector, Real.norm_eq_abs] using
        (PiLp.norm_apply_le (latticeVector n) i)
    exact hh.trans_lt hln
  constructor
  · exact_mod_cast (abs_le.mp hc.le).1
  · exact_mod_cast (abs_le.mp hc.le).2

def latticePeriodize {Y : Type*} [AddCommMonoid Y] [TopologicalSpace Y]
    (f : Cover → Y) (x : Cover) : Y := ∑' n : Fin 3 → ℤ, f (x + latticeVector n)

lemma latticePeriodize_periodic {Y : Type*} [AddCommMonoid Y] [TopologicalSpace Y]
    (f : Cover → Y) (m : Fin 3 → ℤ) (x : Cover) :
    latticePeriodize f (x + latticeVector m) = latticePeriodize f x := by
  unfold latticePeriodize
  calc
    _ = ∑' n : Fin 3 → ℤ, f (x + latticeVector (n + m)) := by
      apply tsum_congr
      intro n
      rw [latticeVector_add]
      congr 1
      abel
    _ = _ := (Equiv.addRight m).tsum_eq (fun n ↦ f (x + latticeVector n))

lemma latticePeriodize_contDiff {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Cover → Y} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (latticePeriodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro a
  obtain ⟨s, hs⟩ := finite_lattice_support_near hs a
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ∑ n ∈ s, f (x + latticeVector n)) :=
    ContDiff.sum fun n _ ↦ hf.comp (contDiff_id.add contDiff_const)
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds a (by norm_num : (0 : ℝ) < 1)] with x hx
  exact tsum_eq_sum (hs x hx)

end CubicTorus

namespace CubicTorus

lemma translate_not_mem_tsupport {Y : Type*} [Zero Y] {f : Cover → Y}
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    x + latticeVector n ∉ tsupport f := by
  intro h
  apply hn
  ext i
  have hi := hs h i
  simp only [PiLp.add_apply, latticeVector] at hi
  have hlo : (-1 : ℝ) < (n i : ℝ) := by linarith [(hx i).2]
  have hhi : (n i : ℝ) < 1 := by linarith [(hx i).1]
  have hνlo : (-1 : ℤ) < n i := by exact_mod_cast hlo
  have hνhi : n i < (1 : ℤ) := by exact_mod_cast hhi
  change n i = 0
  omega

lemma latticePeriodize_eventuallyEq {Y : Type*} [NormedAddCommGroup Y]
    {f : Cover → Y} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    latticePeriodize f =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨s, hlocal⟩ := finite_lattice_support_near hc x
  have hz (n : Fin 3 → ℤ) (hn : n ≠ 0) :
      ∀ᶠ y in 𝓝 x, f (y + latticeVector n) = 0 := by
    have h := notMem_tsupport_iff_eventuallyEq.mp (translate_not_mem_tsupport hs hx hn)
    exact h.comp_tendsto (continuous_id.add continuous_const).continuousAt
  have hfin : ∀ᶠ y in 𝓝 x, ∀ n ∈ s, n ≠ 0 → f (y + latticeVector n) = 0 := by
    apply (eventually_all_finset s).mpr
    intro n _
    by_cases hn : n = 0
    · exact Eventually.of_forall fun y h ↦ False.elim (h hn)
    · exact (hz n hn).mono fun y h _ ↦ h
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1), hfin] with y hy hz
  unfold latticePeriodize
  rw [tsum_eq_single (0 : Fin 3 → ℤ)]
  · simp only [latticeVector_zero, add_zero]
  · intro n hn
    by_cases hs : n ∈ s
    · exact hz n hs hn
    · exact hlocal y hy n hs

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma compactCell_coordinates (z : CompactCell) (i : Fin 3) :
    0 ≤ (z : Cover) i ∧ (z : Cover) i ≤ 1 := by
  obtain ⟨x, hx, he⟩ := z.property
  rw [← he]
  exact ⟨hx.1 i, hx.2 i⟩

lemma latticePeriodize_wall {F : Cover → Cover}
    (hs : tsupport F ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) (i : Fin 3) (x : Cover)
    (hx : x i = 0 ∨ x i = 1) : latticePeriodize F x i = 0 := by
  have he : latticePeriodize F x = 0 := by
    unfold latticePeriodize
    suffices hz : ∀ n : Fin 3 → ℤ, F (x + latticeVector n) = 0 by
      simp only [hz, tsum_zero]
    intro n
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hi := hs h i
    simp only [PiLp.add_apply, latticeVector] at hi
    rcases hx with hx | hx
    · rw [hx, zero_add] at hi
      have hlo : (0 : ℤ) < n i := by exact_mod_cast hi.1
      have hhi : n i < (1 : ℤ) := by exact_mod_cast hi.2
      omega
    · rw [hx] at hi
      have hlo : (-1 : ℤ) < n i := by exact_mod_cast (by linarith : (-1 : ℝ) < (n i : ℝ))
      have hhi : n i < (0 : ℤ) := by exact_mod_cast (by linarith : (n i : ℝ) < 0)
      omega
  rw [he]
  rfl

theorem weakCMC_local_identity {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle) := by
  have h := weakCMC_identity hμ hH (latticePeriodize_contDiff hF hc)
    (latticePeriodize_periodic F) (latticePeriodize_wall hs)
  have he (z : NormalBundle) := latticePeriodize_eventuallyEq hc hs (compactCell_coordinates z.1)
  have hval (z : NormalBundle) : latticePeriodize F z.1 = F z.1 := (he z).eq_of_nhds
  have hder (z : NormalBundle) : fderiv ℝ (latticePeriodize F) z.1 = fderiv ℝ F z.1 :=
    (he z).fderiv_eq
  simpa only [tangentialDivergence, divergence, hder, hval] using h

end CubicTorus

namespace CubicTorus

def coordinateBox (r : ℝ) : Set Torus :=
  {x | ∀ i : Fin 3, ((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ) < r}

lemma measurableSet_coordinateBox (r : ℝ) : MeasurableSet (coordinateBox r) := by
  simp only [coordinateBox, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_lt (measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (by fun_prop))) measurable_const

lemma coordinateBox_mono : Monotone coordinateBox := by
  intro r s hrs x hx i
  exact (hx i).trans_le hrs

lemma coordinateBox_zero : coordinateBox 0 = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro x hx
  have h := ((AddCircle.equivIco (1 : ℝ) 0) (x 0)).2.1
  exact (not_lt_of_ge h) (hx 0)

lemma coordinateBox_lift_preimage {r : ℝ} (hr : r ∈ Icc 0 1) :
    (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹'
      (fundamentalCube ∩ quotientMap ⁻¹' coordinateBox r) =
      univ.pi (fun _ : Fin 3 ↦ Ico 0 r) := by
  ext x
  change ((∀ i, 0 ≤ x i ∧ x i < 1) ∧
    (∀ i, ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) < r)) ↔ _
  constructor
  · rintro ⟨hc, hs⟩ i _
    have he : ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i :=
      AddCircle.equivIco_coe_of_mem (by simpa using hc i)
    exact ⟨(hc i).1, he ▸ hs i⟩
  · intro hx
    have hc : ∀ i, 0 ≤ x i ∧ x i < 1 := fun i ↦
      ⟨(hx i (mem_univ i)).1, (hx i (mem_univ i)).2.trans_le hr.2⟩
    refine ⟨hc, fun i ↦ ?_⟩
    rw [AddCircle.equivIco_coe_of_mem (by simpa using hc i)]
    exact (hx i (mem_univ i)).2

lemma volume_coordinateBox {r : ℝ} (hr : r ∈ Icc 0 1) :
    torusVolume (coordinateBox r) = ENNReal.ofReal (r ^ 3) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_coordinateBox r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_coordinateBox r)), inter_comm]
  have hm := (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    ((measurableSet_fundamentalCube.inter
      (measurable_quotientMap (measurableSet_coordinateBox r))).nullMeasurableSet)
  rw [coordinateBox_lift_preimage hr] at hm
  rw [← hm, Real.volume_pi_Ico]
  simp [← ENNReal.ofReal_pow hr.1, Finset.prod_const]

lemma integral_divergence_coordinateBox {r : ℝ} (hr : r ∈ Icc 0 1)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' coordinateBox r, divergence F x) =
      ∑ i : Fin 3, ((∫ x in Icc (0 : Fin 2 → ℝ) (fun _ ↦ r),
        F (WithLp.toLp 2 (i.insertNth r x)) i) -
      (∫ x in Icc (0 : Fin 2 → ℝ) (fun _ ↦ r),
        F (WithLp.toLp 2 (i.insertNth 0 x)) i)) := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  let g : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i x ↦ F (e.symm x) i
  let dg : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun i x ↦ (EuclideanSpace.proj i).comp
      ((fderiv ℝ F (e.symm x)).comp e.symm.toContinuousLinearMap)
  have hdg : ∀ i x, HasFDerivAt (g i) (dg i x) x := by
    intro i x
    exact (EuclideanSpace.proj i).hasFDerivAt.comp x
      (((hF.1.differentiable (by simp)) (e.symm x)).hasFDerivAt.comp x e.symm.hasFDerivAt)
  have hd : (fun x ↦ ∑ i : Fin 3, dg i x (Pi.single i 1)) =
      fun x ↦ divergence F (e.symm x) := by
    funext x
    simp [dg, divergence, e, PiLp.toLp_single]
  have hct : Continuous (fun x ↦ divergence F (e.symm x)) :=
    (continuous_divergence hF.1).comp e.symm.continuous
  have hth := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin 3 → ℝ) (fun _ ↦ r) (fun _ ↦ hr.1) g dg ∅ countable_empty
    (fun i ↦ ((EuclideanSpace.proj i).continuous.comp
      (hF.1.continuous.comp e.symm.continuous)).continuousOn)
    (fun x _ i ↦ hdg i x) (by rw [hd]; exact hct.integrableOn_Icc)
  rw [hd] at hth
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    e.symm.toHomeomorph.measurableEmbedding, coordinateBox_lift_preimage hr]
  rw [volume_pi, setIntegral_congr_set Measure.univ_pi_Ico_ae_eq_Icc, ← volume_pi]
  convert hth using 1 <;> simp [g, e, Function.comp_def, Pi.zero_def]

lemma box_face_flux_bound {r : ℝ} (hr : 0 ≤ r) {F : Cover → Cover}
    (hF : AdmissibleField F) (i : Fin 3) (a : ℝ) :
    |∫ x in Icc (0 : Fin 2 → ℝ) (fun _ ↦ r), F (WithLp.toLp 2 (i.insertNth a x)) i| ≤ r ^ 2 := by
  have hvol : volume (Icc (0 : Fin 2 → ℝ) (fun _ ↦ r)) = ENNReal.ofReal (r ^ 2) := by
    rw [Real.volume_Icc_pi]
    simp [← ENNReal.ofReal_pow hr, Finset.prod_const]
  have hh := norm_setIntegral_le_of_norm_le_const
    (show volume (Icc (0 : Fin 2 → ℝ) (fun _ ↦ r)) < ⊤ by rw [hvol]; exact ENNReal.ofReal_lt_top)
    (C := (1 : ℝ)) (f := fun x ↦ F (WithLp.toLp 2 (i.insertNth a x)) i) (fun x _ ↦
      (PiLp.norm_apply_le _ _).trans (hF.2.2 _))
  simpa [Real.norm_eq_abs, Measure.real, hvol, ENNReal.toReal_ofReal (sq_nonneg r)] using hh

theorem perimeter_coordinateBox_le {r : ℝ} (hr : r ∈ Icc 0 1) :
    perimeter (coordinateBox r) ≤ ENNReal.ofReal (6 * r ^ 2) := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply ENNReal.ofReal_le_ofReal
  rw [integral_divergence_coordinateBox hr hF]
  calc
    _ ≤ ∑ _i : Fin 3, (2 * r ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have ha := box_face_flux_bound hr.1 hF i r
      have hb := box_face_flux_bound hr.1 hF i 0
      linarith [(le_abs_self _).trans ha, (neg_le_abs _).trans hb]
    _ = _ := by simp; ring

theorem finitePerimeter_coordinateBox {r : ℝ} (hr : r ∈ Icc 0 1) :
    FinitePerimeter (coordinateBox r) :=
  ⟨(measurableSet_coordinateBox r).nullMeasurableSet,
    (perimeter_coordinateBox_le hr).trans_lt ENNReal.ofReal_lt_top⟩

end CubicTorus

namespace CubicTorus
open Filter

lemma representative_norm_le_box {r : ℝ} (hr : 0 ≤ r) {x : Torus}
    (hx : x ∈ coordinateBox r) : ‖representative x‖ ≤ 3 * r := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have hb (i : Fin 3) : ‖(representative x).ofLp i‖ ^ 2 ≤ r ^ 2 := by
    have h0 := ((AddCircle.equivIco (1 : ℝ) 0) (x i)).2.1
    have h1 := hx i
    change ‖((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ)‖ ^ 2 ≤ r ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦ hb i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  calc
    _ ≤ 3 * r ^ 2 := by exact_mod_cast hs
    _ ≤ (3 * r) ^ 2 := by nlinarith [sq_nonneg r]

theorem bv_cubical_isoperimetric {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) {r : ℝ} (hr : r ∈ Icc 0 1) :
    (torusVolume E).toReal * (r ^ 3 - (torusVolume E).toReal) ≤
      3 * r ^ 4 * (perimeter E).toReal := by
  let B := coordinateBox r
  let ν := torusVolume.restrict B
  let V := (torusVolume E).toReal
  let P := (perimeter E).toReal
  have hB : MeasurableSet B := measurableSet_coordinateBox r
  have hvol : ν.real univ = r ^ 3 := by
    simp only [ν, Measure.real, Measure.restrict_apply_univ, B, volume_coordinateBox hr,
      ENNReal.toReal_ofReal (pow_nonneg hr.1 3)]
  let g : Torus × Torus → ℝ := fun z ↦
    characteristic E z.1 * (1 - characteristic E (z.1 + z.2))
  have hgm : Measurable g := (measurable_characteristic hE |>.comp measurable_fst).mul
    (measurable_const.sub (measurable_characteristic hE |>.comp (measurable_fst.add measurable_snd)))
  have hgb (z : Torus × Torus) : |g z| ≤ 1 := by
    rcases characteristic_dichotomy E z.1 with h | h <;>
      rcases characteristic_dichotomy E (z.1 + z.2) with h' | h' <;> simp [g, h, h']
  have hgi : Integrable g (torusVolume.prod ν) :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall hgb)
  have hchi (x : Torus) : Integrable (fun a ↦ characteristic E (x + a)) torusVolume :=
    Integrable.of_bound ((measurable_characteristic hE).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable 1
        (Eventually.of_forall fun a ↦ characteristic_bound E (x + a))
  have hchiB (x : Torus) : (∫ a, characteristic E (x + a) ∂ν) ≤ V := by
    calc
      _ ≤ ∫ a, characteristic E (x + a) ∂torusVolume :=
        setIntegral_le_integral (hchi x) (Eventually.of_forall fun a ↦ characteristic_nonneg E _)
      _ = V := by rw [integral_add_left_eq_self, integral_characteristic hE.nullMeasurableSet]
  have hinner (x : Torus) : characteristic E x * (r ^ 3 - V) ≤ ∫ a, g (x, a) ∂ν := by
    change _ ≤ ∫ a, characteristic E x * (1 - characteristic E (x + a)) ∂ν
    rw [integral_const_mul, integral_sub (integrable_const _) (hchi x).integrableOn,
      integral_const, smul_eq_mul, mul_one, hvol]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left (hchiB x) _) (characteristic_nonneg E x)
  have hlow : V * (r ^ 3 - V) ≤ ∫ x, ∫ a, g (x, a) ∂ν ∂torusVolume := by
    calc
      _ = ∫ x, characteristic E x * (r ^ 3 - V) ∂torusVolume := by
        rw [integral_mul_const, integral_characteristic hE.nullMeasurableSet]
      _ ≤ _ := integral_mono ((integrable_characteristic hE).mul_const _) hgi.integral_prod_left hinner
  have hupper (a : Torus) : (∫ x, g (x, a) ∂torusVolume) ≤ ‖representative a‖ * P := by
    have hi : Integrable (fun x ↦ |characteristic E (x + a) - characteristic E x|) torusVolume := by
      apply Integrable.of_bound
        (((measurable_characteristic hE).comp (measurable_id.add_const a)).sub
          (measurable_characteristic hE)).abs.aestronglyMeasurable 1
      exact Eventually.of_forall fun x ↦ by
        rcases characteristic_dichotomy E (x + a) with h | h <;>
          rcases characteristic_dichotomy E x with h' | h' <;> simp [h, h']
    calc
      _ ≤ ∫ x, |characteristic E (x + a) - characteristic E x| ∂torusVolume := by
        apply integral_mono (Integrable.of_bound
          (hgm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
            (Eventually.of_forall fun x ↦ hgb (x, a))) hi
        intro x
        rcases characteristic_dichotomy E (x + a) with h | h <;>
          rcases characteristic_dichotomy E x with h' | h' <;> simp [g, h, h']
      _ ≤ _ := by simpa only [quotientMap_neg, quotientMap_representative, sub_neg_eq_add, norm_neg] using
        characteristic_translation_bound hE hP (-representative a)
  have hup : (∫ a, ∫ x, g (x, a) ∂torusVolume ∂ν) ≤ 3 * r ^ 4 * P := by
    calc
      _ ≤ ∫ a, (3 * r * P) ∂ν := by
        apply integral_mono_ae hgi.integral_prod_right (integrable_const _)
        filter_upwards [ae_restrict_mem hB] with a ha
        exact (hupper a).trans (mul_le_mul_of_nonneg_right
          (representative_norm_le_box hr.1 ha) ENNReal.toReal_nonneg)
      _ = _ := by rw [integral_const, smul_eq_mul, hvol]; ring
  exact hlow.trans ((integral_integral_swap hgi).le.trans hup)

end CubicTorus

namespace CubicTorus

end CubicTorus
end
end
end

end OAI
