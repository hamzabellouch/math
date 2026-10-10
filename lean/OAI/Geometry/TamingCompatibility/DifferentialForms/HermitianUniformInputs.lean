import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianSupportedSources

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (W : E → E →L[ℝ] E) (a ρ : E → ℝ) (V : E → E)
  (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hρ : ContDiff ℝ ∞ ρ) (hV : ContDiff ℝ ∞ V)

include hW hρ in

lemma logShellSchwartz_uniform_inputs {K : Set E} (hK : IsCompact K) (R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ∀ hr : r ∈ Ioc (0:ℝ) R, ∀ s, ∀ hs : s ∈ Ioc (0:ℝ) r, ∀ b ∈ K,
      (∀ z, |logShellSchwartz W a V ha hV hr.1 hs.1 b z| ≤ C/r) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z => ρ z * logShellSchwartz W a V ha hV hr.1 hs.1 b z) z‖ ≤ (C/r)/(5*r)^n) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedLogShell_derivatives_bounded W a V hW ha hV hK R 0
  choose D hD hb using fun n => shiftedLogShell_derivatives_bounded W a
    (fun w => ρ w • V w) hW ha (hρ.smul hV) hK R n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro r hr s hs b hbK
  constructor
  · intro z
    have h := hb₀ r hr s ⟨hs.1.le,hs.2⟩ b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,zero_add,pow_one] at h
    exact h.trans (by simpa using div_le_div_of_nonneg_right hC₀ (show 0 ≤ r from hr.1.le))
  · intro n hn z
    have he : (fun z => ρ z * logShellSchwartz W a V ha hV hr.1 hs.1 b z) =
        shiftedLogShell W a (fun w => ρ w • V w) r s b :=
      funext (shiftedLogShell_weight W a ρ V r s b)
    rw [he]
    have h := hb n r hr s ⟨hs.1.le,hs.2⟩ b hbK z
    apply h.trans
    simpa only [add_zero,pow_zero,pow_one,div_one] using radialJet_rescale
      (hr.1) n 1 (hCD n hn)

include hW hρ in

lemma logInnerSchwartz_uniform_inputs {K : Set E} (hK : IsCompact K) (R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hs : s ∈ Ioc (0:ℝ) R, ∀ b ∈ K,
      (∀ z, |logInnerSchwartz W a V ha hV hs.1 b z| ≤ C/s) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z => ρ z * logInnerSchwartz W a V ha hV hs.1 b z) z‖ ≤ (C/s)/(5*s)^n) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedLogInner_derivatives_bounded W a V hW ha hV hK R 0
  choose D hD hb using fun n => shiftedLogInner_derivatives_bounded W a
    (fun w => ρ w • V w) hW ha (hρ.smul hV) hK R n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro s hs b hbK
  constructor
  · intro z
    have h := hb₀ s hs b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,zero_add,pow_one] at h
    exact h.trans (by simpa using div_le_div_of_nonneg_right hC₀ (show 0 ≤ s from hs.1.le))
  · intro n hn z
    have he : (fun z => ρ z * logInnerSchwartz W a V ha hV hs.1 b z) =
        shiftedLogInner W a (fun w => ρ w • V w) s b :=
      funext (shiftedLogInner_weight W a ρ V s b)
    rw [he]
    have h := hb n s hs b hbK z
    apply h.trans
    simpa only [add_zero,pow_zero,pow_one,div_one] using radialJet_rescale
      (hs.1) n 1 (hCD n hn)

include hW hρ in

lemma sqrtShellSchwartz_uniform_inputs {K : Set E} (hK : IsCompact K) (R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ∀ hr : r ∈ Ioc (0:ℝ) R, ∀ s, ∀ hs : s ∈ Ioc (0:ℝ) r, ∀ b ∈ K,
      (∀ z, |sqrtShellSchwartz W a V ha hV hr.1 hs.1 b z| ≤ C) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z => ρ z * sqrtShellSchwartz W a V ha hV hr.1 hs.1 b z) z‖ ≤ (C)/(5*r)^n) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedSqrtShell_derivatives_bounded W a V hW ha hV hK R 0
  choose D hD hb using fun n => shiftedSqrtShell_derivatives_bounded W a
    (fun w => ρ w • V w) hW ha (hρ.smul hV) hK R n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro r hr s hs b hbK
  constructor
  · intro z
    have h := hb₀ r hr s ⟨hs.1.le,hs.2⟩ b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one] at h
    exact h.trans (by exact hC₀)
  · intro n hn z
    have he : (fun z => ρ z * sqrtShellSchwartz W a V ha hV hr.1 hs.1 b z) =
        shiftedSqrtShell W a (fun w => ρ w • V w) r s b :=
      funext (shiftedSqrtShell_weight W a ρ V r s b)
    rw [he]
    have h := hb n r hr s ⟨hs.1.le,hs.2⟩ b hbK z
    apply h.trans
    simpa only [add_zero,pow_zero,pow_one,div_one] using radialJet_rescale
      (hr.1) n 0 (hCD n hn)

include hW hρ in

lemma sqrtInnerSchwartz_uniform_inputs {K : Set E} (hK : IsCompact K) (R : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hs : s ∈ Ioc (0:ℝ) R, ∀ b ∈ K,
      (∀ z, |sqrtInnerSchwartz W a V ha hV hs.1 b z| ≤ C) ∧
      (∀ n ≤ N, ∀ z, ‖iteratedFDeriv ℝ n
        (fun z => ρ z * sqrtInnerSchwartz W a V ha hV hs.1 b z) z‖ ≤ (C)/(5*s)^n) := by
  classical
  obtain ⟨D₀,hD₀,hb₀⟩ := shiftedSqrtInner_derivatives_bounded W a V hW ha hV hK R 0
  choose D hD hb using fun n => shiftedSqrtInner_derivatives_bounded W a
    (fun w => ρ w • V w) hW ha (hρ.smul hV) hK R n
  obtain ⟨C,hC,hC₀,hCD⟩ := finite_radialJet_constant D hD D₀ hD₀ N
  refine ⟨C,hC,?_⟩
  intro s hs b hbK
  constructor
  · intro z
    have h := hb₀ s hs b hbK z
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one] at h
    exact h.trans (by exact hC₀)
  · intro n hn z
    have he : (fun z => ρ z * sqrtInnerSchwartz W a V ha hV hs.1 b z) =
        shiftedSqrtInner W a (fun w => ρ w • V w) s b :=
      funext (shiftedSqrtInner_weight W a ρ V s b)
    rw [he]
    have h := hb n s hs b hbK z
    apply h.trans
    simpa only [add_zero,pow_zero,pow_one,div_one] using radialJet_rescale
      (hs.1) n 0 (hCD n hn)

end TamingCompatibility.HermitianRadial

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hD hH hweak hB hdual in

theorem scalarCorrection_logShell_estimates
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (a : Space → ℝ) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ r, ∀ hr : r ∈ Ioc (0:ℝ) R, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) r, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.logShellSupported W a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))‖ ≤ C/r ∧
      ∀ t ∈ Ioo (0:ℝ) δ, 5*r+c*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.logShellSupported W a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))‖ ≤ C*r^2/t^3 := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_all_scales A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq
  obtain ⟨E,hE,hinput⟩ := HermitianRadial.logShellSchwartz_uniform_inputs W a ρ V hW ha
    (ρ.smooth ⊤) hV hK₀ R 3
  refine ⟨δ,hδ,hδ1,c,hc,125*C*E,by positivity,?_⟩
  intro y hy r hr s hsr b hb
  have hr0 : 0 < r := hr.1
  let φ := HermitianRadial.logShellSupported W a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb)
  have hin := hinput r hr s hsr b hb
  have hball : tsupport φ.val ⊆ Metric.ball b (5*r) :=
    (HermitianRadial.shiftedLogShell_support W a V hr.1 s b).trans
      (Metric.closedBall_subset_ball (by linarith [hr.1] : 4*r < 5*r))
  have hM : 0 ≤ E/r := by positivity
  constructor
  · have hnear := (hest y hy).1 (5*r) (by positivity) φ j b (E/r) hM hball hin.1 hin.2
    apply hnear.trans
    have he : C*(E/r) = C*E/r := by ring
    rw [he]
    exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hC hE]) hr.1.le
  · intro t ht hsep
    have hoff := (hest y hy).2 t ht φ j b (5*r) (E/r) (by positivity) hM hball hin.1 hsep
    apply hoff.trans_eq
    field_simp [hr.1.ne' ]
    ring

include hD hH hweak hB hdual in

theorem scalarCorrection_logInner_estimates
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (a : Space → ℝ) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.logInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C/s ∧
      ∀ t ∈ Ioo (0:ℝ) δ, 5*s+c*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.logInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C*s^2/t^3 := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_all_scales A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq
  obtain ⟨E,hE,hinput⟩ := HermitianRadial.logInnerSchwartz_uniform_inputs W a ρ V hW ha
    (ρ.smooth ⊤) hV hK₀ R 3
  refine ⟨δ,hδ,hδ1,c,hc,125*C*E,by positivity,?_⟩
  intro y hy s hsr b hb
  have hs0 : 0 < s := hsr.1
  let φ := HermitianRadial.logInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb)
  have hin := hinput s hsr b hb
  have hball : tsupport φ.val ⊆ Metric.ball b (5*s) :=
    (HermitianRadial.shiftedLogInner_support W a V hsr.1 b).trans
      (Metric.closedBall_subset_ball (by linarith [hsr.1] : 2*s < 5*s))
  have hM : 0 ≤ E/s := by positivity
  constructor
  · have hnear := (hest y hy).1 (5*s) (by positivity) φ j b (E/s) hM hball hin.1 hin.2
    apply hnear.trans
    have he : C*(E/s) = C*E/s := by ring
    rw [he]
    exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hC hE]) hsr.1.le
  · intro t ht hsep
    have hoff := (hest y hy).2 t ht φ j b (5*s) (E/s) (by positivity) hM hball hin.1 hsep
    apply hoff.trans_eq
    field_simp [hsr.1.ne' ]
    ring

include hD hH hweak hB hdual in

theorem scalarCorrection_sqrtShell_estimates
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (a : Space → ℝ) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ r, ∀ hr : r ∈ Ioc (0:ℝ) R, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) r, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtShellSupported W a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))‖ ≤ C ∧
      ∀ t ∈ Ioo (0:ℝ) δ, 5*r+c*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtShellSupported W a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))‖ ≤ C*r^3/t^3 := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_all_scales A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq
  obtain ⟨E,hE,hinput⟩ := HermitianRadial.sqrtShellSchwartz_uniform_inputs W a ρ V hW ha
    (ρ.smooth ⊤) hV hK₀ R 3
  refine ⟨δ,hδ,hδ1,c,hc,125*C*E,by positivity,?_⟩
  intro y hy r hr s hsr b hb
  have hr0 : 0 < r := hr.1
  let φ := HermitianRadial.sqrtShellSupported W a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb)
  have hin := hinput r hr s hsr b hb
  have hball : tsupport φ.val ⊆ Metric.ball b (5*r) :=
    (HermitianRadial.shiftedSqrtShell_support W a V hr.1 s b).trans
      (Metric.closedBall_subset_ball (by linarith [hr.1] : 4*r < 5*r))
  have hM : 0 ≤ E := by positivity
  constructor
  · have hnear := (hest y hy).1 (5*r) (by positivity) φ j b (E) hM hball hin.1 hin.2
    apply hnear.trans
    nlinarith [mul_nonneg hC hE]
  · intro t ht hsep
    have hoff := (hest y hy).2 t ht φ j b (5*r) (E) (by positivity) hM hball hin.1 hsep
    apply hoff.trans_eq
    ring

include hD hH hweak hB hdual in

theorem scalarCorrection_sqrtInner_estimates
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (a : Space → ℝ) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C ∧
      ∀ t ∈ Ioo (0:ℝ) δ, 5*s+c*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C*s^3/t^3 := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_all_scales A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq
  obtain ⟨E,hE,hinput⟩ := HermitianRadial.sqrtInnerSchwartz_uniform_inputs W a ρ V hW ha
    (ρ.smooth ⊤) hV hK₀ R 3
  refine ⟨δ,hδ,hδ1,c,hc,125*C*E,by positivity,?_⟩
  intro y hy s hsr b hb
  have hs0 : 0 < s := hsr.1
  let φ := HermitianRadial.sqrtInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb)
  have hin := hinput s hsr b hb
  have hball : tsupport φ.val ⊆ Metric.ball b (5*s) :=
    (HermitianRadial.shiftedSqrtInner_support W a V hsr.1 b).trans
      (Metric.closedBall_subset_ball (by linarith [hsr.1] : 2*s < 5*s))
  have hM : 0 ≤ E := by positivity
  constructor
  · have hnear := (hest y hy).1 (5*s) (by positivity) φ j b (E) hM hball hin.1 hin.2
    apply hnear.trans
    nlinarith [mul_nonneg hC hE]
  · intro t ht hsep
    have hoff := (hest y hy).2 t ht φ j b (5*s) (E) (by positivity) hM hball hin.1 hsep
    apply hoff.trans_eq
    ring

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
