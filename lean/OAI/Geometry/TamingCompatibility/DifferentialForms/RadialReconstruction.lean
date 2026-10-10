import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialFixedJet
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialJetConstants

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (a : E → ℝ) (V : E → E) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
  (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R)

def logSourceSchwartz {s : ℝ} (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedLogSource a V s b) :=
    (isCompact_closedBall b R).of_isClosed_subset (isClosed_tsupport _)
      (shiftedLogSource_support a V s b R haR)
  exact hc.toSchwartzMap (shiftedLogSource_smooth a V ha hV hs b)

def sqrtSourceSchwartz {s : ℝ} (hs : 0 < s) (b : E) : 𝓢(E,ℝ) := by
  have hc : HasCompactSupport (shiftedSqrtSource a V s b) :=
    (isCompact_closedBall b R).of_isClosed_subset (isClosed_tsupport _)
      (shiftedSqrtSource_support a V s b R haR)
  exact hc.toSchwartzMap (shiftedSqrtSource_smooth a V ha hV hs b)

lemma logSourceSchwartz_reconstruction {s : ℝ} (hs : 0 < s) (b : E)
    (N : ℕ) (hN : R ≤ s*2^N) :
    logSourceSchwartz a V ha hV R haR hs b = logInnerSchwartz a V ha hV hs b +
    ∑ j ∈ Finset.range N, logShellSchwartz a V ha hV (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b := by
  apply SchwartzMap.ext
  intro z
  change shiftedLogSource a V s b z = shiftedLogInner a V s b z +
    (∑ j ∈ Finset.range N, logShellSchwartz a V ha hV (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b) z
  rw [sum_apply]
  change shiftedLogSource a V s b z = scaledCutoff s (z-b) * shiftedLogSource a V s b z +
    ∑ j ∈ Finset.range N, shellCutoff (s*2^j) (z-b) * shiftedLogSource a V s b z
  rw [← Finset.sum_mul,← add_mul,dyadic_cutoff_telescope]
  by_cases hz : ‖z-b‖ ≤ s*2^N
  · rw [scaledCutoff_one (mul_pos hs (by positivity)) hz,one_mul]
  · have ha0 : a (z-b) = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
      have hh := haR h
      simp only [mem_closedBall,dist_zero_right] at hh
      exact hz (hh.trans hN))
    simp [shiftedLogSource,logSingularSource,ha0]

lemma sqrtSourceSchwartz_reconstruction {s : ℝ} (hs : 0 < s) (b : E)
    (N : ℕ) (hN : R ≤ s*2^N) :
    sqrtSourceSchwartz a V ha hV R haR hs b = sqrtInnerSchwartz a V ha hV hs b +
    ∑ j ∈ Finset.range N, sqrtShellSchwartz a V ha hV (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b := by
  apply SchwartzMap.ext
  intro z
  change shiftedSqrtSource a V s b z = shiftedSqrtInner a V s b z +
    (∑ j ∈ Finset.range N, sqrtShellSchwartz a V ha hV (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b) z
  rw [sum_apply]
  change shiftedSqrtSource a V s b z = scaledCutoff s (z-b) * shiftedSqrtSource a V s b z +
    ∑ j ∈ Finset.range N, shellCutoff (s*2^j) (z-b) * shiftedSqrtSource a V s b z
  rw [← Finset.sum_mul,← add_mul,dyadic_cutoff_telescope]
  by_cases hz : ‖z-b‖ ≤ s*2^N
  · rw [scaledCutoff_one (mul_pos hs (by positivity)) hz,one_mul]
  · have ha0 : a (z-b) = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
      have hh := haR h
      simp only [mem_closedBall,dist_zero_right] at hh
      exact hz (hh.trans hN))
    simp [shiftedSqrtSource,sqrtSingularSource,ha0]

end TamingCompatibility.RadialPotential

end
end

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]
variable (a : E → ℝ) (V : E → E) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
  (R : ℝ) (haR : tsupport a ⊆ closedBall 0 R) (K : Set E)

def logShellSupported {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨logShellSchwartz a V ha hV hr hs b,(logShellSchwartz_fixedSupport a V ha hV hr hs b R haR).trans hb⟩

def logInnerSupported {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨logInnerSchwartz a V ha hV hs b,(logInnerSchwartz_fixedSupport a V ha hV hs b R haR).trans hb⟩

def logSourceSupported {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨logSourceSchwartz a V ha hV R haR hs b,(shiftedLogSource_support a V s b R haR).trans hb⟩

lemma logSupported_reconstruction {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K)
    (N : ℕ) (hN : R ≤ s*2^N) :
    logSourceSupported a V ha hV R haR K hs b hb =
      logInnerSupported a V ha hV R haR K hs b hb +
      ∑ j ∈ Finset.range N, logShellSupported a V ha hV R haR K
        (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b hb := by
  apply Subtype.ext
  simpa only [Submodule.coe_add,Submodule.coe_sum,logSourceSupported,logInnerSupported,logShellSupported] using
    logSourceSchwartz_reconstruction a V ha hV R haR hs b N hN

def sqrtShellSupported {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨sqrtShellSchwartz a V ha hV hr hs b,(sqrtShellSchwartz_fixedSupport a V ha hV hr hs b R haR).trans hb⟩

def sqrtInnerSupported {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨sqrtInnerSchwartz a V ha hV hs b,(sqrtInnerSchwartz_fixedSupport a V ha hV hs b R haR).trans hb⟩

def sqrtSourceSupported {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K) :
    supportedSchwartz K :=
  ⟨sqrtSourceSchwartz a V ha hV R haR hs b,(shiftedSqrtSource_support a V s b R haR).trans hb⟩

lemma sqrtSupported_reconstruction {s : ℝ} (hs : 0 < s) (b : E) (hb : closedBall b R ⊆ K)
    (N : ℕ) (hN : R ≤ s*2^N) :
    sqrtSourceSupported a V ha hV R haR K hs b hb =
      sqrtInnerSupported a V ha hV R haR K hs b hb +
      ∑ j ∈ Finset.range N, sqrtShellSupported a V ha hV R haR K
        (mul_pos hs (by positivity : 0 < (2:ℝ)^j)) hs b hb := by
  apply Subtype.ext
  simpa only [Submodule.coe_add,Submodule.coe_sum,sqrtSourceSupported,sqrtInnerSupported,sqrtShellSupported] using
    sqrtSourceSchwartz_reconstruction a V ha hV R haR hs b N hN

end TamingCompatibility.RadialPotential

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
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
    (a : Space → ℝ) (V : Space → Space) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ r, ∀ hr : r ∈ Ioc (0:ℝ) R, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) r, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (logShellSupported a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))‖ ≤ C/r ∧
      ∀ t ∈ Ioo (0:ℝ) δ, 5*r+c*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (logShellSupported a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))‖ ≤ C*r^2/t^3 := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_all_scales A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq
  obtain ⟨E,hE,hinput⟩ := logShellSchwartz_uniform_inputs a ρ V ha
    (ρ.smooth ⊤) hV hK₀ R 3
  refine ⟨δ,hδ,hδ1,c,hc,125*C*E,by positivity,?_⟩
  intro y hy r hr s hsr b hb
  have hr0 : 0 < r := hr.1
  let φ := logShellSupported a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb)
  have hin := hinput r hr s hsr b hb
  have hball : tsupport φ.val ⊆ Metric.ball b (5*r) :=
    (shiftedLogShell_support a V hr.1 s b).trans
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
    (a : Space → ℝ) (V : Space → Space) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (logInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C/s ∧
      ∀ t ∈ Ioo (0:ℝ) δ, 5*s+c*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (logInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C*s^2/t^3 := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_all_scales A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq
  obtain ⟨E,hE,hinput⟩ := logInnerSchwartz_uniform_inputs a ρ V ha
    (ρ.smooth ⊤) hV hK₀ R 3
  refine ⟨δ,hδ,hδ1,c,hc,125*C*E,by positivity,?_⟩
  intro y hy s hsr b hb
  have hs0 : 0 < s := hsr.1
  let φ := logInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb)
  have hin := hinput s hsr b hb
  have hball : tsupport φ.val ⊆ Metric.ball b (5*s) :=
    (shiftedLogInner_support a V hsr.1 b).trans
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
    (a : Space → ℝ) (V : Space → Space) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ r, ∀ hr : r ∈ Ioc (0:ℝ) R, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) r, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (sqrtShellSupported a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))‖ ≤ C ∧
      ∀ t ∈ Ioo (0:ℝ) δ, 5*r+c*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (sqrtShellSupported a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb))‖ ≤ C*r^3/t^3 := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_all_scales A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq
  obtain ⟨E,hE,hinput⟩ := sqrtShellSchwartz_uniform_inputs a ρ V ha
    (ρ.smooth ⊤) hV hK₀ R 3
  refine ⟨δ,hδ,hδ1,c,hc,125*C*E,by positivity,?_⟩
  intro y hy r hr s hsr b hb
  have hr0 : 0 < r := hr.1
  let φ := sqrtShellSupported a V ha hV R haR K hr.1 hsr.1 b (hcenters b hb)
  have hin := hinput r hr s hsr b hb
  have hball : tsupport φ.val ⊆ Metric.ball b (5*r) :=
    (shiftedSqrtShell_support a V hr.1 s b).trans
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
    (a : Space → ℝ) (V : Space → Space) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (sqrtInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C ∧
      ∀ t ∈ Ioo (0:ℝ) δ, 5*s+c*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (sqrtInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C*s^3/t^3 := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_all_scales A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq
  obtain ⟨E,hE,hinput⟩ := sqrtInnerSchwartz_uniform_inputs a ρ V ha
    (ρ.smooth ⊤) hV hK₀ R 3
  refine ⟨δ,hδ,hδ1,c,hc,125*C*E,by positivity,?_⟩
  intro y hy s hsr b hb
  have hs0 : 0 < s := hsr.1
  let φ := sqrtInnerSupported a V ha hV R haR K hsr.1 b (hcenters b hb)
  have hin := hinput s hsr b hb
  have hball : tsupport φ.val ⊆ Metric.ball b (5*s) :=
    (shiftedSqrtInner_support a V hsr.1 b).trans
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

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
