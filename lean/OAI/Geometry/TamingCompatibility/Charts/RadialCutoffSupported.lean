import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialObserverScale
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialErrorEstimates

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

def translatedCutoffLog (R s : ℝ) (b z : E) : ℝ := cutoffLogPotential R s (z-b)
def translatedCutoffSqrt (R s : ℝ) (b z : E) : ℝ := cutoffSqrtPotential R s (z-b)

omit [ProperSpace E] in
lemma translatedCutoffLog_smooth (R : ℝ) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (translatedCutoffLog R s b) :=
  (cutoffLogPotential_smooth R hs).comp (contDiff_id.sub contDiff_const)
omit [ProperSpace E] in
lemma translatedCutoffSqrt_smooth (R : ℝ) {s : ℝ} (hs : 0 < s) (b : E) :
    ContDiff ℝ ∞ (translatedCutoffSqrt R s b) :=
  (cutoffSqrtPotential_smooth R hs).comp (contDiff_id.sub contDiff_const)
omit [ProperSpace E] in
lemma translatedCutoffLog_support {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    tsupport (translatedCutoffLog R s b) ⊆ closedBall b (2*R) :=
  tsupport_translated_subset b _ (cutoffLogPotential_tsupport hR s)
omit [ProperSpace E] in
lemma translatedCutoffSqrt_support {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    tsupport (translatedCutoffSqrt R s b) ⊆ closedBall b (2*R) :=
  tsupport_translated_subset b _ (cutoffSqrtPotential_tsupport hR s)

lemma translatedCutoffLog_compact {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    HasCompactSupport (translatedCutoffLog R s b) :=
  (isCompact_closedBall b (2*R)).of_isClosed_subset (isClosed_tsupport _)
    (translatedCutoffLog_support hR s b)
lemma translatedCutoffSqrt_compact {R : ℝ} (hR : 0 < R) (s : ℝ) (b : E) :
    HasCompactSupport (translatedCutoffSqrt R s b) :=
  (isCompact_closedBall b (2*R)).of_isClosed_subset (isClosed_tsupport _)
    (translatedCutoffSqrt_support hR s b)

omit [ProperSpace E] in
lemma firstOrderSource_translatedCutoffLog (V : E → E) (R : ℝ) {s : ℝ}
    (hs : 0 < s) (b z : E) :
    firstOrderSource V (translatedCutoffLog R s b) z =
      shiftedLogSource (scaledCutoff R) V s b z + shiftedLogError V R s b z := by
  change fderiv ℝ (fun z => cutoffLogPotential R s (z-b)) z (V z) = _
  rw [fderiv_comp_sub]
  simpa [firstOrderSource,shiftedLogSource,logSingularSource,shiftedLogError,cutoffLogError] using
    firstOrderSource_cutoffLog (fun w => V (b+w)) R hs (z-b)
omit [ProperSpace E] in
lemma firstOrderSource_translatedCutoffSqrt (V : E → E) (R : ℝ) {s : ℝ}
    (hs : 0 < s) (b z : E) :
    firstOrderSource V (translatedCutoffSqrt R s b) z =
      shiftedSqrtSource (scaledCutoff R) V s b z + shiftedSqrtError V R s b z := by
  change fderiv ℝ (fun z => cutoffSqrtPotential R s (z-b)) z (V z) = _
  rw [fderiv_comp_sub]
  simpa [firstOrderSource,shiftedSqrtSource,sqrtSingularSource,shiftedSqrtError,cutoffSqrtError] using
    firstOrderSource_cutoffSqrt (fun w => V (b+w)) R hs (z-b)

variable (V : E → E) (hV : ContDiff ℝ ∞ V) {R s : ℝ} (hR : 0 < R) (hs : 0 < s)

def logCutoffSourceSupported (K : Set E) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    supportedSchwartz K := by
  let f := firstOrderSource V (translatedCutoffLog R s b)
  have hf : ContDiff ℝ ∞ f := firstOrderSource_smooth V hV _ (translatedCutoffLog_smooth R hs b)
  have hc : HasCompactSupport f := (translatedCutoffLog_compact hR s b).of_isClosed_subset
    (isClosed_tsupport _) (firstOrderSource_tsupport _ _)
  exact ⟨hc.toSchwartzMap hf, ((firstOrderSource_tsupport _ _).trans
    (translatedCutoffLog_support hR s b)).trans hb⟩
def sqrtCutoffSourceSupported (K : Set E) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    supportedSchwartz K := by
  let f := firstOrderSource V (translatedCutoffSqrt R s b)
  have hf : ContDiff ℝ ∞ f := firstOrderSource_smooth V hV _ (translatedCutoffSqrt_smooth R hs b)
  have hc : HasCompactSupport f := (translatedCutoffSqrt_compact hR s b).of_isClosed_subset
    (isClosed_tsupport _) (firstOrderSource_tsupport _ _)
  exact ⟨hc.toSchwartzMap hf, ((firstOrderSource_tsupport _ _).trans
    (translatedCutoffSqrt_support hR s b)).trans hb⟩

lemma logCutoffSourceSupported_eq (K : Set E) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    logCutoffSourceSupported V hV hR hs K b hb =
      logSourceSupported (scaledCutoff R) V (scaledCutoff_smooth R) hV
        (2*R) (scaledCutoff_tsupport hR) K hs b hb + logErrorSupported V hV hR K s b hb := by
  apply Subtype.ext
  ext z
  exact firstOrderSource_translatedCutoffLog V R hs b z
lemma sqrtCutoffSourceSupported_eq (K : Set E) (b : E) (hb : closedBall b (2*R) ⊆ K) :
    sqrtCutoffSourceSupported V hV hR hs K b hb =
      sqrtSourceSupported (scaledCutoff R) V (scaledCutoff_smooth R) hV
        (2*R) (scaledCutoff_tsupport hR) K hs b hb + sqrtErrorSupported V hV hR K s b hb := by
  apply Subtype.ext
  ext z
  exact firstOrderSource_translatedCutoffSqrt V R hs b z

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

theorem scalarCorrection_cutoffLog_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (logCutoffSourceSupported V hV hR hsr.1 K b (hcenters b hb))‖ ≤ C/(s+dist b y) := by
  obtain ⟨δ₁,hδ₁,C₁,hC₁,hsource⟩ :=
    scalarCorrection_logSource_distance_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j (scaledCutoff R) V (scaledCutoff_smooth R) hV
      (2*R) (scaledCutoff_tsupport hR) K₀ hK₀ hcenters
  obtain ⟨δ₂,hδ₂,C₂,hC₂,herror⟩ :=
    scalarCorrection_logError_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j V hV R hR (2*R) K₀ hK₀ hcenters
  obtain ⟨M,hM,hKM⟩ := hK₀.isBounded.subset_ball_lt 0 q
  let δ := min (min δ₁ δ₂) 1
  refine ⟨δ,lt_min (lt_min hδ₁ hδ₂) (by norm_num),C₁+C₂*(2*R+M+1),by positivity,?_⟩
  intro y hy s hsr b hb
  have hy₁ : y ∈ Metric.ball q δ₁ := (show dist y q < δ from hy).trans_le
    ((min_le_left _ _).trans (min_le_left _ _))
  have hy₂ : y ∈ Metric.ball q δ₂ := (show dist y q < δ from hy).trans_le
    ((min_le_left _ _).trans (min_le_right _ _))
  have hdM : s+dist b y ≤ 2*R+M+1 := by
    have hbM : dist b q < M := hKM hb
    have hy1 : dist q y ≤ 1 := by simpa only [dist_comm] using
      (show dist y q < δ from hy).le.trans (min_le_right _ _)
    linarith [dist_triangle b q y,hsr.2]
  have hden : 0 < s+dist b y := add_pos_of_pos_of_nonneg hsr.1 dist_nonneg
  rw [logCutoffSourceSupported_eq,map_add]
  apply (norm_add_le _ _).trans
  apply (add_le_add (hsource y hy₁ s hsr b hb) (herror y hy₂ s ⟨hsr.1.le,hsr.2⟩ b hb)).trans
  apply (le_div_iff₀ hden).mpr
  calc
    _ = C₁+C₂*(s+dist b y) := by field_simp
    _ ≤ _ := add_le_add (le_refl C₁) (mul_le_mul_of_nonneg_left hdM hC₂)

include hD hH hweak hB hdual in

theorem scalarCorrection_cutoffSqrt_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) (hR1 : 2*R ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (sqrtCutoffSourceSupported V hV hR hsr.1 K b (hcenters b hb))‖ ≤ C*(1+|Real.log (s+dist b y)|) := by
  obtain ⟨δ₁,hδ₁,C₁,hC₁,hsource⟩ :=
    scalarCorrection_sqrtSource_distance_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j (scaledCutoff R) V (scaledCutoff_smooth R) hV
      (2*R) (scaledCutoff_tsupport hR) K₀ hK₀ hcenters hR1
  obtain ⟨δ₂,hδ₂,C₂,hC₂,herror⟩ :=
    scalarCorrection_sqrtError_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j V hV R hR (2*R) K₀ hK₀ hcenters
  let δ := min (min δ₁ δ₂) 1
  refine ⟨δ,lt_min (lt_min hδ₁ hδ₂) (by norm_num),C₁+C₂,by positivity,?_⟩
  intro y hy s hsr b hb
  have hy₁ : y ∈ Metric.ball q δ₁ := (show dist y q < δ from hy).trans_le
    ((min_le_left _ _).trans (min_le_left _ _))
  have hy₂ : y ∈ Metric.ball q δ₂ := (show dist y q < δ from hy).trans_le
    ((min_le_left _ _).trans (min_le_right _ _))
  rw [sqrtCutoffSourceSupported_eq,map_add]
  apply (norm_add_le _ _).trans
  apply (add_le_add (hsource y hy₁ s hsr b hb) (herror y hy₂ s ⟨hsr.1.le,hsr.2⟩ b hb)).trans
  nlinarith [mul_nonneg hC₂ (abs_nonneg (Real.log (s+dist b y)))]

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
