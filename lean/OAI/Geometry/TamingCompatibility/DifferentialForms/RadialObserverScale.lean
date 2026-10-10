import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialMixedLogDyadic

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential

def observerScale (δ c d : ℝ) : ℝ := min (δ/2) (d/(5+c))

lemma observerScale_properties {δ c d D : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hd : 0 ≤ d) (hdD : d ≤ D) :
    0 ≤ observerScale δ c d ∧ observerScale δ c d < δ ∧
    (5+c)*observerScale δ c d ≤ d ∧
    1 ≤ max (5+c) (2*D/δ) ∧ d ≤ max (5+c) (2*D/δ)*observerScale δ c d := by
  have hc5 : 0 < 5+c := by linarith
  have hC : 1 ≤ max (5+c) (2*D/δ) := (by linarith : (1:ℝ) ≤ 5+c).trans (le_max_left _ _)
  have ht0 : 0 ≤ observerScale δ c d := le_min (by positivity) (by positivity)
  refine ⟨ht0,(min_le_left _ _).trans_lt (by linarith),?_,hC,?_⟩
  · calc
      _ ≤ (5+c)*(d/(5+c)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hc5.le
      _ = d := by field_simp
  · unfold observerScale
    by_cases h : δ/2 ≤ d/(5+c)
    · rw [min_eq_left h]
      calc
        d ≤ D := hdD
        _ = (2*D/δ)*(δ/2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    · rw [min_eq_right (le_of_not_ge h)]
      calc
        d = (5+c)*(d/(5+c)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

lemma observerScale_le_dist {δ c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) :
    observerScale δ c d ≤ d := by
  apply (min_le_right _ _).trans
  exact div_le_self hd (by linarith)

lemma inverse_observer_to_distance {s t d L C : ℝ} (hs : 0 < s)
    (ht : 0 ≤ t) (hd : 0 ≤ d) (hL : 1 ≤ L) (hdt : d ≤ L*t) (hC : 0 ≤ C) :
    C/(s+t) ≤ (C*L)/(s+d) := by
  apply (div_le_div_iff₀ (by positivity : 0 < s+t) (by positivity : 0 < s+d)).mpr
  have hsL : s ≤ L*s := by nlinarith
  have he : s+d ≤ L*(s+t) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left he hC]

lemma log_abs_comparison {u v L : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hvLu : v ≤ L*u) (hL : 1 ≤ L) :
    |Real.log u| ≤ |Real.log v|+Real.log L := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hv : 0 < v := hu.trans_le huv
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have h1 : Real.log u ≤ Real.log v := Real.log_le_log hu huv
  have h2 : Real.log v ≤ Real.log L+Real.log u := by
    simpa only [Real.log_mul hL0.ne' hu.ne'] using Real.log_le_log hv hvLu
  apply abs_le.mpr
  constructor
  · linarith [neg_le_abs (Real.log v)]
  · linarith [le_abs_self (Real.log v)]

lemma log_observer_to_distance {s t d L C : ℝ} (hs : 0 < s)
    (ht : 0 ≤ t) (htd : t ≤ d) (hL : 1 ≤ L) (hdt : d ≤ L*t) (hC : 0 ≤ C) :
    C*(10+|Real.log (max s t)|/Real.log 2) ≤
      (C*(10+Real.log (2*L)/Real.log 2+1/Real.log 2))*(1+|Real.log (s+d)|) := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hd : 0 ≤ d := ht.trans htd
  have hu : 0 < max s t := hs.trans_le (le_max_left _ _)
  have huv : max s t ≤ s+d := max_le (by linarith) (by linarith)
  have hv : s+d ≤ (2*L)*max s t := by
    have hsL : s ≤ L*s := by nlinarith
    have hs' : L*s ≤ L*max s t := mul_le_mul_of_nonneg_left (le_max_left _ _) hL0.le
    have ht' : L*t ≤ L*max s t := mul_le_mul_of_nonneg_left (le_max_right _ _) hL0.le
    nlinarith
  have h2L : 1 ≤ 2*L := by linarith
  have hcomp := log_abs_comparison hu huv hv h2L
  have hlog2L : 0 ≤ Real.log (2*L) := Real.log_nonneg h2L
  calc
    _ ≤ C*(10+(|Real.log (s+d)|+Real.log (2*L))/Real.log 2) := by gcongr
    _ ≤ C*(10+(|Real.log (s+d)|+Real.log (2*L))/Real.log 2) +
        C*((10+Real.log (2*L)/Real.log 2)*|Real.log (s+d)|+1/Real.log 2) := by
      apply le_add_of_nonneg_right
      positivity
    _ = _ := by ring

end TamingCompatibility.RadialPotential


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

theorem scalarCorrection_logSource_distance_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (a : Space → ℝ) (V : Space → Space) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (logSourceSupported a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C/(s+dist b y) := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_logSource_observer_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j a V ha hV R haR K₀ hK₀ hcenters
  obtain ⟨M,hM,hKM⟩ := hK₀.isBounded.subset_ball_lt 0 q
  let L := max (5+c) (2*(M+1)/δ)
  have hL : 1 ≤ L := (by linarith : (1:ℝ) ≤ 5+c).trans (le_max_left _ _)
  refine ⟨δ,hδ,C*L,by positivity,?_⟩
  intro y hy s hsr b hb
  have hdM : dist b y ≤ M+1 := by
    have hbM := hKM hb
    have hy1 : dist q y ≤ 1 := by simpa only [dist_comm] using (show dist y q < δ from hy).le.trans hδ1
    have hbM' : dist b q < M := hbM
    linarith [dist_triangle b q y]
  obtain ⟨ht0,htδ,hsep,_,hcomp⟩ := observerScale_properties hδ hc (dist_nonneg : 0 ≤ dist b y) hdM
  have he := hest y hy s hsr b hb (observerScale δ c (dist b y)) ⟨ht0,htδ⟩ hsep
  exact he.trans (inverse_observer_to_distance hsr.1 ht0 dist_nonneg hL hcomp hC)

include hD hH hweak hB hdual in

theorem scalarCorrection_sqrtSource_distance_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (a : Space → ℝ) (V : Space → Space) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) (hR1 : R ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (sqrtSourceSupported a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C*(1+|Real.log (s+dist b y)|) := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_sqrtSource_observer_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j a V ha hV R haR K₀ hK₀ hcenters hR1
  obtain ⟨M,hM,hKM⟩ := hK₀.isBounded.subset_ball_lt 0 q
  let L := max (5+c) (2*(M+1)/δ)
  have hL : 1 ≤ L := (by linarith : (1:ℝ) ≤ 5+c).trans (le_max_left _ _)
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlogL : 0 ≤ Real.log (2*L) := Real.log_nonneg (by linarith)
  refine ⟨δ,hδ,C*(10+Real.log (2*L)/Real.log 2+1/Real.log 2),by positivity,?_⟩
  intro y hy s hsr b hb
  have hdM : dist b y ≤ M+1 := by
    have hbM := hKM hb
    have hy1 : dist q y ≤ 1 := by simpa only [dist_comm] using (show dist y q < δ from hy).le.trans hδ1
    have hbM' : dist b q < M := hbM
    linarith [dist_triangle b q y]
  obtain ⟨ht0,htδ,hsep,_,hcomp⟩ := observerScale_properties hδ hc (dist_nonneg : 0 ≤ dist b y) hdM
  have he := hest y hy s hsr b hb (observerScale δ c (dist b y)) ⟨ht0,htδ⟩ hsep
  exact he.trans (log_observer_to_distance hsr.1 ht0 (observerScale_le_dist hc dist_nonneg) hL hcomp hC)

end TamingCompatibility.GeometricHilbert

end

end OAI
