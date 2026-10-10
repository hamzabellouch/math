import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianAssembly

namespace OAI

section
section

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

theorem scalarCorrection_logSource_distance_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (a : Space → ℝ) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.logSourceSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C/(s+dist b y) := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_logSource_observer_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W a V hW ha hV R haR K₀ hK₀ hcenters
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
    (W : Space → Space →L[ℝ] Space) (a : Space → ℝ) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) (hR1 : R ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtSourceSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C*(1+|Real.log (s+dist b y)|) := by
  obtain ⟨δ,hδ,hδ1,c,hc,C,hC,hest⟩ :=
    scalarCorrection_sqrtSource_observer_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W a V hW ha hV R haR K₀ hK₀ hcenters hR1
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

end TamingCompatibility.GeometricHilbert.Hermitian

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

theorem scalarCorrection_logError_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (S : ℝ)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s ∈ Icc (0:ℝ) S, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.logErrorSupported W V hW hV hR K s b (hcenters b hb))‖ ≤ C := by
  obtain ⟨Q,hQ,hKQ⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space)
  obtain ⟨δ,hδ,C,hC,hest⟩ :=
    scalarCorrection_fixed_jet A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU 0 Q hQ.le hKQ q hq
  obtain ⟨E,hE,hinput⟩ := HermitianRadial.logErrorSchwartz_uniform_inputs W V hW hV hR ρ (ρ.smooth ⊤) hK₀ S 3
  refine ⟨δ,hδ,C*E,by positivity,?_⟩
  intro y hy s hsr b hb
  have hin := hinput s hsr b hb
  exact hest y hy (HermitianRadial.logErrorSupported W V hW hV hR K s b (hcenters b hb)) j E hE hin.1 hin.2

include hD hH hweak hB hdual in

theorem scalarCorrection_sqrtError_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (S : ℝ)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s ∈ Icc (0:ℝ) S, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtErrorSupported W V hW hV hR K s b (hcenters b hb))‖ ≤ C := by
  obtain ⟨Q,hQ,hKQ⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space)
  obtain ⟨δ,hδ,C,hC,hest⟩ :=
    scalarCorrection_fixed_jet A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU 0 Q hQ.le hKQ q hq
  obtain ⟨E,hE,hinput⟩ := HermitianRadial.sqrtErrorSchwartz_uniform_inputs W V hW hV hR ρ (ρ.smooth ⊤) hK₀ S 3
  refine ⟨δ,hδ,C*E,by positivity,?_⟩
  intro y hy s hsr b hb
  have hin := hinput s hsr b hb
  exact hest y hy (HermitianRadial.sqrtErrorSupported W V hW hV hR K s b (hcenters b hb)) j E hE hin.1 hin.2

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
