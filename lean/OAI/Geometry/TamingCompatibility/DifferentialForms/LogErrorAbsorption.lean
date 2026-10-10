import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.CompactUniformBound

namespace OAI


noncomputable section
namespace TamingCompatibility
open Set Filter Topology

lemma exists_inverse_distance_dominates_log (c E F : ℝ) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      c/(2*t) ≤ c/t - (E+F*(1+|Real.log t|)) := by
  let g : ℝ → ℝ := fun t => E*t+F*(t+|t*Real.log t|)
  have hg : Continuous g :=
    (continuous_const.mul continuous_id).add
      (continuous_const.mul (continuous_id.add Real.continuous_mul_log.abs))
  have hzero : g 0 = 0 := by simp [g]
  have he : ∀ᶠ t in 𝓝 (0:ℝ), g t < c/2 :=
    hg.continuousAt.eventually (Iio_mem_nhds (by rw [hzero]; positivity))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro t ht htd
  have hb := hball (show t ∈ Metric.ball (0:ℝ) δ by simpa [Real.dist_eq,abs_of_pos ht] using htd)
  change E*t+F*(t+|t*Real.log t|) < c/2 at hb
  rw [abs_mul,abs_of_pos ht] at hb
  apply (le_sub_iff_add_le).mpr
  apply (mul_le_mul_iff_left₀ ht).mp
  field_simp
  nlinarith

lemma absorb_inverse_distance_error {c E t U V L q : ℝ}
    (hc : 0 < c) (hE : 0 ≤ E) (ht : 0 < t)
    (hU : L-E/t*q ≤ U) (hV : c/t*q ≤ V) :
    L ≤ U+(E/c)*V := by
  have h := mul_le_mul_of_nonneg_left hV (div_nonneg hE hc.le)
  have he : E/c*(c/t*q) = E/t*q := by field_simp
  rw [he] at h
  linarith
end TamingCompatibility


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
variable (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)

include hD hH hweak hB hdual hU hτ hρ hK hφone hK₀ in

theorem exists_positive_combination (hR1 : 2*R ≤ 1) :
    ∃ a c δ : ℝ, 0 < a ∧ 0 < c ∧ 0 < δ ∧
      ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ K, s+‖y-b‖ < δ → ∀ v : Space,
      let β := logForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD)) +
        a • sqrtForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))
      let val := ManifoldForms.pullback β.val (extChartAt Model p.val).symm y
        ![v,coordinateJ J p.val y v]
      0 ≤ val ∧ (‖y-b‖ ≤ s → c*(‖v‖^2/s^2) ≤ val) := by
  obtain ⟨C₀,hC₀,hlog⟩ := nonharmonic_logSource_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters K hK hKU
  obtain ⟨C₁,hC₁,hsqrt⟩ := nonharmonic_sqrtSource_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1 K hK hKU
  let W := hermitianCenterExtension J p.val (D p) hφ hc hφD
  let L := SchwartzMap.seminorm ℝ 0 1 W
  let M := SchwartzMap.seminorm ℝ 0 0 W
  have hL : 0 ≤ L := apply_nonneg _ _
  have hM : 0 ≤ M := apply_nonneg _ _
  let E := (1+M)^2*16*L*M+C₀*M
  let ES := (1+M)^2*10*L*M
  let FS := C₁*M
  let cS := 1/(1+M)
  have hcS : 0 < cS := by dsimp [cS]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨δ,hδ,habs⟩ := exists_inverse_distance_dominates_log cS ES FS hcS
  let a := E/(cS/2)+1
  let c := 2/(1+(1+M)^2)^2
  refine ⟨a,c,min δ R,by dsimp [a]; positivity,by dsimp [c]; positivity,
    lt_min hδ hR,?_⟩
  intro s hsr b hb y hy hnear v
  dsimp only
  have hsp : 0 < s := hsr.1
  have hball := (hcenters b hb).trans (hKU.trans hUD)
  have hyR : ‖y-b‖ < R := by linarith [(lt_min_iff.mp hnear).2]
  have hone : ∀ z ∈ Metric.closedBall b (2*R), φ z = 1 :=
    fun z hz => hφone z (hcenters b hb hz)
  have hl := logForm_trace_lower A J α hs ht H Gs p.val (D p) hφ hc hφD
    hR hsr.1 b y v hball hyR hone hC₀
    (by simpa only [logSource,dist_comm b y,dist_eq_norm] using hlog y hy s hsr b hb)
  have hh := sqrtForm_trace_lower A J α hs ht H Gs p.val (D p) hφ hc hφD
    hR hsr.1 b y v hball hyR hone hC₁
    (by simpa only [sqrtSource,dist_comm b y,dist_eq_norm] using hsqrt y hy s hsr b hb)
  let t := s+‖y-b‖
  have htpos : 0 < t := by dsimp [t]; positivity
  have hsmall : t < δ := (lt_min_iff.mp hnear).1
  have hsa := mul_le_mul_of_nonneg_right (habs t htpos hsmall) (sq_nonneg ‖v‖)
  have hsl : (cS/2)/t*‖v‖^2 ≤
      ManifoldForms.pullback
        (sqrtForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b hball).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := by
    apply le_trans _ hh
    convert hsa using 1 <;> dsimp only [cS,ES,FS,t,M,L,W] <;>
      simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
  let q := 2*s^2*(‖v‖^2+‖W b v‖^2)/(s^2+‖y-b‖^2+‖W b (y-b)‖^2)^2
  have hll : q-E/t*‖v‖^2 ≤
      ManifoldForms.pullback
        (logForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b hball).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := hl
  have hcomb := absorb_inverse_distance_error (by positivity : 0 < cS/2) hE htpos hll hsl
  have hsqnonneg := le_trans (by positivity : 0 ≤ (cS/2)/t*‖v‖^2) hsl
  have htotal : q ≤ ManifoldForms.pullback
      (logForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b hball).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] +
      a * ManifoldForms.pullback
      (sqrtForm A J α hs ht H Gs p.val (D p) hφ hc hφD hR hsr.1 b hball).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := by
    dsimp only [a]
    nlinarith
  change 0 ≤ _ + a*_ ∧ _
  refine ⟨(by positivity : 0 ≤ q).trans htotal,?_⟩
  intro hin
  exact (hermitian_log_trace_inner (W b) hsr.1 hM (W.norm_le_seminorm ℝ b)
    (y-b) v hin).trans htotal
end TamingCompatibility.GeometricHilbert.Hermitian

end

end OAI
