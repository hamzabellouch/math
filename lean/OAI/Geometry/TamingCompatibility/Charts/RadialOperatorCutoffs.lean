import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialGradientBridge
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialScalarNear
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialScalarOff

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Metric
open scoped ContDiff Topology SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

def complexScaledCutoff (r : ℝ) (hr : 0 < r) : 𝓢(E,ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM
    ((scaledCutoff_compact hr).toSchwartzMap (scaledCutoff_smooth r))

lemma complexScaledCutoff_support (r : ℝ) (hr : 0 < r) :
    tsupport (complexScaledCutoff (E := E) r hr) ⊆ closedBall 0 (2*r) :=
  (tsupport_comp_subset Complex.ofReal_zero (scaledCutoff r)).trans (scaledCutoff_tsupport hr)

lemma complexScaledCutoff_compact (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (complexScaledCutoff (E := E) r hr : E → ℂ) :=
  (isCompact_closedBall 0 (2*r)).of_isClosed_subset (isClosed_tsupport _)
    (complexScaledCutoff_support r hr)

lemma complexScaledCutoff_one (r : ℝ) (hr : 0 < r) {z : E} (hz : ‖z‖ ≤ r) :
    complexScaledCutoff r hr z = 1 := by
  change (scaledCutoff r z : ℂ) = 1
  rw [scaledCutoff_one hr hz,Complex.ofReal_one]

lemma complexScaledCutoff_one_nhds (r : ℝ) (hr : 0 < r) {z : E} (hz : ‖z‖ < r) :
    (complexScaledCutoff r hr : E → ℂ) =ᶠ[𝓝 z] fun _ => 1 := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with y hy
  exact complexScaledCutoff_one r hr (le_of_lt hy)

theorem exists_normalized_operator_cutoffs :
    ∃ (ζ : 𝓢(E,ℂ)) (χ : ℕ → 𝓢(E,ℂ)),
      HasCompactSupport (ζ : E → ℂ) ∧
      (∀ n ≤ 3, HasCompactSupport (χ (n+1) : E → ℂ)) ∧
      (∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1) ∧
      (∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) ∧
      ((χ 4 : E → ℂ) =ᶠ[𝓝 0] fun _ => 1) := by
  let r := fun n : ℕ => ((4:ℝ)^n)⁻¹
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  have hr1 : ∀ n, r n ≤ 1 := by
    intro n
    exact (inv_le_one₀ (by positivity : 0 < (4:ℝ)^n)).mpr (one_le_pow₀ (by norm_num))
  have hstep : ∀ n, 2*r (n+1) < r n := by
    intro n
    dsimp [r]
    rw [pow_succ,mul_inv_rev]
    have hp : 0 < ((4:ℝ)^n)⁻¹ := by positivity
    nlinarith
  let χ := fun n => complexScaledCutoff (E := E) (r n) (hr n)
  refine ⟨complexScaledCutoff 2 (by norm_num),χ,complexScaledCutoff_compact 2 (by norm_num),
    fun n _ => complexScaledCutoff_compact (r (n+1)) (hr (n+1)),?_,?_,?_⟩
  · intro n _ x hx
    have hh := complexScaledCutoff_support (r (n+1)) (hr (n+1)) hx
    simp only [mem_closedBall,dist_zero_right] at hh
    exact complexScaledCutoff_one_nhds (r n) (hr n) (hh.trans_lt (hstep n))
  · intro n _ x hx
    apply complexScaledCutoff_one
    have hh := complexScaledCutoff_support (r (n+1)) (hr (n+1)) hx
    simp only [mem_closedBall,dist_zero_right] at hh
    exact hh.trans (by linarith [hr1 (n+1)])
  · exact complexScaledCutoff_one_nhds (r 4) (hr 4) (by simpa only [norm_zero] using hr 4)

end TamingCompatibility.RadialPotential

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory EuclideanSobolevOperators
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

theorem scalarCorrection_local_estimates
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ,
      (∀ r ∈ Ioo (0:ℝ) δ, ∀ (φ : supportedSchwartz K) (j : Fin 2) (b : Space) (M : ℝ),
        0 ≤ M → tsupport φ.val ⊆ Metric.ball b r → (∀ z, |φ.val z| ≤ M) →
        (∀ k ≤ 3, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ρ z * φ.val z) z‖ ≤ M/r^k) →
        ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y φ‖ ≤ C*M) ∧
      (∀ r ∈ Ioo (0:ℝ) δ, ∀ (φ : supportedSchwartz K) (j : Fin 2) (b : Space) (R M : ℝ),
        0 ≤ R → 0 ≤ M → tsupport φ.val ⊆ Metric.ball b R → (∀ z, |φ.val z| ≤ M) →
        R+c*r ≤ dist b y →
        ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y φ‖ ≤ C*M*R^3/r^3) := by
  obtain ⟨ζ,χ,hζ,hcχ,hχ,hζχ,hχ0⟩ := RadialPotential.exists_normalized_operator_cutoffs (E := Space)
  obtain ⟨Cn,hCn,hen⟩ := closedLift_scalar_near_source A J α hs ht D hD H Gs hH hweak B hB hdual
    p τ ρ U hU hUD hτ hρ K hK hKU q hq ζ hζ χ hcχ hχ hζχ hχ0
  obtain ⟨c,hc,Co,hCo,heo⟩ := closedLift_scalar_off_source A J α hs ht D hD H Gs hH hweak B hB hdual
    p τ ρ U hU hUD hτ hρ K hK hKU q hq ζ hζ χ hcχ hχ hζχ hχ0
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp (hen.and heo)
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  refine ⟨δ,hδ,hδ1,c,hc,max Cn Co,hCn.trans (le_max_left _ _),?_⟩
  intro y hy
  have hyε : dist y q < ε := (show dist y q < δ from hy).trans_le hδε
  have hp : ∀ r ∈ Ioo (0:ℝ) δ, dist (r,y) (0,q) < ε := by
    intro r hr
    rw [Prod.dist_eq,dist_zero_right,Real.norm_of_nonneg hr.1.le]
    exact max_lt (hr.2.trans_le hδε) hyε
  constructor
  · intro r hr φ j b M hM hball hval hjets
    rw [scalarCorrectionLM_eq A J α hs ht D H Gs]
    have hbnd := (he (hp r hr)).1 hr.1 (hr.2.le.trans hδ1) φ.val
      (supportedSchwartz_compact hK φ) φ.property j b M hM hball hval hjets
    exact hbnd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hM)
  · intro r hr φ j b R M hR hM hball hval hsep
    rw [scalarCorrectionLM_eq A J α hs ht D H Gs]
    have hbnd := (he (hp r hr)).2 hr.1 (hr.2.le.trans hδ1) φ.val
      (supportedSchwartz_compact hK φ) φ.property j b R M hR hM hball hval hsep
    apply hbnd.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right Cn Co) hM) (pow_nonneg hR 3))
      (pow_nonneg hr.1.le 3)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
