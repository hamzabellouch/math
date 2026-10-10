import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianUniformInputs

namespace OAI


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

theorem scalarCorrection_logSource_observer_estimate
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
      ∀ t ∈ Ico (0:ℝ) δ, (5+c)*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.logSourceSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C/(s+t) := by
  obtain ⟨δ₁,hδ₁,hδ₁1,c₁,hc₁,C₁,hC₁,hinner⟩ :=
    scalarCorrection_logInner_estimates A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W a V hW ha hV R haR K₀ hK₀ hcenters
  obtain ⟨δ₂,hδ₂,_,c₂,_,C₂,_,hshell⟩ :=
    scalarCorrection_logShell_estimates A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W a V hW ha hV R haR K₀ hK₀ hcenters
  let δ := min δ₁ δ₂
  let c := max c₁ c₂
  let C := max C₁ C₂
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨δ,lt_min hδ₁ hδ₂,(min_le_left _ _).trans hδ₁1,c,hc₁.trans_le (le_max_left _ _),
    14*C,by positivity,?_⟩
  intro y hy s hsr b hb t hto hsep
  have hs0 : 0 < s := hsr.1
  have hy₁ : y ∈ Metric.ball q δ₁ := (show dist y q < δ from hy).trans_le (min_le_left _ _)
  have hy₂ : y ∈ Metric.ball q δ₂ := (show dist y q < δ from hy).trans_le (min_le_right _ _)
  obtain ⟨N,hN,_,hmin⟩ := exists_minimal_dyadic_scale hsr.1 hsr.2
  let L := scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
  let v₀ := L (HermitianRadial.logInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))
  let v := fun k => L (HermitianRadial.logShellSupported W a V ha hV R haR K
    (mul_pos hsr.1 (by positivity : 0 < (2:ℝ)^k)) hsr.1 b (hcenters b hb))
  have hi := hinner y hy₁ s hsr b hb
  have h₀near : ‖v₀‖ ≤ C/s := hi.1.trans
    (div_le_div_of_nonneg_right (le_max_left _ _) hsr.1.le)
  have h₀off : s ≤ t → ‖v₀‖ ≤ C*s^2/t^3 := by
    intro hst
    have ht0 : 0 < t := hs0.trans_le hst
    have hsel : 5*s+c₁*t ≤ dist b y := by
      have hc : c₁*t ≤ c*t := mul_le_mul_of_nonneg_right (le_max_left _ _) hto.1
      nlinarith
    exact (hi.2 t ⟨ht0,hto.2.trans_le (min_le_left _ _)⟩ hsel).trans (by gcongr; exact le_max_left _ _)
  have hnear : ∀ k < N, ‖v k‖ ≤ C/(s*2^k) := by
    intro k hk
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hs0,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    exact (hshell y hy₂ (s*2^k) hr s hsr' b hb).1.trans
      (div_le_div_of_nonneg_right (le_max_right _ _) hr.1.le)
  have hoff : ∀ k < N, s*2^k ≤ t → ‖v k‖ ≤ C*(s*2^k)^2/t^3 := by
    intro k hk hkt
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hs0,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    have ht0 : 0 < t := hr.1.trans_le hkt
    have hsel : 5*(s*2^k)+c₂*t ≤ dist b y := by
      have hc : c₂*t ≤ c*t := mul_le_mul_of_nonneg_right (le_max_right _ _) hto.1
      nlinarith
    exact ((hshell y hy₂ (s*2^k) hr s hsr' b hb).2 t
      ⟨ht0,hto.2.trans_le (min_le_right _ _)⟩ hsel).trans (by gcongr; exact le_max_right _ _)
  have he := HermitianRadial.logSupported_reconstruction W a V ha hV R haR K hsr.1 b (hcenters b hb) N hN
  change ‖L _‖ ≤ _
  rw [he,map_add,map_sum]
  exact dyadic_mixed_inverse_bound v₀ v N hs0 hto.1 hC h₀near h₀off hnear hoff

include hD hH hweak hB hdual in

theorem scalarCorrection_sqrtSource_observer_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (a : Space → ℝ) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (haR : tsupport a ⊆ Metric.closedBall 0 R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b R ⊆ K) (hR1 : R ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) R, ∀ b, ∀ hb : b ∈ K₀,
      ∀ t ∈ Ico (0:ℝ) δ, (5+c)*t ≤ dist b y →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtSourceSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))‖ ≤ C*(10+|Real.log (max s t)|/Real.log 2) := by
  obtain ⟨δ₁,hδ₁,hδ₁1,c₁,hc₁,C₁,hC₁,hinner⟩ :=
    scalarCorrection_sqrtInner_estimates A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W a V hW ha hV R haR K₀ hK₀ hcenters
  obtain ⟨δ₂,hδ₂,_,c₂,_,C₂,_,hshell⟩ :=
    scalarCorrection_sqrtShell_estimates A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W a V hW ha hV R haR K₀ hK₀ hcenters
  let δ := min δ₁ δ₂
  let c := max c₁ c₂
  let C := max C₁ C₂
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨δ,lt_min hδ₁ hδ₂,(min_le_left _ _).trans hδ₁1,c,hc₁.trans_le (le_max_left _ _),
    C,hC,?_⟩
  intro y hy s hsr b hb t hto hsep
  have hs0 : 0 < s := hsr.1
  have hy₁ : y ∈ Metric.ball q δ₁ := (show dist y q < δ from hy).trans_le (min_le_left _ _)
  have hy₂ : y ∈ Metric.ball q δ₂ := (show dist y q < δ from hy).trans_le (min_le_right _ _)
  obtain ⟨N,hN,hscale,hmin⟩ := exists_minimal_dyadic_scale hsr.1 hsr.2
  let L := scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
  let v₀ := L (HermitianRadial.sqrtInnerSupported W a V ha hV R haR K hsr.1 b (hcenters b hb))
  let v := fun k => L (HermitianRadial.sqrtShellSupported W a V ha hV R haR K
    (mul_pos hsr.1 (by positivity : 0 < (2:ℝ)^k)) hsr.1 b (hcenters b hb))
  have hi := hinner y hy₁ s hsr b hb
  have h₀near : ‖v₀‖ ≤ C := hi.1.trans (le_max_left _ _)
  have hnear : ∀ k < N, ‖v k‖ ≤ C := by
    intro k hk
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hs0,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    exact (hshell y hy₂ (s*2^k) hr s hsr' b hb).1.trans
      (le_max_right _ _)
  have hoff : ∀ k < N, s*2^k ≤ t → ‖v k‖ ≤ C*(s*2^k)^3/t^3 := by
    intro k hk hkt
    have hr : s*2^k ∈ Ioc (0:ℝ) R := ⟨by positivity,(hmin k hk).le⟩
    have hsr' : s ∈ Ioc (0:ℝ) (s*2^k) := ⟨hs0,by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]⟩
    have ht0 : 0 < t := hr.1.trans_le hkt
    have hsel : 5*(s*2^k)+c₂*t ≤ dist b y := by
      have hc : c₂*t ≤ c*t := mul_le_mul_of_nonneg_right (le_max_right _ _) hto.1
      nlinarith
    exact ((hshell y hy₂ (s*2^k) hr s hsr' b hb).2 t
      ⟨ht0,hto.2.trans_le (min_le_right _ _)⟩ hsel).trans (by gcongr; exact le_max_right _ _)
  have he := HermitianRadial.sqrtSupported_reconstruction W a V ha hV R haR K hsr.1 b (hcenters b hb) N hN
  change ‖L _‖ ≤ _
  rw [he,map_add,map_sum]
  exact dyadic_mixed_log_bound v₀ v N hs0 hto.1 hC (hscale.trans (by linarith)) h₀near hnear hoff

end TamingCompatibility.GeometricHilbert.Hermitian

end

end OAI
