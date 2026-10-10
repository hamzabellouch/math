import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.RadialOperatorCutoffs

namespace OAI

section
section

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

theorem scalarCorrection_fixed_jet
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (b₀ : Space) (R : ℝ) (hR : 0 ≤ R) (hKR : K ⊆ Metric.ball b₀ R)
    (q : Space) (hq : q ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Metric.ball q δ,
      ∀ (φ : supportedSchwartz K) (j : Fin 2) (M : ℝ), 0 ≤ M →
      (∀ z, |φ.val z| ≤ M) →
      (∀ k ≤ 3, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ρ z * φ.val z) z‖ ≤ M) →
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y φ‖ ≤ C*M := by
  obtain ⟨ζ,χ,hζ,hcχ,hχ,hζχ,hχ0⟩ := RadialPotential.exists_normalized_operator_cutoffs (E := Space)
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,hest⟩ :=
    geometric_inhomogeneous_two_jet A J α hs ht D hD p τ ρ hU hUD hτ hρ q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨E,hE,hsource⟩ := geometric_scaled_source_dual A J α hs ht D hD p τ hK (hKU.trans hUD)
    (fun z hz => hτ z (hKU hz))
  obtain ⟨c,hc,hce⟩ := exists_rhs_scalarJet_constant L 3
  have hc0 : 0 ≤ c := (by norm_num : (0:ℝ) ≤ 1).trans hc
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hqV)
  have hKV : Metric.closedBall q (ε/2) ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεV
  obtain ⟨C₀,hC₀,hout⟩ := closedLift_scaled_basis_local_bound A J α hs ht D hD
    (stdOrthonormalBasis ℝ Space).toBasis p τ η L
    hV (hVW.trans (hWU.trans hUD))
    (fun z hz => hτ z (hWU (hVW hz))) hηone (isCompact_closedBall q (ε/2)) hKV
  obtain ⟨e,he,hevent⟩ := Metric.eventually_nhds_iff.mp hest
  let r := min (e/2) 1
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr1 : r ≤ 1 := min_le_right _ _
  have hre : r < e := (min_le_left _ _).trans_lt (by linarith)
  let δ := min e (ε/2)
  have hδ : 0 < δ := lt_min he (by positivity)
  refine ⟨δ,hδ,C₀*C*((c+E*R^3)*r^3+B*E*R^3)/r^3,by positivity,?_⟩
  intro y hy φ j M hM hval hjets
  have hyK : y ∈ Metric.closedBall q (ε/2) :=
    (show dist y q < δ from hy).le.trans (min_le_right _ _)
  have he' := hevent (show dist (r,y) (0,q) < e from by
    rw [Prod.dist_eq,dist_zero_right,Real.norm_of_nonneg hr.le]
    exact max_lt hre ((show dist y q < δ from hy).trans_le (min_le_left _ _)))
  let f := scalarTestLM A J α hs ht D p K hK (hKU.trans hUD) j φ
  have hd : ∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ E*M*R^3*‖v‖ :=
    hsource φ.val (supportedSchwartz_compact hK φ) φ.property j b₀ R M hR hM
      (φ.property.trans hKR) hval
  have hEM : 0 ≤ E*M*R^3 := by positivity
  have ha := hdual f (E*M*R^3) hEM hd
  have hjets' : ∀ k ≤ 3, ∀ z,
      ‖iteratedFDeriv ℝ k (fun z => ρ z * φ.val z) z‖ ≤ M/r^k := by
    intro k hk z
    apply (hjets k hk z).trans
    exact (le_div_iff₀ (pow_pos hr k)).mpr (by
      simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1 : r^k ≤ 1) hM)
  have hd' := normalizedRawRHSMap_component_scaled_bound A J α hs ht D hD p τ ρ L 3 c hce j φ.val
    (supportedSchwartz_compact hK φ) (φ.property.trans (hKU.trans hUD))
    (fun z hz => hτ z (hKU (φ.property hz))) r M hr hM hjets'
  have hj := he' hr hr1 f (H f) (Gs f) (E*M*R^3) (c*M) hEM
    (mul_nonneg hc0 hM) (hH f) hd hd' (hweak f) 0 hχ0
  have ho := hout H Gs f y hyK r
    (C*((c*M+E*M*R^3)*r^3+‖antiToEnergy A J α hs ht (Gs f)‖)) hr hr1 (by
    simpa only [smul_zero,zero_add,OrthonormalBasis.coe_toBasis] using hj)
  rw [scalarCorrectionLM_eq A J α hs ht D H Gs]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hr 3)).mpr
  calc
    _ = r^3*‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
        (extChartAt Model p.val).symm y -
        ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm y‖ := by
          rw [mul_comm]
    _ ≤ C₀*(C*((c*M+E*M*R^3)*r^3+‖antiToEnergy A J α hs ht (Gs f)‖)) := ho
    _ ≤ C₀*C*((c+E*R^3)*r^3+B*E*R^3)*M := by
      calc
        _ ≤ C₀*(C*((c*M+E*M*R^3)*r^3+B*(E*M*R^3))) := by gcongr
        _ = _ := by ring
end TamingCompatibility.GeometricHilbert

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

theorem scalarCorrection_all_scales
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ,
      (∀ r > (0:ℝ), ∀ (φ : supportedSchwartz K) (j : Fin 2) (b : Space) (M : ℝ),
        0 ≤ M → tsupport φ.val ⊆ Metric.ball b r → (∀ z, |φ.val z| ≤ M) →
        (∀ k ≤ 3, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ρ z * φ.val z) z‖ ≤ M/r^k) →
        ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y φ‖ ≤ C*M) ∧
      (∀ r ∈ Ioo (0:ℝ) δ, ∀ (φ : supportedSchwartz K) (j : Fin 2) (b : Space) (R M : ℝ),
        0 ≤ R → 0 ≤ M → tsupport φ.val ⊆ Metric.ball b R → (∀ z, |φ.val z| ≤ M) →
        R+c*r ≤ dist b y →
        ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y φ‖ ≤ C*M*R^3/r^3) := by
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space)
  obtain ⟨δ₀,hδ₀,hδ₀1,c,hc,C₀,hC₀,hest⟩ :=
    scalarCorrection_local_estimates A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq
  obtain ⟨δ₁,hδ₁,C₁,hC₁,hfixed⟩ :=
    scalarCorrection_fixed_jet A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU 0 R hR.le hKR q hq
  let δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  have hδsmall : δ ≤ δ₀ := min_le_left _ _
  have hδ1 : δ ≤ 1 := hδsmall.trans hδ₀1
  refine ⟨δ,hδ,hδ1,c,hc,max C₀ (C₁/δ₀^3),hC₀.trans (le_max_left _ _),?_⟩
  intro y hy
  have hy₀ : y ∈ Metric.ball q δ₀ := (show dist y q < δ from hy).trans_le hδsmall
  have hy₁ : y ∈ Metric.ball q δ₁ := (show dist y q < δ from hy).trans_le (min_le_right _ _)
  constructor
  · intro r hr φ j b M hM hball hval hjets
    by_cases hrδ : r < δ₀
    · exact ((hest y hy₀).1 r ⟨hr,hrδ⟩ φ j b M hM hball hval hjets).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hM)
    · have hδr : δ₀ ≤ r := le_of_not_gt hrδ
      have hM' : M ≤ M/δ₀^3 := (le_div_iff₀ (pow_pos hδ₀ 3)).mpr
        (by simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hδ₀.le hδ₀1 : δ₀^3 ≤ 1) hM)
      have hpow : ∀ k ≤ 3, δ₀^3 ≤ r^k := fun k hk =>
        (pow_le_pow_of_le_one hδ₀.le hδ₀1 hk).trans (pow_le_pow_left₀ hδ₀.le hδr k)
      have hb := hfixed y hy₁ φ j (M/δ₀^3) (by positivity)
        (fun z => (hval z).trans hM') (fun k hk z => (hjets k hk z).trans
          (div_le_div_of_nonneg_left hM (pow_pos hδ₀ 3) (hpow k hk)))
      apply hb.trans
      calc
        C₁*(M/δ₀^3) = (C₁/δ₀^3)*M := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hM
  · intro r hr φ j b R M hR hM hball hval hsep
    have hb := (hest y hy₀).2 r ⟨hr.1,hr.2.trans_le hδsmall⟩ φ j b R M hR hM hball hval hsep
    exact hb.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hM) (pow_nonneg hR 3))
      (pow_nonneg hr.1.le 3))

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
