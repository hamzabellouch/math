import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianCorrectedLower

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma harmonicLift_closed
    (H : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
      (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
    (f : antiPre A J α hs ht) : IsClosed (H f).val.val := by
  obtain ⟨h,hh,hc⟩ := harmonicAnti_smooth A J α hs ht D hD _
    ((harmonicAnti A J α hs ht).starProjection_apply_mem (smoothL2 A J α hs ht true f.val))
  have he : H f = h := Subtype.ext ((smoothL2 A J α hs ht true).injective
    ((hH f).trans hh.symm))
  rw [he]
  exact coclosed_antiInvariant_closed J α ht h.val.property h.property hc
end TamingCompatibility.GeometricHilbert

namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (p : X) (D : Data J α ht p)
  {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)
  {R s : ℝ} (a : ℝ) (hR : 0 < R) (hsp : 0 < s) (b : Space)
  (hball : Metric.closedBall b (2*R) ⊆ D.domain)

def combinedForm : smoothForms X 2 :=
  logForm A J α hs ht H Gs p D hφ hc hφD hR hsp b hball +
    a • sqrtForm A J α hs ht H Gs p D hφ hc hφD hR hsp b hball

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma combinedForm_closed (hHc : ∀ f, IsClosed (H f).val.val) :
    IsClosed (combinedForm A J α hs ht H Gs p D hφ hc hφD a hR hsp b hball).val := by
  apply (mem_closedForms_iff _).mp
  apply Submodule.add_mem
  · exact (mem_closedForms_iff _).mpr (correctedDdc_closed A J α hs ht H Gs hHc _)
  · exact Submodule.smul_mem _ a
      ((mem_closedForms_iff _).mpr (correctedDdc_closed A J α hs ht H Gs hHc _))

lemma combinedForm_invariant
    (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
      weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫) :
    IsInvariant (combinedForm A J α hs ht H Gs p D hφ hc hφD a hR hsp b hball).val J := by
  have hl : IsInvariant (logForm A J α hs ht H Gs p D hφ hc hφD hR hsp b hball).val J :=
    correctedDdc_invariant A J α hs ht H Gs hweak _
  have hs' : IsInvariant (sqrtForm A J α hs ht H Gs p D hφ hc hφD hR hsp b hball).val J :=
    correctedDdc_invariant A J α hs ht H Gs hweak _
  intro x u v
  change eval (logForm A J α hs ht H Gs p D hφ hc hφD hR hsp b hball).val x
      (J.endomorphism x u) (J.endomorphism x v) +
    a * eval (sqrtForm A J α hs ht H Gs p D hφ hc hφD hR hsp b hball).val x
      (J.endomorphism x u) (J.endomorphism x v) = _
  rw [hl x u v,hs' x u v]
  rfl
end TamingCompatibility.GeometricHilbert.Hermitian

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

theorem nonharmonicCorrection_off_source_uniform
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (q : Space) (hq : q ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      (∀ z ∈ U, rawPair J α ht p.val (D p) f.val.val z = 0) →
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y f‖ ≤ C*M := by
  obtain ⟨ζ,χ,hζ,hcχ,hχ,hζχ,hχ0⟩ := exists_normalized_operator_cutoffs (E := Space)
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,hest⟩ :=
    geometric_off_source_two_jet A J α hs ht D hD p τ ρ hU hUD hτ hρ q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hqV)
  have hKV : Metric.closedBall q (ε/2) ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεV
  obtain ⟨C₀,hC₀,hout⟩ := closedLift_scaled_basis_local_bound A J α hs ht D hD
    (stdOrthonormalBasis ℝ Space).toBasis p τ η L
    hV (hVW.trans (hWU.trans hUD))
    (fun z hz => hτ z (hWU (hVW hz))) hηone (isCompact_closedBall q (ε/2)) hKV
  have htK : ∀ᶠ t : ℝ × Space in 𝓝 (0,q), t.2 ∈ Metric.closedBall q (ε/2) :=
    (continuous_snd.tendsto (0,q)).eventually (Metric.closedBall_mem_nhds q (by positivity))
  have hshrink : ∀ᶠ t : ℝ × Space in 𝓝 (0,q), ∀ n : Fin 4, ∀ hr : t.1 ≠ 0,
      tsupport (normalizedCutoff L t.2 t.1 hr (χ (n.val+1))) ⊆ W := by
    apply (Filter.eventually_all.mpr ?_)
    intro n
    exact normalizedCutoff_eventually_support L q (χ (n.val+1)) (hcχ n.val (by omega)) hW hqW
  have hevent : ∀ᶠ t : ℝ × Space in 𝓝 (0,q), ∀ (hr : 0 < t.1), t.1 ≤ 1 →
      ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      (∀ z ∈ U, rawPair J α ht p.val (D p) f.val.val z = 0) →
      t.1^3*‖nonharmonicCorrectionLM A J α hs ht Gs p.val t.2 f‖ ≤ C₀*C*(1+B)*M := by
    filter_upwards [hest,htK,hshrink] with t hh htK hsupport
    intro hr hr1 f M hM hdu hfzero
    have hj := hh hr hr1 f (H f) (Gs f) M hM (hH f) hdu
      ⟨W,hW,Subset.rfl,fun n hn => hsupport ⟨n,by omega⟩ hr.ne',
        fun z hz => hfzero z (hWU hz)⟩ (hweak f) 0 hχ0
    have hj' : t.1*‖SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
            (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f)) (L t.2)‖ +
        t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ Space i}
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
            (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f)))) (L t.2)‖ +
        t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ Space j}
            (∂_{stdOrthonormalBasis ℝ Space i}
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
            (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f))))) (L t.2)‖ ≤ C*(1+B)*M := by
      simp only [smul_zero,zero_add] at hj
      apply hj.trans
      have ha := hdual f M hM hdu
      have hp := mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1 : t.1^3 ≤ 1) hM
      nlinarith [mul_nonneg hC (sub_nonneg.mpr ha),mul_nonneg hC (sub_nonneg.mpr hp)]
    have ho := hout H Gs f t.2 htK t.1 (C*(1+B)*M) hr hr1 (by
      simpa only [OrthonormalBasis.coe_toBasis] using hj')
    rw [closedLiftOfInverse_pullback_sub] at ho
    change t.1^3*‖nonharmonicCorrectionLM A J α hs ht Gs p.val t.2 f‖ ≤ _ at ho
    exact ho.trans_eq (by ring)
  obtain ⟨r₀,hr₀,he⟩ := Metric.eventually_nhds_iff.mp hevent
  let δ := min r₀ 1
  have hδ : 0 < δ := lt_min hr₀ (by norm_num)
  let r := δ/2
  have hr : 0 < r := by positivity
  have hr1 : r ≤ 1 := by dsimp [r]; linarith [min_le_right r₀ (1:ℝ)]
  refine ⟨δ,hδ,C₀*C*(1+B)/r^3,by positivity,?_⟩
  intro y hy f M hM hd hz
  have hp : dist (r,y) (0,q) < r₀ := by
    rw [Prod.dist_eq,dist_zero_right,Real.norm_of_nonneg hr.le]
    apply max_lt
    · dsimp [r]; linarith [min_le_left r₀ (1:ℝ)]
    · exact (show dist y q < δ from hy).trans_le (min_le_left _ _)
  have hu := he hp hr hr1 f M hM hd hz
  calc
    _ ≤ (C₀*C*(1+B)*M)/r^3 := (le_div_iff₀ (pow_pos hr 3)).mpr (by simpa only [mul_comm] using hu)
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
