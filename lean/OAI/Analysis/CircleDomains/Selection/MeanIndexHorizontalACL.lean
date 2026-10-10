import OAI.Analysis.CircleDomains.Selection.HorizontalMeanIndexBound
import OAI.Analysis.CircleDomains.Sobolev.RationalLineDerivative

namespace OAI

/-! The actual locally lifted mean index is absolutely continuous on
almost every physical horizontal line. Rational slice estimates are
simultaneous, and continuity from above supplies arbitrary endpoints. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
 theorem meanIndex_horizontal_ACL_derivative
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (Q : C(ℂ, X)) {a b c d : ℝ} (J : Set ℝ) (hJ : MeasurableSet J)
    (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox (Icc a b) J))
    (hpos : ∀ z ∈ planarSliceBox (Icc a b) J, 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox (Icc a b) J, diskRayProjection (Ψ z) = F (Q z))
    (v : ℂ → ℝ) (hv : ∀ z (hz : z ∈ planarSliceBox (Icc a b) J),
      v z = meanGeometricIndex hsch K hKS (η.map f) ⟨Ψ z, hpos z hz⟩)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ Q '' planarSliceBox (Icc a b) J))
    (hinj : InjOn (F ∘ Q) (planarSliceBox (Icc a b) J))
    (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ)
    (hfin : (∫⁻ z in planarSliceBox (Icc a b) J, ρ z) < ∞)
    (hcounts : ∀ᵐ y ∂volume, ∀ p q : ℚ, Icc (p : ℝ) q ⊆ Icc a b →
      (∫⁻ γ : A, pathImageCount
        (Q '' (planarSliceBox (Icc (p : ℝ) q) J ∩ Complex.im ⁻¹' {y})) γ.val ∂(η : Measure A)) ≤
        ∫⁻ x in Icc (p : ℝ) q, ρ ⟨x, y⟩) :
    ∀ᵐ y ∂volume.restrict J,
      AbsolutelyContinuousOnInterval (fun x => v ⟨x, y⟩) c d ∧
        (∀ᵐ x ∂volume.restrict (Icc c d),
          |deriv (fun t => v ⟨t, y⟩) x| ≤ (ρ ⟨x, y⟩).toReal) := by
  have hG : Measurable (fun y : ℝ => ∫⁻ x in Icc a b, ρ ⟨x, y⟩) :=
    (hρ.comp (Complex.equivRealProdCLM.symm.continuous.comp continuous_swap).measurable).lintegral_prod_right'
  have hfinite : ∀ᵐ y ∂volume.restrict J, (∫⁻ x in Icc a b, ρ ⟨x, y⟩) < ∞ := by
    apply ae_lt_top hG
    rw [← lintegral_planarSliceBox measurableSet_Icc hJ ρ hρ]
    exact hfin.ne
  filter_upwards [ae_restrict_mem hJ, hfinite, ae_mono Measure.restrict_le_self hcounts]
    with s hs hsfin hscount
  have hlocal : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x < y →
      ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < x → y < (q : ℝ) → (q : ℝ) < b →
        ENNReal.ofReal (dist (v ⟨x, s⟩) (v ⟨y, s⟩)) ≤ ∫⁻ t in Icc (p : ℝ) q, ρ ⟨t, s⟩ := by
    intro x hx y hy hxy p q hp hpx hyq hq
    have hIxy : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1.le hy.2.le
    have hIpq : Icc (p : ℝ) q ⊆ Icc a b := Icc_subset_Icc hp.le hq.le
    have hxy_pq : Icc x y ⊆ Icc (p : ℝ) q := Icc_subset_Icc hpx.le hyq.le
    have hb := meanIndex_horizontal_segment_bound hsch hsep A K hK hKS η F f hf hmap
      Q (Icc a b) J Ψ hΨ hpos hproj v hv hF hinj hxy hIxy hs
    have hwide : ENNReal.ofReal |v ⟨y, s⟩ - v ⟨x, s⟩| ≤
        ∫⁻ γ : A, pathImageCount
          (Q '' (planarSliceBox (Icc (p : ℝ) q) J ∩ Complex.im ⁻¹' {s})) γ.val ∂(η : Measure A) :=
      hb.trans (lintegral_mono fun γ => pathImageCount_mono_set
        (image_mono (inter_subset_inter_left _ (planarSliceBox_mono hxy_pq Subset.rfl))) γ.val)
    simpa only [Real.dist_eq, abs_sub_comm] using hwide.trans (hscount p q hIpq)
  exact ⟨locally_absolutelyContinuous_of_rational_bounds (fun x => v ⟨x, s⟩)
      (fun x => ρ ⟨x, s⟩) hac hcd hdb hsfin hlocal,
    locally_ae_abs_deriv_le_of_rational_bounds (fun x => v ⟨x, s⟩)
      (fun x => ρ ⟨x, s⟩)
      (hρ.comp (Complex.equivRealProdCLM.symm.continuous.comp
        (continuous_id.prodMk continuous_const)).measurable) hac hcd hdb hsfin hlocal⟩

end CircleDomainRigidity

end

end OAI
