import OAI.Analysis.Mahler.SphereFlux

namespace OAI

open Complex MeasureTheory Metric Filter Set
open scoped Topology

namespace Mahler

noncomputable def actualRealComplexJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℂ) (x : E) : RealComplexTwoJet E :=
  (fderiv ℝ u x, fderiv ℝ (fderiv ℝ u) x)

/-- Uniform first and second derivative convergence gives uniform convergence
of the actual outward sphere densities. The nonlinear operation is a continuous
finite shuffle polynomial. -/
theorem sphereDensity_tendstoUniformlyOn {k : ℕ} {I : Type*} {l : Filter I}
    {u : I → ComplexEuclidean (k+1) → ℂ} {v : ComplexEuclidean (k+1) → ℂ}
    {K : Set (ComplexEuclidean (k+1))} (hK : IsCompact K)
    (hv : ContinuousOn (actualRealComplexJet v) K)
    (h1 : TendstoUniformlyOn (fun i => fderiv ℝ (u i)) (fderiv ℝ v) l K)
    (h2 : TendstoUniformlyOn (fun i => fderiv ℝ (fderiv ℝ (u i)))
      (fderiv ℝ (fderiv ℝ v)) l K) :
    TendstoUniformlyOn
      (fun i x => sphereJetDensity k (x, actualRealComplexJet (u i) x))
      (fun x => sphereJetDensity k (x, actualRealComplexJet v x)) l K := by
  have hj := SymmetricMahler.uniform_pair
    (V := ComplexEuclidean (k+1) →L[ℝ] ℂ)
    (W := ComplexEuclidean (k+1) →L[ℝ] (ComplexEuclidean (k+1) →L[ℝ] ℂ)) h1 h2
  have hid : TendstoUniformlyOn (fun (_ : I) (x : ComplexEuclidean (k+1)) => x) id l K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall (by intro i x hx; simpa using hε)
  exact SymmetricMahler.uniform_comp_of_compact hK (continuousOn_id.prodMk hv)
    (SymmetricMahler.uniform_pair hid hj) (continuous_sphereJetDensity k)

/-- A genuine area integral limit; continuity gives measurability, compactness
gives a bounded limit density, and uniform convergence supplies a common
integrable constant bound. No integral convergence is a hypothesis. -/
theorem sphereJetIntegral_tendsto {k : ℕ} {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated]
    {u : I → ComplexEuclidean (k+1) → ℂ} {v : ComplexEuclidean (k+1) → ℂ}
    {K : Set (ComplexEuclidean (k+1))} (hK : IsCompact K)
    (hS : sphere (0 : ComplexEuclidean (k+1)) 1 ⊆ K)
    (hv : ContinuousOn (actualRealComplexJet v) K)
    (hu : ∀ᶠ i in l, ContinuousOn (actualRealComplexJet (u i)) K)
    (h1 : TendstoUniformlyOn (fun i => fderiv ℝ (u i)) (fderiv ℝ v) l K)
    (h2 : TendstoUniformlyOn (fun i => fderiv ℝ (fderiv ℝ (u i)))
      (fderiv ℝ (fderiv ℝ v)) l K) :
    Tendsto (fun i => ∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet (u i) z)
        ∂sphereArea (k+1)) l
      (𝓝 (∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
        sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet v z)
          ∂sphereArea (k+1))) := by
  let : IsFiniteMeasure (sphereArea (k+1)) := by unfold sphereArea; infer_instance
  have hc : ContinuousOn (fun x => sphereJetDensity k (x, actualRealComplexJet v x)) K :=
    (continuous_sphereJetDensity k).comp_continuousOn (continuousOn_id.prodMk hv)
  have huni := sphereDensity_tendstoUniformlyOn hK hv h1 h2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [hu] with i hi
    have hci : Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
        sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet (u i) z)) :=
      ((continuous_sphereJetDensity k).comp_continuousOn
        (continuousOn_id.prodMk hi)).comp_continuous continuous_subtype_val
          (fun z => hS z.property)
    exact hci.aestronglyMeasurable
  · refine ⟨C+1, ?_⟩
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp huni 1 (by norm_num)] with i hi
    apply ae_of_all
    intro z
    have hb := hC z (hS z.property)
    have hd := hi z (hS z.property)
    have hh := dist_triangle
      (sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet (u i) z))
      (sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet v z)) 0
    simp only [dist_zero_right] at hh
    rw [dist_comm] at hd
    linarith
  · apply ae_of_all
    intro z
    exact huni.tendsto_at (hS z.property)

/-- The limit for actual d^c u wedge (dd^c u)^k, not a surrogate jet integral. -/
theorem unitSphereFlux_tendsto {k : ℕ} {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated]
    {u : I → ComplexEuclidean (k+1) → ℂ} {v : ComplexEuclidean (k+1) → ℂ}
    {K : Set (ComplexEuclidean (k+1))} (hK : IsCompact K)
    (hS : sphere (0 : ComplexEuclidean (k+1)) 1 ⊆ K)
    (hv : ContinuousOn (actualRealComplexJet v) K)
    (hu : ∀ᶠ i in l, ContinuousOn (actualRealComplexJet (u i)) K)
    (hdv : ∀ x ∈ K, DifferentiableAt ℝ (fderiv ℝ v) x)
    (hdu : ∀ᶠ i in l, ∀ x ∈ K, DifferentiableAt ℝ (fderiv ℝ (u i)) x)
    (h1 : TendstoUniformlyOn (fun i => fderiv ℝ (u i)) (fderiv ℝ v) l K)
    (h2 : TendstoUniformlyOn (fun i => fderiv ℝ (fderiv ℝ (u i)))
      (fderiv ℝ (fderiv ℝ v)) l K) :
    Tendsto (fun i => unitSphereFlux k (u i)) l (𝓝 (unitSphereFlux k v)) := by
  have ht := sphereJetIntegral_tendsto hK hS hv hu h1 h2
  have he : (fun i => unitSphereFlux k (u i)) =ᶠ[l]
      (fun i => ∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
        sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet (u i) z)
          ∂sphereArea (k+1)) := by
    filter_upwards [hdu] with i hi
    apply integral_congr_ae
    apply ae_of_all
    intro z
    exact congrArg (sphereDensity k z) (boundaryForm_eq_jet (hi z (hS z.property)) k)
  have hev : unitSphereFlux k v =
      ∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
        sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet v z)
          ∂sphereArea (k+1) := by
    apply integral_congr_ae
    apply ae_of_all
    intro z
    exact congrArg (sphereDensity k z) (boundaryForm_eq_jet (hdv z (hS z.property)) k)
  rw [hev]
  exact ht.congr' he.symm

end Mahler

end OAI
