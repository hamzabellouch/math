import OAI.Geometry.RCD.Transport.WeakLengthCompression

namespace OAI

/-! # Tight endpoint tails give tight geodesic plans

Properness makes the bounded families of geodesics compact. Both endpoint
tails control the mass outside those families, uniformly in the sequence.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] [SeparableSpace X] in
theorem geodesic_plans_tight_of_endpoint_tails
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (p : X)
    (hg : ∀ j, ∀ᵐ γ ∂(πs j : Measure C(Time,X)), IsGeodesic γ)
    (htail : ∀ ε : ℝ≥0∞, 0<ε → ∃ R : ℝ, 0≤R ∧ ∀ j,
      (πs j : Measure C(Time,X)) {γ | R<dist (γ 0) p}+
      (πs j : Measure C(Time,X)) {γ | R<dist (γ 1) p}≤ε) :
    IsTightMeasureSet {((ρ : ProbabilityMeasure C(Time,X)) : Measure C(Time,X)) | ρ∈Set.range πs} := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  obtain ⟨R,hR,hRtail⟩ := htail ε hε
  let F := {γ : C(Time,X) | IsGeodesic γ ∧ ∀ t, dist (γ t) p≤3*R}
  refine ⟨F,isCompact_bounded_geodesics p (mul_nonneg (by norm_num) hR),?_⟩
  rintro ν ⟨ρ,⟨j,rfl⟩,rfl⟩
  have hsub : ∀ᵐ γ ∂(πs j : Measure C(Time,X)), γ∈Fᶜ →
      γ∈({γ | R<dist (γ 0) p}∪{γ | R<dist (γ 1) p}) := by
    filter_upwards [hg j] with γ hγ
    intro hnot
    by_contra ht
    have h0 : dist (γ 0) p≤R := not_lt.mp (fun h => ht (Or.inl h))
    have h1 : dist (γ 1) p≤R := not_lt.mp (fun h => ht (Or.inr h))
    have hstay (t : Time) : dist (γ t) p≤3*R := by
      have hlen : dist (γ 0) (γ 1)≤2*R := by
        have hd := dist_triangle (γ 0) p (γ 1)
        rw [dist_comm p (γ 1)] at hd
        linarith
      have habs : |(t:ℝ)-(0:Time)|≤1 := by
        change |(t:ℝ)-0|≤1
        rw [sub_zero,abs_of_nonneg t.property.1]
        exact t.property.2
      calc
        _ ≤ dist (γ t) (γ 0)+dist (γ 0) p := dist_triangle _ _ _
        _ = |(t:ℝ)-(0:Time)| * dist (γ 0) (γ 1)+dist (γ 0) p := by rw [hγ t 0]
        _ ≤ 1*(2*R)+R := add_le_add (mul_le_mul habs hlen dist_nonneg (by norm_num)) h0
        _ = _ := by ring
    exact hnot ⟨hγ,hstay⟩
  exact (measure_mono_ae hsub).trans ((measure_union_le _ _).trans (hRtail j))

omit [MeasurableSpace X] [BorelSpace X] in
theorem geodesic_plans_subsequence_of_endpoint_tails
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (p : X)
    (hg : ∀ j, ∀ᵐ γ ∂(πs j : Measure C(Time,X)), IsGeodesic γ)
    (htail : ∀ ε : ℝ≥0∞, 0<ε → ∃ R : ℝ, 0≤R ∧ ∀ j,
      (πs j : Measure C(Time,X)) {γ | R<dist (γ 0) p}+
      (πs j : Measure C(Time,X)) {γ | R<dist (γ 1) p}≤ε) :
    ∃ π : ProbabilityMeasure C(Time,X), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (πs ∘ φ) atTop (𝓝 π) := by
  have hc := isCompact_closure_of_isTightMeasureSet
    (geodesic_plans_tight_of_endpoint_tails πs p hg htail)
  obtain ⟨π,_,φ,hφ,hlim⟩ := hc.tendsto_subseq (fun j => subset_closure (mem_range_self j))
  exact ⟨π,φ,hφ,hlim⟩

end RegularPointCoordinates

end

end OAI
