import OAI.Analysis.CircleDomains.Uniformization.BandLimits
import OAI.Analysis.CircleDomains.Modulus.LevelIncidence

namespace OAI

/-! Pointwise contraction of boundary intervals preserves compatibility
of the new coordinate with the fixed earlier coordinates. -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem real_band_subset_of_liminf_limsup
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [CompactSpace X] [T2Space X]
    (U : Set X) (u v : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1) (hv : ∀x, v x ∈ Icc 0 1)
    {x : X} (hx : x ∈ closure U)
    (hlo : liminf u (𝓝[U] x) ≤ liminf v (𝓝[U] x))
    (hhi : limsup v (𝓝[U] x) ≤ limsup u (𝓝[U] x)) :
    {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph U v)} ⊆
      {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph U u)} := by
  have hu' : ∀x ∈ U, |u x| ≤ 1 := fun x _ => abs_le.mpr ⟨by linarith [(hu x).1], (hu x).2⟩
  have hv' : ∀x ∈ U, |v x| ≤ 1 := fun x _ => abs_le.mpr ⟨by linarith [(hv x).1], (hv x).2⟩
  rw [intervalFiberHull_clusterGraph_eq_boundary_band hv' hx,
    intervalFiberHull_clusterGraph_eq_boundary_band hu' hx]
  exact Icc_subset_Icc hlo hhi

theorem circle_band_subset_of_real_band
    {X : Type*} [TopologicalSpace X] (U : Set X) (u v : X → ℝ) {x : X}
    (h : {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph U v)} ⊆
      {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph U u)}) :
    ∀t, (x, t) ∈ circleBandGraph U v → (x, t) ∈ circleBandGraph U u := by
  intro t ht
  obtain ⟨⟨y, r⟩, hr, heq⟩ := ht
  have hy : y = x := congrArg Prod.fst heq
  subst y
  exact ⟨(x, r), h hr, heq⟩

theorem freeComponentFailure_mono_new
    {X T J Λ : Type*} [TopologicalSpace X]
    (F : Set X) (Rnew Snew : Set (X × T)) (R : Λ → Set (X × T)) (labels : J → Λ)
    (hsub : ∀x ∈ F, ∀t, (x, t) ∈ Rnew → (x, t) ∈ Snew) :
    freeComponentFailure F Rnew R labels ⊆ freeComponentFailure F Snew R labels := by
  rintro t ⟨⟨x, s⟩, hx, heq⟩
  exact ⟨(x, s), ⟨hx.1, hsub x hx.1 s.1 hx.2.1, hx.2.2⟩, heq⟩

theorem band_contraction_preserves_compatibility
    {X T J Λ : Type*} [TopologicalSpace X]
    [TopologicalSpace T] [MeasurableSpace (T × (J → T))]
    (μ : Measure (T × (J → T))) (F : Set X)
    (Rnew Snew : Set (X × T)) (R : Λ → Set (X × T)) (labels : J → Λ)
    (hsub : ∀x ∈ F, ∀t, (x, t) ∈ Rnew → (x, t) ∈ Snew)
    (hzero : μ (freeComponentFailure F Snew R labels) = 0) :
    μ (freeComponentFailure F Rnew R labels) = 0 :=
  measure_mono_null (freeComponentFailure_mono_new F Rnew Snew R labels hsub) hzero

end CircleDomainRigidity

end

end OAI
