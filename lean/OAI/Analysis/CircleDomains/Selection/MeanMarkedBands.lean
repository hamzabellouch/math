import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanGraphGeometry
import OAI.Analysis.CircleDomains.Probability.ArcBoundaryMeasure

namespace OAI

/-! Actual interval representatives for the marked fibers of the mean
period graph. At nonsingular marks their widths are bounded by the
original path-hit probability, not by an assumed graph-width budget. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem SmoothMeanPeriodData.exists_marked_band
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M : Set Sphere} (hdense : Dense U) {b : Sphere} {π : Sphere → Sphere}
    (hMS : M \ {b} ⊆ S) (hbS : b ∉ S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M b π)
    {x : Sphere} (hx : x ∉ U) :
    ∃ lo hi : ℝ, 0 ≤ hi - lo ∧
      hi - lo ≤ (if x = b then 1 else (η : Measure A).real {γ | x ∈ range γ.val}) ∧
      {θ : UnitAddCircle | (x, θ) ∈ periodBandGraph U M b Q.patch Q.branch} ⊆
        ((↑) : ℝ → UnitAddCircle) '' Icc lo hi := by
  classical
  by_cases hxb : x = b
  · refine ⟨0, 1, by norm_num, by simp only [hxb, ite_true, sub_zero, le_refl], ?_⟩
    intro θ _
    refine ⟨unitCircleCut θ, ?_, ?_⟩
    · simpa only [unitCircleCut, zero_add, mem_Icc] using
        (show (0 : ℝ) ≤ (AddCircle.equivIco (1 : ℝ) 0 θ : ℝ) ∧
          (AddCircle.equivIco (1 : ℝ) 0 θ : ℝ) ≤ 0 + 1 from
          ⟨(AddCircle.equivIco (1 : ℝ) 0 θ).property.1,
            (AddCircle.equivIco (1 : ℝ) 0 θ).property.2.le⟩)
    · simp only [unitCircleCut, AddCircle.coe_equivIco]
  by_cases hxM : x ∈ M
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp (Q.cover (hMS ⟨hxM, hxb⟩))
    let lo := liminf (Q.branch i) (𝓝[U] x)
    let hi := limsup (Q.branch i) (𝓝[U] x)
    let : NeBot (𝓝[U] x) := mem_closure_iff_nhdsWithin_neBot.mp
      (show x ∈ closure U by rw [hdense.closure_eq]; trivial)
    have hbnd : ∀ᶠ y in 𝓝[U] x, -(Q.bound i) ≤ Q.branch i y ∧ Q.branch i y ≤ Q.bound i :=
      Eventually.of_forall (fun y => abs_le.mp (Q.bounded i y))
    have hle : lo ≤ hi := liminf_le_limsup
      (isBoundedUnder_of_eventually_le (hbnd.mono fun _ h => h.2))
      (isBoundedUnder_of_eventually_ge (hbnd.mono fun _ h => h.1))
    refine ⟨lo, hi, sub_nonneg.mpr hle, ?_, ?_⟩
    · simpa only [hxb, ite_false] using Q.branch_width_le_hit hsch hsep A K hK hKS η F f hf
        hmap hdense h0 h1 hF i ⟨hxM, hx⟩ hxi
    · have hcompat : ∀ i j y, y ∈ Q.patch i → y ∈ Q.patch j → ∀ θ,
          (y, θ) ∈ circleBandGraph U (Q.branch i) ↔
            (y, θ) ∈ circleBandGraph U (Q.branch j) := by
        intro i j y hyi hyj θ
        obtain ⟨k, hk⟩ := Q.transition i j y hyi hyj
        exact (Set.ext_iff.mp (circleBand_fiber_eq_of_eventually_add_int hk) θ).symm
      rw [periodBandGraph_fiber_on_patch U M b Q.patch Q.branch
        (fun i hi => hbS (Q.patch_closure i (subset_closure hi))) hcompat hxM hxi,
        circleBandGraph_fiber_eq_image_realFiber,
        intervalFiberHull_clusterGraph_eq_boundary_band
          (fun y _ => Q.bounded i y) (show x ∈ closure U by rw [hdense.closure_eq]; trivial)]
  · refine ⟨0, 0, by norm_num, ?_, ?_⟩
    · simp only [hxb, ite_false, sub_self]
      exact measureReal_nonneg
    · intro θ hθ
      exact (hxM hθ.1).elim

 theorem SmoothMeanPeriodData.exists_marked_band_family
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M : Set Sphere} (hdense : Dense U) {b : Sphere} {π : Sphere → Sphere}
    (hMS : M \ {b} ⊆ S) (hbS : b ∉ S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M b π)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U)
    (hend : ∀ γ : A, b ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2)) :
    ∃ lo hi : T → ℝ,
      (∀ s, 0 ≤ hi s - lo s) ∧
      (∀ s, hi s - lo s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      Summable (fun s => (hi s - lo s) ^ 2) ∧
      ∀ s, {θ : UnitAddCircle | (σ s, θ) ∈ periodBandGraph U M b Q.patch Q.branch} ⊆
        ((↑) : ℝ → UnitAddCircle) '' Icc (lo s) (hi s) := by
  classical
  choose lo hi hnon hbound hfiber using fun s =>
    Q.exists_marked_band hsch hsep A K hK hKS η F f hf hmap hdense hMS hbS h0 h1 hF (hσ s)
  have hhit : (η : Measure A).real {γ | b ∈ range γ.val} = 1 := by
    have heq : {γ : A | b ∈ range γ.val} = univ := eq_univ_of_forall hend
    simp only [heq, measureReal_def, measure_univ, ENNReal.toReal_one]
  have hle (s : T) : hi s - lo s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val} := by
    by_cases hs : σ s = b
    · simpa only [hs, ite_true, hhit] using hbound s
    · simpa only [hs, ite_false] using hbound s
  refine ⟨lo, hi, hnon, hle, ?_, hfiber⟩
  exact Summable.of_nonneg_of_le (fun s => sq_nonneg _) (fun s =>
    (sq_le_sq₀ (hnon s) measureReal_nonneg).mpr (hle s)) hbudget

end CircleDomainRigidity

end

end OAI
