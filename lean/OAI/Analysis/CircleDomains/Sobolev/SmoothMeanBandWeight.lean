import OAI.Analysis.CircleDomains.Probability.ExactBandMeasure
import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanPeriodConsequences

namespace OAI

/-! Local branch widths are controlled by the actual masked-coordinate
weights. Exact Haar length prevents a change of branch from weakening
the weight used by subsequent code laws. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem SmoothMeanPeriodData.branch_width_le_dustWeight
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M B : Set Sphere} (hdense : Dense U) {b : Sphere} {π : Sphere → Sphere}
    (hbS : b ∉ S) (hBU : B ⊆ Uᶜ)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M b π)
    (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hgraph : C.graph = periodBandGraph U M b Q.patch Q.branch)
    (i : Q.Index) {x : Sphere} (hx : x ∈ B ∩ M) (hxi : x ∈ Q.patch i) :
    ENNReal.ofReal (limsup (Q.branch i) (𝓝[U] x) -
      liminf (Q.branch i) (𝓝[U] x)) ≤ C.dustWeight x := by
  have hwidth : limsup (Q.branch i) (𝓝[U] x) -
      liminf (Q.branch i) (𝓝[U] x) ≤ 1 :=
    (Q.branch_width_le_hit hsch hsep A K hK hKS η F f hf hmap hdense h0 h1 hF i
      ⟨hx.2, hBU hx.1⟩ hxi).trans measureReal_le_one
  have hcompat : ∀ i j y, y ∈ Q.patch i → y ∈ Q.patch j → ∀ θ,
      (y, θ) ∈ circleBandGraph U (Q.branch i) ↔
        (y, θ) ∈ circleBandGraph U (Q.branch j) := by
    intro i j y hyi hyj θ
    obtain ⟨k, hk⟩ := Q.transition i j y hyi hyj
    exact (Set.ext_iff.mp (circleBand_fiber_eq_of_eventually_add_int hk) θ).symm
  have hsub : {θ : UnitAddCircle | (x, θ) ∈ circleBandGraph U (Q.branch i)} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (C.lower ⟨x, hx.1⟩) (C.upper ⟨x, hx.1⟩) := by
    intro θ hθ
    apply C.marked_fiber ⟨x, hx.1⟩
    rw [hgraph]
    exact (periodBandGraph_on_patch U M b Q.patch Q.branch
      (fun j hj => hbS (Q.patch_closure j (subset_closure hj))) hcompat hxi θ).mpr ⟨hx.2, hθ⟩
  simpa only [MaskedCoordinateData.dustWeight, dite_eq_left hx.1] using
    band_width_le_of_fiber_subset (fun y _ => Q.bounded i y)
      (show x ∈ closure U by rw [hdense.closure_eq]; trivial) hwidth hsub

 omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem masked_singular_weight_ge_one
    {G U M B : Set Sphere} {b : Sphere} {π : Sphere → Sphere}
    {I : Type*} (patch : I → Set Sphere) (branch : I → Sphere → ℝ)
    (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hgraph : C.graph = periodBandGraph U M b patch branch)
    (hb : b ∈ B) (hbM : b ∈ M) : 1 ≤ C.dustWeight b := by
  have hsub : (univ : Set UnitAddCircle) ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (C.lower ⟨b, hb⟩) (C.upper ⟨b, hb⟩) := by
    intro θ _
    apply C.marked_fiber ⟨b, hb⟩
    rw [hgraph]
    exact periodBandGraph_singular U M b patch branch hbM θ
  have h := (measure_mono (μ := (volume : Measure UnitAddCircle)) hsub).trans
    ((volume_addCircle_image_Icc_le _ _).trans
      (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  simpa only [MaskedCoordinateData.dustWeight, dite_eq_left hb, AddCircle.measure_univ, ENNReal.ofReal_one] using h

end CircleDomainRigidity

end

end OAI
