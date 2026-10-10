import OAI.Analysis.CircleDomains.Selection.PerturbedMeanBands
import OAI.Analysis.CircleDomains.Transfer.LogarithmicCutCharts
import OAI.Analysis.CircleDomains.Modulus.PeriodBandBudget
import OAI.Analysis.CircleDomains.Selection.LiftedMeanBands

namespace OAI

/-! The actual smoothed mean-period graph is paid for by the selected
law's point-hit probabilities, with unit budget at its terminal point. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
theorem logarithmicCutChart_im_pos (a : ℝ) {z : ℂ} (h0 : z ≠ 0) (h1 : ‖z‖ < 1) :
    0 < (logarithmicCutChart a z).im := by
  have hlog := Real.log_neg (norm_pos_iff.mpr h0) h1
  simpa only [logarithmicCutChart, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, zero_add] using neg_pos.mpr hlog

variable [MeasurableSpace C(PathTime, Sphere)]

theorem mean_period_graph_incidence_le_hit
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (U M S : Set Sphere) (hU : IsOpen U) (hdense : Dense U) (b : Sphere)
    (h0 : ∀ x ∈ S, F x ≠ 0)
    (h1 : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ x ∈ M \ (U ∪ {b}), ∀ γ : A, InjOn F (range γ.val ∪ {x}))
    {I : Type*} (V : I → Set Sphere) (hV : ∀ i, IsOpen (V i))
    (hVS : ∀ i, closure (V i) ⊆ S) (hbV : ∀ i, b ∉ V i)
    (hcover : M \ {b} ⊆ ⋃ i, V i)
    (a B : I → ℝ) (u : I → Sphere → ℝ)
    (hbound : ∀ i x, x ∈ U → |u i x| ≤ B i)
    (hcont : ∀ i, ContinuousOn (u i) (U ∩ V i))
    (hlog : ∀ i, ContinuousOn (fun x => logarithmicCutChart (a i) (F x)) (closure (V i)))
    (htrans : ∀ i j x, x ∈ V i → x ∈ V j →
      ∃ k : ℤ, u j =ᶠ[𝓝[U] x] fun y => u i y + k)
    (error : Sphere → ℝ) (herror : ∀ x ∈ M \ U, Tendsto error (𝓝[U] x) (𝓝 0))
    (hu : ∀ i x, x ∈ V i → u i x =
      meanGeometricIndex hsch K hKS (η.map f)
        (upperHalfPlaneClamp (logarithmicCutChart (a i) (F x))) + error x)
    (x : Sphere) :
    volume {θ | (x, θ) ∈ periodBandGraph U M b V u} ≤
      if x = b then 1 else (η : Measure A) {γ | x ∈ range γ.val} := by
  classical
  apply periodBandGraph_incidence_le_budget U M hdense b V hbV hcover u B hbound
  · intro i j y hi hj θ
    obtain ⟨k, hk⟩ := htrans i j y hi hj
    exact (Set.ext_iff.mp (circleBand_fiber_eq_of_eventually_add_int hk) θ).symm
  · simp only [ite_true]
    exact le_rfl
  · intro i y hy
    have hyb : y ≠ b := fun he => hbV i (he ▸ hy.2)
    simp only [hyb, ite_false]
    let : NeBot (𝓝[U] y) := mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [hdense.closure_eq]; trivial)
    by_cases hyU : y ∈ U
    · have ht : Tendsto (u i) (𝓝[U] y) (𝓝 (u i y)) :=
        ((hcont i).continuousAt ((hU.inter (hV i)).mem_nhds ⟨hyU, hy.2⟩)).continuousWithinAt
      rw [ht.limsup_eq, ht.liminf_eq, sub_self, ENNReal.ofReal_zero]
      exact bot_le
    · have hyS : y ∈ S := hVS i (subset_closure hy.2)
      let L : Sphere → ClosedUpperHalfPlane := fun z =>
        upperHalfPlaneClamp (logarithmicCutChart (a i) (F z))
      have hLC : ContinuousAt L y := continuous_upperHalfPlaneClamp.continuousAt.comp
        ((hlog i).continuousAt (mem_of_superset ((hV i).mem_nhds hy.2) subset_closure))
      have him : 0 < (logarithmicCutChart (a i) (F y)).im :=
        logarithmicCutChart_im_pos (a i) (h0 y hyS) (h1 y ⟨hy.1, hyU⟩)
      have hLv : (L y).val = logarithmicCutChart (a i) (F y) :=
        upperHalfPlaneClamp_val him.le
      have hproj : diskRayProjection (L y).val = F y := by
        rw [hLv]
        exact logarithmicCutChart_projection (a i) (h0 y hyS)
      have heq : (fun z => u i z - meanGeometricIndex hsch K hKS (η.map f) (L z))
          =ᶠ[𝓝[U] y] error := by
        filter_upwards [nhdsWithin_le_nhds ((hV i).mem_nhds hy.2)] with z hz
        rw [hu i z hz]
        exact add_sub_cancel_left _ _
      have herr := (herror y ⟨hy.1, hyU⟩).congr' heq.symm
      have hbnd := (perturbed_mapped_mean_bands hsch hsep A K hK hKS η F f hf hmap y
        (hF y ⟨hy.1, fun h => h.elim hyU hyb⟩) U y
        (by rw [hdense.closure_eq]; trivial) L hLC.continuousWithinAt
        (by simpa only [hLv] using him) hproj (u i) herr).2.2
      apply (ENNReal.ofReal_le_ofReal hbnd).trans
      rw [ofReal_measureReal]

end CircleDomainRigidity

end

end OAI
