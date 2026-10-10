import OAI.Geometry.Immersion.ClosedSurface.TensorBounds
import OAI.Geometry.Immersion.ClosedSurface.FreeAmplitude
import OAI.Geometry.Immersion.ClosedSurface.ExtendedCancellation

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter



theorem real_finite_free_mode {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {U : Set Base} (h : RealModeDomain F U) {b : Base → ℝ}
    (hb : ContDiffOn ℝ ∞ b U) (δ : ℝ) {τ s K C : ℝ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + q + 1) K)
    (hbV : WeightedBound U s (m + q + 1) C (freeSeed δ τ b F)) :
    let Z := modeApprox τ (fun p => complexify (F p)) (freeSeed δ τ b F) (fun _ => 0) q
    ContDiffOn ℝ ∞ (realOsc τ Z) U ∧
    WeightedBound U τ m (2 ^ m * ((1 + freeModeConstant 4 m K q) * C)) (realOsc τ Z) ∧
    WeightedBound U τ m
      (2 ^ m * (fullErrorConstant 4 (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C))
      (realLinearizedTensor F (realOsc τ Z)) := by
  dsimp only
  have hv := freeSeed_isFree hF h δ τ hb
  have hd := h.complexDomain hF
  have hm := contDiffOn_modeApprox τ hd hv.smooth (f := fun _ => 0) contDiffOn_const q
  have ha := weighted_modeApprox_free hτ (contDiff_complexify hF) hd hs hτs hs1 hK hC
    hv.smooth hv.perpX hv.perpY hv.perpSecond q m hc hbV
  have hzero : WeightedBound U s (m + q + 1) C (fun _ : Base => (0 : Fin 3 → ℂ)) :=
    (weightedBound_zero U s _).mono_const hC
  have hr := weighted_residual_modeApprox hτ (contDiff_complexify hF) hd hs hs1 hK hC
    (f := fun _ => 0) contDiffOn_const hv.smooth hv.perpX hv.perpY hv.perpSecond q m
    hc.toFullModeCoefficientBound hzero hbV
  refine ⟨contDiffOn_realOsc hm τ, ?_, ?_⟩
  · exact weighted_realOsc h.isOpen hτ hτs
      (mul_nonneg (add_nonneg zero_le_one (freeModeConstant_nonneg 4 m q hK)) hC) hm ha
  · have hR := contDiffOn_residual τ hd hm (f := fun _ => 0) contDiffOn_const
    have hpos : 0 ≤ fullErrorConstant 4 (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C := by
      have hcpos := fullErrorConstant_nonneg 4 (m + q) hK
      positivity
    have hr' := weighted_realOsc h.isOpen hτ hτs hpos hR hr
    apply hr'.congr
    intro p hp
    have hx := realLinearized_residual (hF.differentiable (by simp) p)
      (hm.contDiffAt (h.isOpen.mem_nhds hp) |>.differentiableAt (by simp)) τ (fun _ => 0)
    have hz : realOsc τ (fun _ : Base => (0 : Fin 3 → ℂ)) p = 0 := by
      ext i
      simp [realOsc, oscillate, QuadraticMean.realPart]
    rw [hz, sub_zero] at hx
    exact hx

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter



theorem weighted_chart_free {F : RField 4} {χ e : Base → Base}
    (hFe : ContDiff ℝ ∞ (F ∘ e)) {U V : Set Base} (hU : IsOpen U)
    (h : RealModeDomain (F ∘ e) V)
    (hχ : ContDiffOn ℝ ∞ χ U) (hχV : MapsTo χ U V) (hinv : EqOn (e ∘ χ) id U)
    {b : Base → ℝ} (hb : ContDiffOn ℝ ∞ b V) (δ : ℝ)
    {τ s K C J D : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hJ : 1 ≤ J) (hD : 0 ≤ D) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify ((F ∘ e) p)) V s (m + q + 1) K)
    (hbV : WeightedBound V s (m + q + 1) C (freeSeed δ τ b (F ∘ e)))
    (hχc : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ j χ U p‖ ≤ J)
    (hχb : ∀ v, ‖v‖ ≤ 1 → WeightedBound U τ m D (coordDeriv v χ)) :
    let X := displacement τ (fun p => (χ p).1) (chartFreeAmplitude δ τ (F ∘ e) b q χ)
    let E := 2 ^ m * (fullErrorConstant 4 (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C)
    ContDiffOn ℝ ∞ X U ∧
    WeightedBound U τ m
      ((m.factorial : ℝ) * (2 ^ m * ((1 + freeModeConstant 4 m K q) * C)) * J ^ m) X ∧
    WeightedBound U τ m
      (4 * (2 ^ m * (2 ^ m * ((m.factorial : ℝ) * E * J ^ m) * D) * D))
      (realLinearizedTensor F X) := by
  let Z := modeApprox τ (fun p => complexify ((F ∘ e) p))
    (freeSeed δ τ b (F ∘ e)) (fun _ => 0) q
  have hh := real_finite_free_mode hFe h hb δ hτ hs hτs hs1 hK hC q m hc hbV
  dsimp only at hh ⊢
  have hxdef : displacement τ (fun p => (χ p).1)
      (chartFreeAmplitude δ τ (F ∘ e) b q χ) = realOsc τ Z ∘ χ :=
    (realOsc_comp τ Z χ).symm
  rw [hxdef]
  have hsizepos : 0 ≤ 2 ^ m * ((1 + freeModeConstant 4 m K q) * C) := by
    have hpos := freeModeConstant_nonneg 4 m q hK
    positivity
  have herrorpos : 0 ≤ 2 ^ m *
      (fullErrorConstant 4 (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C) := by
    have hpos := fullErrorConstant_nonneg 4 (m + q) hK
    positivity
  have hτ1 := hτs.trans hs1
  have hxsm : ContDiffOn ℝ ∞ (realOsc τ Z) V := hh.1
  have hR := contDiffOn_realLinearizedTensor h.isOpen hFe.contDiffOn hxsm
  have hRC := hR.comp hχ hχV
  refine ⟨hxsm.comp hχ hχV, ?_, ?_⟩
  · change WeightedBound U τ m _ (realOsc τ Z ∘ χ)
    exact hh.2.1.comp_coordinates hU.uniqueDiffOn h.isOpen.uniqueDiffOn hτ hτ1 hJ
      hsizepos hχ hxsm hχV hχc
  · have hRCB := hh.2.2.comp_coordinates hU.uniqueDiffOn h.isOpen.uniqueDiffOn hτ hτ1 hJ
      herrorpos hχ hR hχV hχc
    have hpull := weighted_pullbackField_apply hU hτ (by positivity) hD hRC hχ hRCB hχb
    apply hpull.congr
    intro p hp
    have hi : (F ∘ e) ∘ χ =ᶠ[nhds p] F := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact congrArg F (hinv hx)
    change realLinearizedTensor F (realOsc τ Z ∘ χ) p = _
    rw [← realLinearizedTensor_congr_left hi]
    exact realLinearizedTensor_comp (hFe.differentiable (by simp) (χ p))
      (hxsm.contDiffAt (h.isOpen.mem_nhds (hχV hp)) |>.differentiableAt (by simp))
      (hχ.contDiffAt (hU.mem_nhds hp) |>.differentiableAt (by simp))

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.RootMean Set Filter
open ClosedSurfaceR4.QuadraticMean (displacement)

lemma realLinearizedTensor_indicator {n : ℕ} {U S : Set Base} (hU : IsOpen U)
    (hS : IsClosed S) (hSU : S ⊆ U) (F X : RField n)
    (hz : ∀ p ∈ U, p ∉ S → X p = 0) :
    realLinearizedTensor F (U.indicator X) = U.indicator (realLinearizedTensor F X) := by
  classical
  funext p
  by_cases hp : p ∈ U
  · rw [indicator_of_mem hp]
    apply realLinearizedTensor_congr_right
    filter_upwards [hU.mem_nhds hp] with x hx
    exact indicator_of_mem hx X
  · rw [indicator_of_notMem hp]
    have hzero : U.indicator X =ᶠ[nhds p] fun _ => 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hh => hp (hSU ((tsupport_indicator_subset hS hz) hh)))
    rw [realLinearizedTensor_congr_right hzero, realLinearizedTensor_zero_right]

lemma displacement_indicator {n : ℕ} (U : Set Base) (τ : ℝ) (φ : Base → ℝ) (Z : Field n) :
    displacement τ φ (U.indicator Z) = U.indicator (displacement τ φ Z) := by
  classical
  funext p
  by_cases hp : p ∈ U
  · simp only [indicator_of_mem hp, displacement]
  · rw [indicator_of_notMem hp]
    apply displacement_zero_value
    exact indicator_of_notMem hp Z



theorem weighted_extended_chart_free {F : RField 4} {χ e : Base → Base}
    (hFe : ContDiff ℝ ∞ (F ∘ e)) {U V S : Set Base} (hU : IsOpen U)
    (h : RealModeDomain (F ∘ e) V) (hS : IsClosed S) (hSU : S ⊆ U)
    (hχ : ContDiffOn ℝ ∞ χ U) (hχV : MapsTo χ U V) (hinv : EqOn (e ∘ χ) id U)
    {ψ u : Base → ℝ} (hb : ContDiffOn ℝ ∞ (phaseAmplitude ψ u) V)
    (hsp : ∀ p ∈ U, χ p ∈ tsupport ψ → p ∈ S) (δ : ℝ)
    {τ s K C J D : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hJ : 1 ≤ J) (hD : 0 ≤ D) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify ((F ∘ e) p)) V s (m + q + 1) K)
    (hbV : WeightedBound V s (m + q + 1) C (freeSeed δ τ (phaseAmplitude ψ u) (F ∘ e)))
    (hχc : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ j χ U p‖ ≤ J)
    (hχb : ∀ v, ‖v‖ ≤ 1 → WeightedBound U τ m D (coordDeriv v χ)) :
    let X := displacement τ (fun p => (χ p).1)
      (U.indicator (chartFreeAmplitude δ τ (F ∘ e) (phaseAmplitude ψ u) q χ))
    let E := 2 ^ m * (fullErrorConstant 4 (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C)
    ContDiff ℝ ∞ X ∧ tsupport X ⊆ S ∧
    WeightedBound univ τ m
      ((m.factorial : ℝ) * (2 ^ m * ((1 + freeModeConstant 4 m K q) * C)) * J ^ m) X ∧
    WeightedBound univ τ m
      (4 * (2 ^ m * (2 ^ m * ((m.factorial : ℝ) * E * J ^ m) * D) * D))
      (realLinearizedTensor F X) := by
  dsimp only
  rw [displacement_indicator]
  have hh := weighted_chart_free hFe hU h hχ hχV hinv hb δ hτ hs hτs hs1
    hK hC hJ hD q m hc hbV hχc hχb
  dsimp only at hh
  have hzA := chartFree_vanishes hsp δ τ (F ∘ e) u q
  have hz : ∀ p ∈ U, p ∉ S → displacement τ (fun p => (χ p).1)
      (chartFreeAmplitude δ τ (F ∘ e) (phaseAmplitude ψ u) q χ) p = 0 := by
    intro p hp hn
    exact displacement_zero_value τ _ (hzA p hp hn)
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  have hsizepos := freeModeConstant_nonneg 4 m q hK
  have herrorpos := fullErrorConstant_nonneg 4 (m + q) hK
  refine ⟨contDiff_indicator_of_support hU hS hSU hh.1 hz,
    tsupport_indicator_subset hS hz,
    hh.2.1.indicator_of_support hU hS hSU (by positivity) hz, ?_⟩
  rw [realLinearizedTensor_indicator hU hS hSU _ _ hz]
  apply hh.2.2.indicator_of_support hU hS hSU (by positivity)
  intro p hp hn
  have heq : displacement τ (fun p => (χ p).1)
      (chartFreeAmplitude δ τ (F ∘ e) (phaseAmplitude ψ u) q χ) =ᶠ[nhds p] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hp, hS.isOpen_compl.mem_nhds hn] with x hxU hxS
    exact hz x hxU hxS
  rw [realLinearizedTensor_congr_right heq, realLinearizedTensor_zero_right]

end ClosedSurfaceR4.RealModes

end

end OAI
