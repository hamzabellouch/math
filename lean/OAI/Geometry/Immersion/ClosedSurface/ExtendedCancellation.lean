import OAI.Geometry.Immersion.ClosedSurface.SupportedCancellation

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter



lemma phaseCanceller_vanishes_local {n : ℕ} {U V S : Set Base} (hV : IsOpen V)
    {χ e : Base → Base} (he : ContinuousOn e V) (hχV : MapsTo χ U V)
    (hinv : EqOn (e ∘ χ) id U) {A : Base → ComplexTensor} (hAsp : tsupport A ⊆ S)
    (τ : ℝ) (F : RField n) (q : ℕ) :
    ∀ p ∈ U, p ∉ S → phaseCanceller τ F χ e A q p = 0 := by
  intro p hp hn
  have hAz : ∀ᶠ y in nhds (e (χ p)), A y = 0 := by
    rw [show e (χ p) = p from hinv hp]
    exact notMem_tsupport_iff_eventuallyEq.mp (fun hh => hn (hAsp hh))
  have hec := (he (χ p) (hχV hp)).continuousAt (hV.mem_nhds (hχV hp))
  have hAe : ∀ᶠ y in nhds (χ p), A (e y) = 0 := hec.tendsto.eventually hAz
  have ht : χ p ∉ tsupport (coordinateTarget e A) := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [hAe] with x hx
    simp only [coordinateTarget, hx, map_zero, Pi.zero_apply]
  have htn : χ p ∉ tsupport (fun p => -coordinateTarget e A p) := by simpa using ht
  have hz : χ p ∉ tsupport (phaseCancelAmplitude τ F e A q) := by
    intro hh
    exact htn (forcedMode_tsupport τ (fun p => complexify (F (e p)))
      (fun p => -coordinateTarget e A p) q hh)
  change realOsc τ (phaseCancelAmplitude τ F e A q) (χ p) = 0
  exact image_eq_zero_of_notMem_tsupport
    (fun hh => hz (realOsc_tsupport τ (phaseCancelAmplitude τ F e A q) hh))

lemma displacement_zero_value {n : ℕ} (τ : ℝ) (φ : Base → ℝ) {A : Field n}
    {p : Base} (hA : A p = 0) : displacement τ φ A p = 0 := by
  ext i
  simp [displacement, QuadraticMean.realMode, QuadraticMean.realPart, hA]

lemma linearized_error_vanishes {n : ℕ} {U S : Set Base} (hU : IsOpen U)
    (hS : IsClosed S) {F X : RField n} {A : Base → ComplexTensor}
    (hX : ∀ p ∈ U, p ∉ S → X p = 0) (hAsp : tsupport A ⊆ S)
    (τ : ℝ) (φ : Base → ℝ) :
    ∀ p ∈ U, p ∉ S → realLinearizedTensor F X p + displacement τ φ A p = 0 := by
  intro p hp hn
  have hEq : X =ᶠ[nhds p] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hp, hS.isOpen_compl.mem_nhds hn] with x hxU hxS
    exact hX x hxU hxS
  rw [realLinearizedTensor_congr_right hEq, realLinearizedTensor_zero_right,
    displacement_zero_value τ φ (image_eq_zero_of_notMem_tsupport (fun hh => hn (hAsp hh))), zero_add]



theorem phaseCanceller_extend {n : ℕ} {U V S : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    (hS : IsClosed S) (hSU : S ⊆ U) {F : RField n} {χ e : Base → Base}
    (he : ContinuousOn e V) (hχV : MapsTo χ U V) (hinv : EqOn (e ∘ χ) id U)
    {A : Base → ComplexTensor} (hAsp : tsupport A ⊆ S) (τ : ℝ) (q m : ℕ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hsm : ContDiffOn ℝ ∞ (phaseCanceller τ F χ e A q) U)
    (hb : WeightedBound U τ m C (phaseCanceller τ F χ e A q))
    (hr : WeightedBound U τ m D (fun p => realLinearizedTensor F (phaseCanceller τ F χ e A q) p +
      displacement τ (fun p => (χ p).1) A p)) :
    let X := U.indicator (phaseCanceller τ F χ e A q)
    ContDiff ℝ ∞ X ∧ tsupport X ⊆ S ∧ WeightedBound univ τ m C X ∧
      WeightedBound univ τ m D
        (fun p => realLinearizedTensor F X p + displacement τ (fun p => (χ p).1) A p) := by
  dsimp only
  have hz := phaseCanceller_vanishes_local hV he hχV hinv hAsp τ F q
  refine ⟨contDiff_indicator_of_support hU hS hSU hsm hz,
    tsupport_indicator_subset hS hz, hb.indicator_of_support hU hS hSU hC hz, ?_⟩
  have hext := hr.indicator_of_support hU hS hSU hD (linearized_error_vanishes hU hS hz hAsp τ _)
  rwa [indicator_linearized_error hU hS hSU hz hAsp τ (fun p => (χ p).1)] at hext



theorem weighted_extended_phaseCanceller {n : ℕ} {F : RField n} {χ e : Base → Base}
    (hFe : ContDiff ℝ ∞ (F ∘ e)) {U V S : Set Base} (hU : IsOpen U)
    (h : ModeDomain (fun p => complexify (F (e p))) V)
    (hS : IsClosed S) (hSU : S ⊆ U)
    (hχ : ContDiffOn ℝ ∞ χ U) (he : ContDiffOn ℝ ∞ e V)
    (hχV : MapsTo χ U V) (hinv : EqOn (e ∘ χ) id U)
    (hF : ContDiffOn ℝ ∞ F U) {A : Base → ComplexTensor} (hAsp : tsupport A ⊆ S)
    {τ s K C J D : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hA : ContDiffOn ℝ ∞ (coordinateTarget e A) V) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F (e p))) V s (m + q + 1) K)
    (hb : WeightedBound V s (m + q + 1) C (coordinateTarget e A))
    (hχc : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ j χ U p‖ ≤ J)
    (hχb : ∀ v, ‖v‖ ≤ 1 → WeightedBound U τ m D (coordDeriv v χ)) :
    let X := U.indicator (phaseCanceller τ F χ e A q)
    let E := 2 ^ m * (fullErrorConstant n (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C)
    ContDiff ℝ ∞ X ∧ tsupport X ⊆ S ∧
    WeightedBound univ τ m
      ((m.factorial : ℝ) * (2 ^ m * (forcedModeConstant n m K q * C)) * J ^ m) X ∧
    WeightedBound univ τ m
      (4 * (2 ^ m * (2 ^ m * ((m.factorial : ℝ) * E * J ^ m) * D) * D))
      (fun p => realLinearizedTensor F X p + displacement τ (fun p => (χ p).1) A p) := by
  dsimp only
  have hh := weighted_phaseCanceller hFe hU h hχ he hχV hinv hF hτ hs hτs hs1
    hK hC hJ hD hA q m hc hb hχc hχb
  dsimp only at hh
  apply phaseCanceller_extend hU h.isOpen hS hSU he.continuousOn hχV hinv hAsp τ q m
    _ _ hh.1 hh.2.1 hh.2.2
  · have hpos := forcedModeConstant_nonneg n m q hK
    have hJ0 : 0 ≤ J := le_trans zero_le_one hJ
    positivity
  · have hpos := fullErrorConstant_nonneg n (m + q) hK
    have hJ0 : 0 ≤ J := le_trans zero_le_one hJ
    positivity

end ClosedSurfaceR4.RealModes

end

end OAI
