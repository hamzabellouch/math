import OAI.Geometry.Immersion.ClosedSurface.PhaseCancellation
import OAI.Geometry.Immersion.ClosedSurface.PullbackBounds

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.QuadraticMean (displacement)




theorem weighted_phaseCanceller {n : ℕ} {F : RField n} {χ e : Base → Base}
    (hFe : ContDiff ℝ ∞ (F ∘ e)) {U V : Set Base} (hU : IsOpen U)
    (h : ModeDomain (fun p => complexify (F (e p))) V)
    (hχ : ContDiffOn ℝ ∞ χ U) (he : ContDiffOn ℝ ∞ e V)
    (hχV : Set.MapsTo χ U V) (hinv : Set.EqOn (e ∘ χ) id U)
    (hF : ContDiffOn ℝ ∞ F U) {A : Base → ComplexTensor}
    {τ s K C J D : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hA : ContDiffOn ℝ ∞ (coordinateTarget e A) V) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F (e p))) V s (m + q + 1) K)
    (hb : WeightedBound V s (m + q + 1) C (coordinateTarget e A))
    (hχc : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ j χ U p‖ ≤ J)
    (hχb : ∀ v, ‖v‖ ≤ 1 → WeightedBound U τ m D (coordDeriv v χ)) :
    let E := 2 ^ m * (fullErrorConstant n (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C)
    ContDiffOn ℝ ∞ (phaseCanceller τ F χ e A q) U ∧
    WeightedBound U τ m
      ((m.factorial : ℝ) * (2 ^ m * (forcedModeConstant n m K q * C)) * J ^ m)
      (phaseCanceller τ F χ e A q) ∧
    WeightedBound U τ m
      (4 * (2 ^ m * (2 ^ m * ((m.factorial : ℝ) * E * J ^ m) * D) * D))
      (fun p => realLinearizedTensor F (phaseCanceller τ F χ e A q) p +
        displacement τ (fun p => (χ p).1) A p) := by
  dsimp only
  have hforce := real_finite_forced_mode hFe h hτ hs hτs hs1 hK hC hA.neg q m hc
    (hb.neg h.isOpen.uniqueDiffOn hA)
  dsimp only at hforce
  have hτ1 : τ ≤ 1 := hτs.trans hs1
  have hAC : 0 ≤ 2 ^ m * (forcedModeConstant n m K q * C) :=
    mul_nonneg (by positivity) (mul_nonneg (forcedModeConstant_nonneg _ _ _ hK) hC)
  have hEC : 0 ≤ 2 ^ m *
      (fullErrorConstant n (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg
      (pow_nonneg (fullErrorConstant_nonneg _ _ hK) _) (pow_nonneg (div_nonneg hτ.le hs.le) _)) hC)
  have hZ := contDiffOn_modeApprox τ h (V := fun _ => 0) contDiffOn_const hA.neg q
  have hR := contDiffOn_realOsc (contDiffOn_residual τ h hZ hA.neg) τ
  have hRB : WeightedBound V τ m
      (2 ^ m * (fullErrorConstant n (m + q) K ^ (q + 1) * (τ / s) ^ (q + 1) * C))
      (realOsc τ (SmallModes.residual τ (fun p => complexify (F (e p)))
        (fun p => -coordinateTarget e A p) (phaseCancelAmplitude τ F e A q))) := by
    apply hforce.2.2.congr
    intro p hp
    exact (realLinearized_residual (hFe.differentiable (by simp) p)
      (hZ.contDiffAt (h.isOpen.mem_nhds hp) |>.differentiableAt (by simp)) τ
      (fun p => -coordinateTarget e A p)).symm
  refine ⟨hforce.1.comp hχ hχV, ?_, ?_⟩
  · exact hforce.2.1.comp_coordinates hU.uniqueDiffOn h.isOpen.uniqueDiffOn hτ hτ1 hJ
      hAC hχ hforce.1 hχV hχc
  · have hRC := hR.comp hχ hχV
    have hRCB := hRB.comp_coordinates hU.uniqueDiffOn h.isOpen.uniqueDiffOn hτ hτ1 hJ
      hEC hχ hR hχV hχc
    have hpull := weighted_pullbackField_apply hU hτ (by positivity) hD hRC hχ hRCB hχb
    apply hpull.congr
    intro p hp
    have hi : e ∘ χ =ᶠ[nhds p] id := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact hinv hx
    have hip : e (χ p) = p := hinv hp
    apply phaseCanceller_residual
    · rw [hip]
      exact hF.contDiffAt (hU.mem_nhds hp) |>.differentiableAt (by simp)
    · exact he.contDiffAt (h.isOpen.mem_nhds (hχV hp)) |>.differentiableAt (by simp)
    · exact hχ.contDiffAt (hU.mem_nhds hp) |>.differentiableAt (by simp)
    · exact hi
    · exact hZ.contDiffAt (h.isOpen.mem_nhds (hχV hp)) |>.differentiableAt (by simp)

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.SmallModes
open Set

lemma modeApprox_tsupport {n : ℕ} (τ : ℝ) (G V : Field n) (f : Tensor) (q : ℕ) :
    tsupport (modeApprox τ G V f q) ⊆ tsupport V ∪ tsupport f := by
  apply closure_minimal _ ((isClosed_tsupport V).union (isClosed_tsupport f))
  intro p hp
  by_contra hn
  let W := (tsupport V ∪ tsupport f)ᶜ
  have hW : IsOpen W := ((isClosed_tsupport V).union (isClosed_tsupport f)).isOpen_compl
  have hzV : ∀ x ∈ W, V x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hh => hx (Or.inl hh))
  have hzf : ∀ x ∈ W, f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hh => hx (Or.inr hh))
  exact hp (modeApprox_vanishes τ G V f hW hzV hzf q p hn)

lemma forcedMode_tsupport {n : ℕ} (τ : ℝ) (G : Field n) (f : Tensor) (q : ℕ) :
    tsupport (modeApprox τ G (fun _ => 0) f q) ⊆ tsupport f := by
  simpa only [← Pi.zero_def, tsupport_zero, empty_union] using modeApprox_tsupport τ G (fun _ => 0) f q

end ClosedSurfaceR4.SmallModes

namespace ClosedSurfaceR4.RealModes
open Set ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)

lemma realOsc_tsupport {n : ℕ} (τ : ℝ) (Z : Field n) :
    tsupport (realOsc τ Z) ⊆ tsupport Z := by
  apply closure_minimal _ (isClosed_tsupport Z)
  intro p hp
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  exact hp (by
    unfold realOsc
    simp only [oscillate, hz, smul_zero]
    ext i
    rfl)

lemma coordinateTarget_tsupport {e : Base → Base} (he : Continuous e)
    (A : Base → ComplexTensor) : tsupport (coordinateTarget e A) ⊆ e ⁻¹' tsupport A := by
  apply closure_minimal _ ((isClosed_tsupport A).preimage he)
  intro p hp
  by_contra hn
  have hz : A (e p) = 0 := image_eq_zero_of_notMem_tsupport hn
  exact hp (by simp only [coordinateTarget, hz, map_zero])

lemma phaseCanceller_tsupport {n : ℕ} {χ e : Base → Base} (hχ : Continuous χ) (he : Continuous e)
    (τ : ℝ) (F : RField n) (A : Base → ComplexTensor) (q : ℕ) :
    tsupport (phaseCanceller τ F χ e A q) ⊆ (e ∘ χ) ⁻¹' tsupport A := by
  apply closure_minimal _ ((isClosed_tsupport A).preimage (he.comp hχ))
  intro p hp
  by_contra hn
  have ht : χ p ∉ tsupport (coordinateTarget e A) :=
    fun hh => hn (coordinateTarget_tsupport he A hh)
  have htneg : χ p ∉ tsupport (fun p => -coordinateTarget e A p) := by simpa using ht
  have hm : χ p ∉ tsupport (phaseCancelAmplitude τ F e A q) :=
    fun hh => htneg (forcedMode_tsupport τ (fun p => complexify (F (e p)))
      (fun p => -coordinateTarget e A p) q hh)
  have hro : χ p ∉ tsupport (realOsc τ (phaseCancelAmplitude τ F e A q)) :=
    fun hh => hm (realOsc_tsupport τ _ hh)
  exact hp (show realOsc τ (phaseCancelAmplitude τ F e A q) (χ p) = 0 from
    image_eq_zero_of_notMem_tsupport hro)



lemma contDiff_extended_phaseCanceller {n : ℕ} {U S : Set Base} (hU : IsOpen U)
    (hS : IsClosed S) (hSU : S ⊆ U) {χ e : Base → Base}
    (hχ : Continuous χ) (he : Continuous e) (hinv : Set.EqOn (e ∘ χ) id U)
    {A : Base → ComplexTensor} (hAsp : tsupport A ⊆ S)
    (τ : ℝ) (F : RField n) (q : ℕ)
    (hsm : ContDiffOn ℝ ∞ (phaseCanceller τ F χ e A q) U) :
    ContDiff ℝ ∞ (U.indicator (phaseCanceller τ F χ e A q)) := by
  apply contDiff_indicator_of_support hU hS hSU hsm
  intro p hp hn
  apply image_eq_zero_of_notMem_tsupport
  intro hh
  have hmem := phaseCanceller_tsupport hχ he τ F A q hh
  change e (χ p) ∈ tsupport A at hmem
  have hi : e (χ p) = p := hinv hp
  rw [hi] at hmem
  exact hn (hAsp hmem)

lemma realLinearizedTensor_congr_right {n : ℕ} {F X Y : RField n} {p : Base}
    (h : X =ᶠ[nhds p] Y) : realLinearizedTensor F X p = realLinearizedTensor F Y p := by
  ext i
  simp only [realLinearizedTensor_apply, realLinearized, coordDeriv, h.fderiv_eq]

lemma realLinearizedTensor_zero_right {n : ℕ} (F : RField n) (p : Base) :
    realLinearizedTensor F (fun _ => 0) p = 0 := by
  ext i
  simp [realLinearizedTensor_apply, realLinearized, coordDeriv]



lemma indicator_linearized_error {n : ℕ} {U S : Set Base} (hU : IsOpen U)
    (hS : IsClosed S) (hSU : S ⊆ U) {X F : RField n} {A : Base → ComplexTensor}
    (hX : ∀ p ∈ U, p ∉ S → X p = 0) (hAsp : tsupport A ⊆ S)
    (τ : ℝ) (φ : Base → ℝ) :
    U.indicator (fun p => realLinearizedTensor F X p + displacement τ φ A p) =
      fun p => realLinearizedTensor F (U.indicator X) p + displacement τ φ A p := by
  classical
  funext p
  by_cases hp : p ∈ U
  · rw [indicator_of_mem hp]
    congr 1
    apply realLinearizedTensor_congr_right
    filter_upwards [hU.mem_nhds hp] with x hx
    exact (indicator_of_mem hx X).symm
  · have hsp := tsupport_indicator_subset hS hX
    have hzero : U.indicator X =ᶠ[nhds p] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hh => hp (hSU (hsp hh)))
    have hAz : A p = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hp (hSU (hAsp hh)))
    rw [indicator_of_notMem hp, realLinearizedTensor_congr_right hzero]
    change 0 = realLinearizedTensor F (fun _ => 0) p + _
    rw [realLinearizedTensor_zero_right]
    simp only [displacement, hAz, QuadraticMean.realMode, smul_zero, zero_add]
    ext i
    rfl

end ClosedSurfaceR4.RealModes

end

end OAI
