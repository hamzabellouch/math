import OAI.Geometry.Immersion.ClosedSurface.SupportedCancellation
import OAI.Geometry.Immersion.ClosedSurface.MeanBilinearity

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates Set
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude zeroPair)


def chartFreeAmplitude (δ τ : ℝ) (F : RField 4) (b : Base → ℝ) (q : ℕ)
    (χ : Base → Base) : Field 4 :=
  modeApprox τ (fun p => complexify (F p)) (freeSeed δ τ b F) (fun _ => 0) q ∘ χ


def chartLeadingTensor (b : Base → ℝ) (χ : Base → Base) : Base → PhaseMean.Tensor :=
  fun p => pullbackField χ p
    (fun i => b (χ p) ^ 2 * (firstDirection i).1 * (secondDirection i).1)

lemma contDiffOn_chartFreeAmplitude {F : RField 4} {U V : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V) {b : Base → ℝ}
    (hb : ContDiffOn ℝ ∞ b V) {χ : Base → Base} (hχ : ContDiffOn ℝ ∞ χ U)
    (hχV : MapsTo χ U V) (δ τ : ℝ) (q : ℕ) :
    ContDiffOn ℝ ∞ (chartFreeAmplitude δ τ F b q χ) U := by
  have hv := freeSeed_isFree hF h δ τ hb
  exact (contDiffOn_modeApprox τ (h.complexDomain hF) hv.smooth (f := fun _ => 0) contDiffOn_const q).comp hχ hχV

lemma chartFree_zeroTensor {F : RField 4} {U V : Set Base} (hU : IsOpen U)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V) {b : Base → ℝ}
    (hb : ContDiffOn ℝ ∞ b V) {χ : Base → Base} (hχ : ContDiffOn ℝ ∞ χ U)
    (hχV : MapsTo χ U V) {δ τ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    {p : Base} (hp : p ∈ U) :
    phaseZeroTensor τ (fun p => (χ p).1) (chartFreeAmplitude δ τ F b q χ) p =
      δ ^ 2 • chartLeadingTensor b χ p +
      δ ^ 2 • pullbackField χ p (meanTensor δ τ F b q (χ p)) := by
  have hv := freeSeed_isFree hF h δ τ hb
  have hz := (contDiffOn_modeApprox τ (h.complexDomain hF) hv.smooth (f := fun _ => 0) contDiffOn_const q).contDiffAt
    (h.isOpen.mem_nhds (hχV hp))
  change phaseZeroTensor τ (fun p => (χ p).1)
    (modeApprox τ (fun p => complexify (F p)) (freeSeed δ τ b F) (fun _ => 0) q ∘ χ) p = _
  rw [phaseZeroTensor_coordinate (hz.differentiableAt (by simp))
    ((hχ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)),
    freePhase_zeroTensor h hδ hτ b q (hχV hp), map_add, map_smul, map_smul]
  rfl

lemma chartFree_vanishes {U S : Set Base} {χ : Base → Base} {ψ : Base → ℝ}
    (hsp : ∀ p ∈ U, χ p ∈ tsupport ψ → p ∈ S)
    (δ τ : ℝ) (F : RField 4) (u : Base → ℝ) (q : ℕ) :
    ∀ p ∈ U, p ∉ S → chartFreeAmplitude δ τ F (phaseAmplitude ψ u) q χ p = 0 := by
  intro p hp hn
  have hψ : χ p ∉ tsupport ψ := fun hh => hn (hsp p hp hh)
  change modeApprox τ (fun p => complexify (F p)) (freeSeed δ τ (phaseAmplitude ψ u) F)
    (fun _ => 0) q (χ p) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hh
  have hm := modeApprox_tsupport τ (fun p => complexify (F p))
    (freeSeed δ τ (phaseAmplitude ψ u) F) (fun _ => 0) q hh
  have hzero : tsupport (fun _ : Base => (0 : Fin 3 → ℂ)) = ∅ := by
    simpa only [← Pi.zero_def] using (tsupport_zero : tsupport (0 : Base → Fin 3 → ℂ) = ∅)
  rw [hzero, union_empty] at hm
  have hs : tsupport (freeSeed δ τ (phaseAmplitude ψ u) F) ⊆ tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro x hx
    by_contra hxψ
    have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxψ
    exact hx (by simp [freeSeed, phaseAmplitude, hz])
  exact hψ (hs hm)

lemma phaseZeroTensor_congr_right {n : ℕ} (τ : ℝ) (φ : Base → ℝ)
    {Z W : Field n} {p : Base} (h : Z =ᶠ[nhds p] W) :
    phaseZeroTensor τ φ Z p = phaseZeroTensor τ φ W p := by
  ext i
  simp only [phaseZeroTensor, derivativeAmplitude, h.fderiv_eq, h.self_of_nhds]

lemma phaseZeroTensor_zero {n : ℕ} (τ : ℝ) (φ : Base → ℝ) (p : Base) :
    phaseZeroTensor τ φ (fun _ => (0 : Ambient n)) p = 0 := by
  ext i
  simp [phaseZeroTensor, derivativeAmplitude, zeroPair]

lemma phaseZeroTensor_indicator {n : ℕ} {U S : Set Base} (hU : IsOpen U)
    (hS : IsClosed S) (hSU : S ⊆ U) {Z : Field n}
    (hz : ∀ p ∈ U, p ∉ S → Z p = 0) (τ : ℝ) (φ : Base → ℝ) :
    phaseZeroTensor τ φ (U.indicator Z) = U.indicator (phaseZeroTensor τ φ Z) := by
  classical
  funext p
  by_cases hp : p ∈ U
  · rw [indicator_of_mem hp]
    apply phaseZeroTensor_congr_right
    filter_upwards [hU.mem_nhds hp] with x hx
    exact indicator_of_mem hx Z
  · rw [indicator_of_notMem hp]
    have hzero : U.indicator Z =ᶠ[nhds p] fun _ => 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hh => hp (hSU ((tsupport_indicator_subset hS hz) hh)))
    rw [phaseZeroTensor_congr_right τ φ hzero, phaseZeroTensor_zero]



lemma extended_free_mean {F : RField 4} {U V S : Set Base} (hU : IsOpen U)
    (hS : IsClosed S) (hSU : S ⊆ U) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    {ψ u : Base → ℝ} (hb : ContDiffOn ℝ ∞ (phaseAmplitude ψ u) V)
    {χ : Base → Base} (hχ : ContDiffOn ℝ ∞ χ U) (hχV : MapsTo χ U V)
    (hsp : ∀ p ∈ U, χ p ∈ tsupport ψ → p ∈ S)
    {δ τ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ) :
    phaseZeroTensor τ (fun p => (χ p).1)
      (U.indicator (chartFreeAmplitude δ τ F (phaseAmplitude ψ u) q χ)) =
      fun p => δ ^ 2 • U.indicator (chartLeadingTensor (phaseAmplitude ψ u) χ) p +
        δ ^ 2 • U.indicator
          (fun p => pullbackField χ p (meanTensor δ τ F (phaseAmplitude ψ u) q (χ p))) p := by
  classical
  rw [phaseZeroTensor_indicator hU hS hSU (chartFree_vanishes hsp δ τ F u q)]
  funext p
  by_cases hp : p ∈ U
  · simp only [indicator_of_mem hp]
    exact chartFree_zeroTensor hU hF h hb hχ hχV hδ hτ q hp
  · simp only [indicator_of_notMem hp, smul_zero, add_zero]

end ClosedSurfaceR4.RealModes

end

end OAI
