import OAI.Geometry.Immersion.ClosedSurface.PhaseMean

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.FiniteMean
open ClosedSurfaceR4.WeightedEstimates Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem MeanBounds.finset_sum {ι : Type*} {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} (hs : 0 ≤ s) {reference : E → F} {r : ℝ} {L : ℕ}
    (a : Finset ι) (T : ι → ℝ → (E → F) → E → F) (B K : ι → ℕ → ℝ → ℝ)
    (hT : ∀ i ∈ a, MeanBounds U s reference r L (T i) (B i) (K i)) :
    MeanBounds U s reference r L (fun η f x => ∑ i ∈ a, T i η f x)
      (fun m C => 1 + ∑ i ∈ a, B i m C) (fun m C => 1 + ∑ i ∈ a, K i m C) := by
  constructor
  · intro m C hC
    have hh : 0 ≤ ∑ i ∈ a, B i m C := Finset.sum_nonneg
      (fun i hi => le_trans zero_le_one ((hT i hi).B_pos m C hC))
    linarith
  · intro m C hC
    have hh : 0 ≤ ∑ i ∈ a, K i m C := Finset.sum_nonneg
      (fun i hi => le_trans zero_le_one ((hT i hi).K_pos m C hC))
    linarith
  · intro η hη hη1 f hf hball
    exact ContDiffOn.sum (fun i hi => (hT i hi).smooth η hη hη1 f hf hball)
  · intro η hη hη1 m C f hC hf hball hb
    have hh := WeightedBound.finset_sum hU hs a (fun i => η * B i m C)
      (fun i => T i η f) (fun i hi => (hT i hi).smooth η hη hη1 f hf hball)
      (fun i hi => (hT i hi).value η hη hη1 m C f hC hf hball hb)
    apply hh.mono_const
    rw [← Finset.mul_sum, mul_add, mul_one]
    linarith
  · intro η hη hη1 m C D f g hC hD hf hg hballf hballg hbf hbg hbd
    have hh := WeightedBound.finset_sum hU hs a (fun i => K i m C * η * D)
      (fun i => T i η f - T i η g)
      (fun i hi => ((hT i hi).smooth η hη hη1 f hf hballf).sub
        ((hT i hi).smooth η hη hη1 g hg hballg))
      (fun i hi => (hT i hi).difference η hη hη1 m C D f g hC hD hf hg hballf hballg hbf hbg hbd)
    have hbound : (∑ i ∈ a, K i m C * η * D) ≤ (1 + ∑ i ∈ a, K i m C) * η * D := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, add_mul, one_mul, add_mul]
      have hpos : 0 ≤ η * D := mul_nonneg hη.le hD
      linarith
    apply (hh.mono_const hbound).congr
    intro x hx
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]

end ClosedSurfaceR4.FiniteMean

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




lemma contDiff_of_tsupport_subset {U : Set E} (hU : IsOpen U) {f : E → F}
    (hfs : tsupport f ⊆ U) (hf : ContDiffOn ℝ ∞ f U) : ContDiff ℝ ∞ f := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hx)
  · have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hx (hfs hh))
    exact contDiffAt_const.congr_of_eventuallyEq hz



lemma WeightedBound.extend_support {U : Set E} (hU : IsOpen U) {f : E → F}
    (hfs : tsupport f ⊆ U) {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) : WeightedBound univ s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_univ]
  by_cases hxU : x ∈ U
  · rw [← iteratedFDerivWithin_of_isOpen j hU hxU]
    exact hb j hj x hxU
  · have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hxU (hfs hh))
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds]
    simpa using hC

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.SmallModes
open Set ClosedSurfaceR4.QuadraticMean

lemma gradientAmplitude_vanishes {n : ℕ} (τ : ℝ) {Z : Field n} {U : Set Base}
    (hU : IsOpen U) (hZ : ∀ p ∈ U, Z p = 0) (v : Base) :
    ∀ p ∈ U, gradientAmplitude τ Z v p = 0 := by
  intro p hp
  have he : Z =ᶠ[nhds p] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact hZ x hx
  unfold gradientAmplitude coordDeriv
  rw [he.fderiv_eq, he.self_of_nhds]
  simp


lemma modeMeanError_vanishes {n : ℕ} (τ : ℝ) (G : Field n) {V W : Field n}
    {U : Set Base} (hU : IsOpen U) (hV : ∀ p ∈ U, V p = 0) (hW : ∀ p ∈ U, W p = 0)
    (q : ℕ) (v w : Base) : ∀ p ∈ U, modeMeanError τ G V W q v w p = 0 := by
  have hMV := modeApprox_vanishes τ G V (fun _ => 0) hU hV (fun _ _ => rfl) q
  have hMW := modeApprox_vanishes τ G W (fun _ => 0) hU hW (fun _ _ => rfl) q
  have hDV := gradientAmplitude_vanishes τ hU hMV v
  have hDW := gradientAmplitude_vanishes τ hU hMW w
  intro p hp
  simp only [modeMeanError, hDV p hp, hDW p hp, leadingDerivative, hV p hp, hW p hp,
    smul_zero, zeroPair, sub_self]

end ClosedSurfaceR4.SmallModes

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates Set



lemma meanTensor_tsupport (δ τ : ℝ) (F : RField 4) (ψ u : Base → ℝ) (q : ℕ) :
    tsupport (meanTensor δ τ F (phaseAmplitude ψ u) q) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro p hp
  by_contra hn
  let U := (tsupport ψ)ᶜ
  have hU : IsOpen U := (isClosed_tsupport ψ).isOpen_compl
  have hz : ∀ x ∈ U, freeSeed δ τ (phaseAmplitude ψ u) F x = 0 := by
    intro x hx
    have hh : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [freeSeed, phaseAmplitude, hh]
  have hm := modeMeanError_vanishes τ (fun x => complexify (F x)) hU hz hz q
  have hvalue : meanTensor δ τ F (phaseAmplitude ψ u) q p = 0 := by
    ext i
    simp only [meanTensor, normalizedMeanError, hm (firstDirection i) (secondDirection i) p hn, mul_zero,
      Pi.zero_apply]
  exact hp hvalue

lemma contDiff_meanTensor_of_support {V : Set Base} {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F V) {ψ u : Base → ℝ} (hψ : ContDiffOn ℝ ∞ ψ V)
    (hu : ContDiffOn ℝ ∞ u V) (hpos : ∀ p ∈ V, 0 < u p) (hsp : tsupport ψ ⊆ V)
    (δ τ : ℝ) (q : ℕ) : ContDiff ℝ ∞ (meanTensor δ τ F (phaseAmplitude ψ u) q) := by
  exact contDiff_of_tsupport_subset h.isOpen ((meanTensor_tsupport δ τ F ψ u q).trans hsp)
    (contDiffOn_meanTensor hF h (contDiffOn_phaseAmplitude hψ hu hpos) δ τ q)

end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeightedBound.restrict_open {U : Set E} (hU : IsOpen U) {f : E → F}
    {s C : ℝ} {m : ℕ} (hb : WeightedBound univ s m C f) : WeightedBound U s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx]
  simpa only [iteratedFDerivWithin_univ] using hb j hj x (mem_univ x)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma tsupport_indicator_subset {U K : Set E} {f : E → F} (hK : IsClosed K)
    (hf : ∀ x ∈ U, x ∉ K → f x = 0) : tsupport (U.indicator f) ⊆ K := by
  classical
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  by_cases hxU : x ∈ U
  · exact hx (by rw [indicator_of_mem hxU, hf x hxU hn])
  · exact hx (indicator_of_notMem hxU _)

lemma contDiff_indicator_of_support {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    (hz : ∀ x ∈ U, x ∉ K → f x = 0) : ContDiff ℝ ∞ (U.indicator f) := by
  classical
  apply contDiff_of_tsupport_subset hU ((tsupport_indicator_subset hK hz).trans hKU)
  apply hf.congr
  intro x hx
  exact indicator_of_mem hx f

lemma WeightedBound.indicator_of_support {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) (hz : ∀ x ∈ U, x ∉ K → f x = 0) :
    WeightedBound univ s m C (U.indicator f) := by
  classical
  apply WeightedBound.extend_support hU ((tsupport_indicator_subset hK hz).trans hKU) hC
  apply hb.congr
  intro x hx
  exact indicator_of_mem hx f

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
