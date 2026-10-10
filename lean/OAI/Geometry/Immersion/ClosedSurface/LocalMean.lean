import OAI.Geometry.Immersion.ClosedSurface.PhaseMean

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set






structure LocalBounds (U V : Set Base) (s r ρ R : ℝ) (reference : Base → Tensor)
    (F : RField 4) (ψ : Base → ℝ) (Q : Base → Tensor →L[ℝ] ℝ) (χ e : Base → Base) : Prop where
  openU : IsOpen U
  smoothF : ContDiff ℝ ∞ F
  domain : RealModeDomain F V
  smoothPsi : ContDiffOn ℝ ∞ ψ V
  smoothQ : ContDiffOn ℝ ∞ Q V
  smoothChi : ContDiffOn ℝ ∞ χ U
  smoothInv : ContDiffOn ℝ ∞ e V
  chiInto : MapsTo χ U V
  invInto : MapsTo e V U
  smoothPullback : ContDiffOn ℝ ∞ (pullbackField χ) U
  margin : ∀ p ∈ V, ρ + ‖Q p‖ * r ≤ coefficient Q e reference p ∧
    coefficient Q e reference p ≤ R - ‖Q p‖ * r



structure Budgets (U V : Set Base) (s : ℝ) (F : RField 4) (ψ : Base → ℝ)
    (Q : Base → Tensor →L[ℝ] ℝ) (χ e : Base → Base) where
  inv : ℕ → ℝ
  chi : ℕ → ℝ
  psi : ℕ → ℝ
  forms : ℕ → ℝ
  pull : ℕ → ℝ
  normal : ℕ → ℝ
  mode : ℕ → ℝ
  inv_pos : ∀ m, 1 ≤ inv m
  chi_pos : ∀ m, 1 ≤ chi m
  psi_pos : ∀ m, 1 ≤ psi m
  forms_pos : ∀ m, 1 ≤ forms m
  pull_pos : ∀ m, 1 ≤ pull m
  normal_pos : ∀ m, 1 ≤ normal m
  mode_pos : ∀ m, 1 ≤ mode m
  inv_bound : ∀ m j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ inv m
  chi_bound : ∀ m j, 1 ≤ j → j ≤ m → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ j χ U p‖ ≤ chi m
  psi_bound : ∀ m, WeightedBound V s m (psi m) ψ
  forms_bound : ∀ m, WeightedBound V s m (forms m) Q
  pull_bound : ∀ m, WeightedBound U s m (pull m) (pullbackField χ)
  normal_bound : ∀ m, WeightedBound V s m (normal m) (freeNormal F)
  mode_bound : ∀ m, ReconstructionCoefficientBound (fun p => complexify (F p)) V s m (mode m)

variable {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
  {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}


def inputFactor (d : Budgets U V s F ψ Q χ e) (m : ℕ) : ℝ :=
  2 ^ m * d.forms m * (m.factorial : ℝ) * d.inv m ^ m

lemma inputFactor_nonneg (d : Budgets U V s F ψ Q χ e) (m : ℕ) : 0 ≤ inputFactor d m := by
  have hp := le_trans zero_le_one (d.forms_pos m)
  have hj := le_trans zero_le_one (d.inv_pos m)
  unfold inputFactor
  positivity

lemma LocalBounds.amplitude_smooth (h : LocalBounds U V s r ρ R reference F ψ Q χ e)
    (hρ : 0 < ρ) {A : Base → Tensor} (hA : ContDiffOn ℝ ∞ A U)
    (hball : InTrialBall U reference r A) :
    ContDiffOn ℝ ∞ (phaseAmplitude ψ (coefficient Q e A)) V := by
  have hR := coefficient_trial_range h.invInto h.margin hball
  exact contDiffOn_phaseAmplitude h.smoothPsi
    (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA)
    (fun p hp => hρ.trans_le (hR hp).1)



theorem LocalBounds.amplitude_bounds
    (h : LocalBounds U V s r ρ R reference F ψ Q χ e)
    (d : Budgets U V s F ψ Q χ e) (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ) (n : ℕ) (C : ℝ) :
    ∃ A0 : ℝ, 1 ≤ A0 ∧ ∀ (A B : Base → Tensor) (D : ℝ), 0 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      InTrialBall U reference r A → InTrialBall U reference r B →
      WeightedBound U s n C A → WeightedBound U s n C B →
      WeightedBound U s n D (A - B) →
      WeightedBound V s n A0 (phaseAmplitude ψ (coefficient Q e A)) ∧
      WeightedBound V s n A0 (phaseAmplitude ψ (coefficient Q e B)) ∧
      WeightedBound V s n (A0 * inputFactor d n * D)
        (fun p => phaseAmplitude ψ (coefficient Q e A) p - phaseAmplitude ψ (coefficient Q e B) p) := by
  let C' := max 1 (inputFactor d n * C)
  obtain ⟨A0, hA0, hb⟩ := compact_amplitude_bounds (R := R) h.domain.isOpen.uniqueDiffOn hρ
    (show 1 ≤ C' from le_max_left _ _) (le_trans zero_le_one (d.psi_pos n)) n
  refine ⟨A0, hA0, ?_⟩
  intro A B D hC hD hA hB hballA hballB hbA hbB hbD
  have hcoeff (X : Base → Tensor) (hX : ContDiffOn ℝ ∞ X U)
      (hbX : WeightedBound U s n C X) : WeightedBound V s n C' (coefficient Q e X) :=
    (weighted_coefficient h.openU.uniqueDiffOn h.domain.isOpen.uniqueDiffOn hs hs1
      (d.inv_pos n) (le_trans zero_le_one (d.forms_pos n)) hC h.smoothQ h.smoothInv
      h.invInto hX (d.inv_bound n) (d.forms_bound n) hbX).mono_const (le_max_right _ _)
  have hdiff := weighted_coefficient_difference h.openU.uniqueDiffOn h.domain.isOpen.uniqueDiffOn
    hs hs1 (d.inv_pos n) (le_trans zero_le_one (d.forms_pos n)) hD h.smoothQ h.smoothInv
    h.invInto hA hB (d.inv_bound n) (d.forms_bound n) hbD
  have hu := contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA
  have hv := contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hB
  have hh := hb s (inputFactor d n * D) ψ (coefficient Q e A) (coefficient Q e B) hs
    (mul_nonneg (inputFactor_nonneg d n) hD) h.smoothPsi hu hv
    (coefficient_trial_range h.invInto h.margin hballA)
    (coefficient_trial_range h.invInto h.margin hballB) (d.psi_bound n) (hcoeff A hA hbA)
    (hcoeff B hB hbB) hdiff
  refine ⟨hh.1, hh.2.1, ?_⟩
  simpa only [mul_assoc] using hh.2.2

end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set
variable {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
  {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

def outputFactor (d : Budgets U V s F ψ Q χ e) (m : ℕ) : ℝ :=
  2 ^ m * d.pull m * (m.factorial : ℝ) * d.chi m ^ m

lemma outputFactor_nonneg (d : Budgets U V s F ψ Q χ e) (m : ℕ) : 0 ≤ outputFactor d m := by
  have hp := le_trans zero_le_one (d.pull_pos m)
  have hj := le_trans zero_le_one (d.chi_pos m)
  unfold outputFactor
  positivity

lemma LocalBounds.transport_bound (h : LocalBounds U V s r ρ R reference F ψ Q χ e)
    (d : Budgets U V s F ψ Q χ e) (hs : 0 < s) (hs1 : s ≤ 1)
    {m : ℕ} {D : ℝ} {g : Base → Tensor} (hD : 0 ≤ D) (hg : ContDiffOn ℝ ∞ g V)
    (hb : WeightedBound V s m D g) : WeightedBound U s m (outputFactor d m * D)
      (fun p => pullbackField χ p (g (χ p))) := by
  have hc := hb.comp_coordinates h.openU.uniqueDiffOn h.domain.isOpen.uniqueDiffOn hs hs1
    (d.chi_pos m) hD h.smoothChi hg h.chiInto (d.chi_bound m)
  have hchi := le_trans zero_le_one (d.chi_pos m)
  have hh := (d.pull_bound m).clm_apply h.openU.uniqueDiffOn hs.le
    (le_trans zero_le_one (d.pull_pos m)) (by positivity) h.smoothPullback
    (hg.comp h.smoothChi h.chiInto) hc
  convert hh using 1 <;> try rfl
  dsimp [outputFactor]
  ring

lemma LocalBounds.mean_smooth (h : LocalBounds U V s r ρ R reference F ψ Q χ e)
    (hρ : 0 < ρ) {A : Base → Tensor} (hA : ContDiffOn ℝ ∞ A U)
    (hball : InTrialBall U reference r A) (δ : ℝ) (q : ℕ) (η : ℝ) :
    ContDiffOn ℝ ∞ (meanTerm δ s F ψ Q χ e q η A) U := by
  exact h.smoothPullback.clm_apply
    ((contDiffOn_meanTensor h.smoothF h.domain (h.amplitude_smooth hρ hA hball) δ (η * s) q).comp
      h.smoothChi h.chiInto)




theorem LocalBounds.mean_estimates (h : LocalBounds U V s r ρ R reference F ψ Q χ e)
    (d : Budgets U V s F ψ Q χ e) (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ)
    {δ : ℝ} (hδ : 0 < δ) (q m : ℕ) (C : ℝ) :
    ∃ β κ : ℝ, 1 ≤ β ∧ 1 ≤ κ ∧ ∀ (η : ℝ), 0 < η → η ≤ 1 →
      ∀ (A B : Base → Tensor) (D : ℝ), 0 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      InTrialBall U reference r A → InTrialBall U reference r B →
      WeightedBound U s (m + (q + 2)) C A → WeightedBound U s (m + (q + 2)) C B →
      WeightedBound U s (m + (q + 2)) D (A - B) →
      WeightedBound U s m (η * β) (meanTerm δ s F ψ Q χ e q η A) ∧
      WeightedBound U s m (κ * η * D)
        (meanTerm δ s F ψ Q χ e q η A - meanTerm δ s F ψ Q χ e q η B) := by
  let n := m + q + 2
  obtain ⟨a, ha, hb⟩ := h.amplitude_bounds d hs hs1 hρ n C
  let Z := meanErrorConstant 4 m (d.mode n) q * (Real.sqrt 2 * 2 ^ n * d.normal n) ^ 2 * a ^ 2
  have hz : 0 ≤ Z := mul_nonneg (mul_nonneg
    (meanErrorConstant_nonneg 4 m q (le_trans zero_le_one (d.mode_pos n))) (sq_nonneg _)) (sq_nonneg _)
  refine ⟨max 1 (outputFactor d m * Z), max 1 (outputFactor d m * (2 * Z * inputFactor d n)),
    le_max_left _ _, le_max_left _ _, ?_⟩
  intro η hη hη1 A B D hC hD hA hB hballA hballB hbA hbB hbD
  have hn : m + (q + 2) = n := by dsimp [n]; omega
  rw [hn] at hbA hbB hbD
  obtain ⟨haA, haB, haD⟩ := hb A B D hC hD hA hB hballA hballB hbA hbB hbD
  have hsa := h.amplitude_smooth hρ hA hballA
  have hsb := h.amplitude_smooth hρ hB hballB
  have hτs : η * s ≤ s := by nlinarith
  have hcancel : η * s / s = η := mul_div_cancel_right₀ _ hs.ne'
  have hval := weighted_meanTensor h.smoothF h.domain hsa hδ (mul_pos hη hs) hs hτs hs1
    (le_trans zero_le_one (d.mode_pos n)) (le_trans zero_le_one ha)
    (le_trans zero_le_one (d.normal_pos n)) q m (d.mode_bound n) haA (d.normal_bound n)
  have hval' : WeightedBound V s m (Z * η)
      (meanTensor δ (η * s) F (phaseAmplitude ψ (coefficient Q e A)) q) := by
    convert hval using 1
    rw [hcancel]
    dsimp [Z, n]
    ring
  have hv := h.transport_bound d hs hs1 (mul_nonneg hz hη.le)
    (contDiffOn_meanTensor h.smoothF h.domain hsa δ (η * s) q) hval'
  have hdiff := weighted_meanTensor_difference h.smoothF h.domain hsa hsb hδ
    (mul_pos hη hs) hs hτs hs1 (le_trans zero_le_one (d.mode_pos n))
    (le_trans zero_le_one ha) (mul_nonneg (mul_nonneg (le_trans zero_le_one ha)
      (inputFactor_nonneg d n)) hD) (le_trans zero_le_one (d.normal_pos n)) q m
    (d.mode_bound n) haA haB haD (d.normal_bound n)
  have hdiff' : WeightedBound V s m (2 * Z * inputFactor d n * D * η)
      (fun p => meanTensor δ (η * s) F (phaseAmplitude ψ (coefficient Q e A)) q p -
        meanTensor δ (η * s) F (phaseAmplitude ψ (coefficient Q e B)) q p) := by
    convert hdiff using 1
    rw [hcancel]
    dsimp [Z, n]
    ring
  have hi := inputFactor_nonneg d n
  have hd := h.transport_bound d hs hs1 (by positivity)
    ((contDiffOn_meanTensor h.smoothF h.domain hsa δ (η * s) q).sub
      (contDiffOn_meanTensor h.smoothF h.domain hsb δ (η * s) q)) hdiff'
  constructor
  · apply hv.mono_const
    calc
      _ = η * (outputFactor d m * Z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hη.le
  · have hbound : outputFactor d m * (2 * Z * inputFactor d n * D * η) ≤
        max 1 (outputFactor d m * (2 * Z * inputFactor d n)) * η * D := by
      calc
        _ = (outputFactor d m * (2 * Z * inputFactor d n)) * (η * D) := by ring
        _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (le_max_right 1
          (outputFactor d m * (2 * Z * inputFactor d n))) (mul_nonneg hη.le hD)
    apply (hd.mono_const hbound).congr
    intro p hp
    exact (map_sub (pullbackField χ p) _ _).symm

end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set




theorem actual_local_mean_bounds {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
    {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}
    (h : LocalBounds U V s r ρ R reference F ψ Q χ e)
    (d : Budgets U V s F ψ Q χ e) (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ)
    {δ : ℝ} (hδ : 0 < δ) (q : ℕ) :
    ∃ B K : ℕ → ℝ → ℝ, MeanBounds U s reference r (q + 2)
      (meanTerm δ s F ψ Q χ e q) B K := by
  choose β κ hβ hκ hb using fun m C => h.mean_estimates d hs hs1 hρ hδ q m C
  refine ⟨β, κ, ?_⟩
  constructor
  · intro m C hC
    exact hβ m C
  · intro m C hC
    exact hκ m C
  · intro η hη hη1 A hA hball
    exact h.mean_smooth hρ hA hball δ q η
  · intro η hη hη1 m C A hC hA hball hAB
    have hzero : WeightedBound U s (m + (q + 2)) 0 (A - A) := by
      apply (weightedBound_zero U s (m + (q + 2)) (F := Tensor)).congr
      intro p hp
      simp
    exact (hb m C η hη hη1 A A 0 (le_trans zero_le_one hC) le_rfl hA hA hball hball
      hAB hAB hzero).1
  · intro η hη hη1 m C D A B hC hD hA hB hballA hballB hbA hbB hbD
    exact (hb m C η hη hη1 A B D (le_trans zero_le_one hC) hD hA hB hballA hballB
      hbA hbB hbD).2

end ClosedSurfaceR4.PhaseMean

end

end OAI
