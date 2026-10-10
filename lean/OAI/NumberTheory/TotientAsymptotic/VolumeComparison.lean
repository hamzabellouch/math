import OAI.NumberTheory.TotientAsymptotic.UnionPerturbation
import OAI.NumberTheory.TotientAsymptotic.GridApproximation

namespace OAI

/-! The banded perturbed volume and the exact finite coefficient differ by
a vanishing normalized error. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def exactWitnessUnion (x : ℝ) (H d : ℕ) : Set (Fin (R x H) → ℝ) :=
  ⋃ η ∈ witnessFinset H (theta x) d, tailPrefixRegion x H η

def perturbedWitnessUnion (x : ℝ) (H d : ℕ) : Set (Fin (R x H) → ℝ) :=
  ⋃ η ∈ witnessFinset H (theta x) d,
    perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H

lemma bandedWitnessRegion_eq {x : ℝ} {H : ℕ}
    (hs : theta x ∈ Set.Ico (0 : ℝ) 1) (d : ℕ) :
    bandedWitnessRegion x H d = perturbedWitnessUnion x H d := by
  ext u
  simp only [bandedWitnessRegion, perturbedWitnessUnion, Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hb, η, hη, hu⟩
    exact ⟨η, (mem_witnessFinset hs).mpr hη, hu, hb⟩
  · rintro ⟨η, hη, hu, hb⟩
    exact ⟨hb, η, (mem_witnessFinset hs).mp hη, hu⟩

lemma exactWitnessUnion_volume_ne_top {x : ℝ} {H : ℕ} (hR : 0 < R x H) (d : ℕ) :
    volume (exactWitnessUnion x H d) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (measure_biUnion_finset_le _ _)
  exact ENNReal.sum_ne_top.mpr (fun η _ => volume_tailPrefixRegion_ne_top hR η)

lemma perturbedWitnessUnion_volume_ne_top (x : ℝ) (H d : ℕ) :
    volume (perturbedWitnessUnion x H d) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (prefixBandRegion_volume_ne_top x H)
  apply measure_mono
  intro u hu
  obtain ⟨η, hη⟩ := Set.mem_iUnion.mp hu
  obtain ⟨_, hu⟩ := Set.mem_iUnion.mp hη
  exact hu.2

lemma exactWitnessUnion_empty_of_not_totient {x : ℝ} {H d : ℕ}
    (hs : theta x ∈ Set.Ico (0 : ℝ) 1) (hd : ¬ IsTotient d) :
    exactWitnessUnion x H d = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨η, hη⟩ := Set.mem_iUnion.mp hu
  obtain ⟨hη, _⟩ := Set.mem_iUnion.mp hη
  have hw := (mem_witnessFinset hs).mp hη
  exact hd ⟨w η, witness_w_pos hw.1, hw.2⟩

lemma unionVolumeCoefficient_mul_G {x : ℝ} {H : ℕ}
    (hB : 0 < B x) (hs : theta x ∈ Set.Ico (0 : ℝ) 1) (f : ℝ → ℝ) :
    unionVolumeCoefficient H f x*G x (m x) =
      ∑ d ∈ Finset.Icc 1 (tailValueBound H),
        f ((ell d : ℝ)/d)/d*volume.real (exactWitnessUnion x H d) := by
  unfold unionVolumeCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : IsTotient d
  · rw [ite_eq_left hd, div_mul_cancel₀ _ (G_pos hB _).ne']
    rfl
  · rw [ite_eq_right hd, zero_mul, exactWitnessUnion_empty_of_not_totient hs hd]
    simp

lemma perturbed_exact_volume_difference {x : ℝ} {H : ℕ} (hB : 0 ≤ B x)
    (hR : 0 < R x H) (d : ℕ) :
    |volume.real (perturbedWitnessUnion x H d)-volume.real (exactWitnessUnion x H d)| ≤
      volume.real (perturbedWitnessUnion x H d \ exactWitnessUnion x H d)+
        volume.real (exactWitnessUnion x H d \ prefixBandRegion x H) := by
  have hfinite := exactWitnessUnion_volume_ne_top hR d
  have hsub : exactWitnessUnion x H d \ perturbedWitnessUnion x H d ⊆
      exactWitnessUnion x H d \ prefixBandRegion x H := by
    rintro u ⟨hu, hn⟩
    refine ⟨hu, ?_⟩
    intro hb
    obtain ⟨η, hη⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hη, hu⟩ := Set.mem_iUnion.mp hη
    exact hn (Set.mem_iUnion.mpr ⟨η, Set.mem_iUnion.mpr
      ⟨hη, banded_tailRegion_subset_perturbed η hB ⟨hu, hb⟩, hb⟩⟩)
  have hfinDiff : volume (exactWitnessUnion x H d \ prefixBandRegion x H) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (measure_mono Set.sdiff_subset)
  have hh := (le_measureReal_sdiff (μ := volume) (s₁ := exactWitnessUnion x H d)
    (perturbedWitnessUnion_volume_ne_top x H d)).trans (measureReal_mono hsub hfinDiff)
  have ha := le_measureReal_sdiff (μ := volume) (s₁ := perturbedWitnessUnion x H d) hfinite
  rw [abs_le]
  constructor <;> linarith [show 0 ≤ volume.real
    (perturbedWitnessUnion x H d \ exactWitnessUnion x H d) from measureReal_nonneg,
      show 0 ≤ volume.real (exactWitnessUnion x H d \ prefixBandRegion x H) from measureReal_nonneg]

/-- The geometric approximation to the exact coefficient. Only the
prime-grid-to-volume step remains in the mass approximation after this. -/
theorem banded_volume_coefficient_approximation (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput)
    (hford : FordCoordinateConcentrationInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ f : ℝ → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      |bandedVolumeMass x H f/G x (m x)-unionVolumeCoefficient H f x| ≤ ε H := by
  obtain ⟨ε, hε, hp⟩ := weighted_union_perturbation_removal hbox hmertens hren
  obtain ⟨δ, hδ, hb⟩ := weighted_union_band_removal hbox hmertens hren hford
  refine ⟨fun H => ε H+δ H, by simpa using hε.add hδ, ?_⟩
  filter_upwards [hp, hb] with H hHp hHb
  filter_upwards [hHp, hHb, theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    m_tendsto.eventually (eventually_gt_atTop H)] with x hxp hxb hs hB hm
  intro f hf
  have hR : 0 < R x H := by unfold R; omega
  have heq : bandedVolumeMass x H f-unionVolumeCoefficient H f x*G x (m x) =
      ∑ d ∈ Finset.Icc 1 (tailValueBound H), f ((ell d : ℝ)/d)/d*
        (volume.real (perturbedWitnessUnion x H d)-volume.real (exactWitnessUnion x H d)) := by
    rw [unionVolumeCoefficient_mul_G hB hs, bandedVolumeMass, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [bandedWitnessRegion_eq hs]
    change _*volume.real _-_*volume.real _ = _
    ring
  have habs : |bandedVolumeMass x H f-unionVolumeCoefficient H f x*G x (m x)| ≤
      (∑ d ∈ Finset.Icc 1 (tailValueBound H), f ((ell d : ℝ)/d)/d*
        volume.real (perturbedWitnessUnion x H d \ exactWitnessUnion x H d))+
      (∑ d ∈ Finset.Icc 1 (tailValueBound H), f ((ell d : ℝ)/d)/d*
        volume.real (exactWitnessUnion x H d \ prefixBandRegion x H)) := by
    rw [heq, ← Finset.sum_add_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro d hd
    have hw : 0 ≤ f ((ell d : ℝ)/d)/d := div_nonneg (hf _).1 (Nat.cast_nonneg _)
    rw [abs_mul, abs_of_nonneg hw, ← mul_add]
    exact mul_le_mul_of_nonneg_left (perturbed_exact_volume_difference hB.le hR d) hw
  have htotal := add_le_add (hxp f hf) (hxb f hf)
  rw [← add_div] at htotal
  calc
    _ = |bandedVolumeMass x H f-unionVolumeCoefficient H f x*G x (m x)|/G x (m x) := by
      have hq : bandedVolumeMass x H f/G x (m x)-unionVolumeCoefficient H f x =
          (bandedVolumeMass x H f-unionVolumeCoefficient H f x*G x (m x))/G x (m x) := by
        rw [sub_div, mul_div_cancel_right₀ _ (G_pos hB _).ne']
      rw [hq, abs_div, abs_of_pos (G_pos hB _)]
    _ ≤ _ := div_le_div_of_nonneg_right habs (G_pos hB _).le
    _ ≤ ε H+δ H := htotal

end TotientAsymptotic

end

end OAI
