import OAI.NumberTheory.TotientAsymptotic.PerturbationRemoval
import OAI.NumberTheory.TotientAsymptotic.WitnessUnionLoss
import OAI.NumberTheory.TotientAsymptotic.BandGrid

namespace OAI

/-! Perturbation removal for the actual unions in the finite coefficient. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

lemma prefixBandRegion_volume_ne_top (x : ℝ) (H : ℕ) :
    volume (prefixBandRegion x H) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (measure_mono (prefixBandRegion_covered x H))
  rw [volume_gridRegion]
  exact ENNReal.natCast_ne_top _

lemma union_perturbation_loss_bound {H : ℕ} {x : ℝ} (d : ℕ) :
    volume.real ((⋃ η ∈ witnessFinset H (theta x) d,
      perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H) \
        (⋃ η ∈ witnessFinset H (theta x) d, tailPrefixRegion x H η)) ≤
    ∑ η ∈ witnessFinset H (theta x) d,
      volume.real ((perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H) \
        tailPrefixRegion x H η) := by
  let W := witnessFinset H (theta x) d
  let U := ⋃ η ∈ W, tailPrefixRegion x H η
  have he : ((⋃ η ∈ W, perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H) \ U) =
      ⋃ η ∈ W, ((perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H) \ U) := by
    ext u
    simp only [Set.mem_sdiff, Set.mem_iUnion]
    aesop
  change volume.real ((⋃ η ∈ W, perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H) \ U) ≤ _
  rw [he]
  apply (measureReal_biUnion_finset_le _ _).trans
  apply Finset.sum_le_sum
  intro η hη
  have hsub : ((perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H) \ U) ⊆
      ((perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H) \ tailPrefixRegion x H η) := by
    rintro u ⟨hu, hn⟩
    exact ⟨hu, fun ht => hn (Set.mem_iUnion.mpr ⟨η, Set.mem_iUnion.mpr ⟨hη, ht⟩⟩)⟩
  exact measureReal_mono hsub (ne_top_of_le_ne_top (prefixBandRegion_volume_ne_top x H)
    (measure_mono (fun _ hu => hu.1.2)))

/-- Removing all retained `xi` factors in the actual witness unions has a
vanishing normalized error for every weight between zero and one. -/
theorem weighted_union_perturbation_removal (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ f : ℝ → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      (∑ d ∈ Finset.Icc 1 (tailValueBound H), f ((ell d : ℝ)/d)/d *
        volume.real ((⋃ η ∈ witnessFinset H (theta x) d,
          perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H) \
            (⋃ η ∈ witnessFinset H (theta x) d, tailPrefixRegion x H η)))/G x (m x) ≤ ε H := by
  obtain ⟨ε, hε, hbound⟩ := witness_perturbation_removal hbox hmertens hren
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hbound] with H hH
  filter_upwards [hH, theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hs hB
  intro f hf
  apply le_trans _ (hx (activeWitnesses H (theta x))
    (fun η hη => (mem_activeWitnesses hs).mp hη))
  apply div_le_div_of_nonneg_right _ (G_pos hB _).le
  rw [← weighted_witness_fibers hs]
  apply Finset.sum_le_sum
  intro d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hw : 0 ≤ f ((ell d : ℝ)/d)/d := div_nonneg (hf _).1 hd0.le
  have hw' : f ((ell d : ℝ)/d)/d ≤ (d : ℝ)⁻¹ := by
    simpa only [one_div] using div_le_div_of_nonneg_right (hf _).2 hd0.le
  exact (mul_le_mul_of_nonneg_left (union_perturbation_loss_bound d) hw).trans
    (mul_le_mul_of_nonneg_right hw' (Finset.sum_nonneg (fun _ _ => measureReal_nonneg)))

end TotientAsymptotic

end

end OAI
