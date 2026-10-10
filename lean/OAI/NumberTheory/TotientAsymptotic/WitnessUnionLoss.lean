import OAI.NumberTheory.TotientAsymptotic.BandRemoval

namespace OAI

/-! Transfer of the band-removal estimate to the actual unions at each tail value. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def activeWitnesses (H : ℕ) (s : ℝ) : Finset (TailDatum H) :=
  (allTailData H).filter (IsWitness H s)

lemma mem_activeWitnesses {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) : η ∈ activeWitnesses H s ↔ IsWitness H s η := by
  simp only [activeWitnesses, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨witness_mem_allTailData hs h, h⟩⟩

lemma sum_witness_fibers {H : ℕ} {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (F : TailDatum H → ℝ) :
    (∑ d ∈ Finset.Icc 1 (tailValueBound H), ∑ η ∈ witnessFinset H s d, F η) =
      ∑ η ∈ activeWitnesses H s, F η := by
  have hmaps : ∀ η ∈ activeWitnesses H s,
      (w η).totient ∈ Finset.Icc 1 (tailValueBound H) := by
    intro η hη
    have hw := (mem_activeWitnesses hs).mp hη
    exact Finset.mem_Icc.mpr ⟨Nat.totient_pos.mpr (witness_w_pos hw),
      witness_totient_bound hs η ⟨hw, rfl⟩⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  ext η
  rw [mem_witnessFinset hs, Finset.mem_filter, mem_activeWitnesses hs]
  rfl

lemma weighted_witness_fibers {H : ℕ} {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (F : TailDatum H → ℝ) :
    (∑ d ∈ Finset.Icc 1 (tailValueBound H),
      (d : ℝ)⁻¹*∑ η ∈ witnessFinset H s d, F η) =
      ∑ η ∈ activeWitnesses H s, ((w η).totient : ℝ)⁻¹*F η := by
  rw [← sum_witness_fibers hs]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η hη
  rw [((mem_witnessFinset hs).mp hη).2]

lemma union_band_loss_bound {H : ℕ} {x : ℝ} (d : ℕ) :
    volume.real ((⋃ η ∈ witnessFinset H (theta x) d, tailPrefixRegion x H η) \
      prefixBandRegion x H) ≤
      ∑ η ∈ witnessFinset H (theta x) d,
        volume.real (tailPrefixRegion x H η \ prefixBandRegion x H) := by
  have he : ((⋃ η ∈ witnessFinset H (theta x) d, tailPrefixRegion x H η) \
      prefixBandRegion x H) =
      ⋃ η ∈ witnessFinset H (theta x) d,
        (tailPrefixRegion x H η \ prefixBandRegion x H) := by
    ext u
    simp only [Set.mem_sdiff, Set.mem_iUnion]
    aesop
  rw [he]
  exact measureReal_biUnion_finset_le _ _

/-- The discarded volume in the coefficient's actual witness unions is
uniformly negligible for every weight between zero and one. -/
theorem weighted_union_band_removal (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput)
    (hford : FordCoordinateConcentrationInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ f : ℝ → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      (∑ d ∈ Finset.Icc 1 (tailValueBound H), f ((ell d : ℝ)/d)/d *
        volume.real ((⋃ η ∈ witnessFinset H (theta x) d, tailPrefixRegion x H η) \
          prefixBandRegion x H))/G x (m x) ≤ ε H := by
  obtain ⟨ε, hε, hbound⟩ := witness_band_removal hbox hmertens hren hford
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
  exact (mul_le_mul_of_nonneg_left (union_band_loss_bound d) hw).trans
    (mul_le_mul_of_nonneg_right hw' (Finset.sum_nonneg (fun _ _ => measureReal_nonneg)))

end TotientAsymptotic

end

end OAI
