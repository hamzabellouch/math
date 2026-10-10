import OAI.NumberTheory.TotientAsymptotic.SimplexScaling
import OAI.NumberTheory.TotientAsymptotic.TruncatedConcentration

namespace OAI

/-! Coarse-band violations survive the small diagonal enlargement and are
therefore bounded by Ford's published coordinate concentration. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma rescaled_band_violation {b t u κ : ℝ} (hb : 0 < b)
    (ht : (99/100 : ℝ)*b ≤ t ∧ t ≤ (101/100 : ℝ)*b)
    (hκ : 1 ≤ κ ∧ κ ≤ (102/100 : ℝ))
    (hu : u < (91/100 : ℝ)*t ∨ (109/100 : ℝ)*t < u) :
    u/κ < (95/100 : ℝ)*b ∨ (105/100 : ℝ)*b < u/κ := by
  have hp : 0 < κ := lt_of_lt_of_le zero_lt_one hκ.1
  rcases hu with hu | hu
  · left
    apply (div_lt_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hκ.1 hb.le]
  · right
    apply (lt_div_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hκ.2 hb.le]

lemma volume_scaled_set_le {N : ℕ} (κ : Fin N → ℝ) (hκ : ∀ i, 0 < κ i)
    (S T : Set (Fin N → ℝ)) (hT : MeasurableSet T) (hfin : volume T ≠ ⊤)
    (hmap : Set.MapsTo (simplexScale κ) S T) :
    volume.real S ≤ (∏ i, κ i)*volume.real T := by
  have hp : 0 < ∏ i, κ i := Finset.prod_pos (fun i _ => hκ i)
  have hd : LinearMap.det (simplexScale κ) ≠ 0 := by
    rw [simplexScale_det]
    exact inv_ne_zero hp.ne'
  have hh : volume S ≤ ENNReal.ofReal (∏ i, κ i)*volume T := by
    have hsub : S ⊆ (simplexScale κ) ⁻¹' T := hmap
    apply (measure_mono hsub).trans_eq
    rw [← Measure.map_apply (simplexScale κ).continuous_of_finiteDimensional.measurable hT,
      Real.map_linearMap_volume_pi_eq_smul_volume_pi hd, simplexScale_det, inv_inv,
      abs_of_pos hp, Measure.smul_apply, smul_eq_mul]
  have hf : ENNReal.ofReal (∏ i, κ i)*volume T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.le] using
    ENNReal.toReal_mono hf hh

lemma measurableSet_coarseCoordinateBad (m : ℕ) (B : ℝ) {N : ℕ} (i : Fin N) :
    MeasurableSet (coarseCoordinateBad m B i) := by
  exact ((isOpen_lt (continuous_apply i) continuous_const).union
    (isOpen_lt continuous_const (continuous_apply i))).measurableSet

/-- The concentration bound after diagonal normalization, before summing
retained coordinates. All scale and center comparisons are explicit. -/
theorem scaled_coarse_concentration (hford : FordCoordinateConcentrationInput) :
    ∃ C c : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 < c ∧
    ∀ N ≥ N₀, ∀ (m q : ℕ) (B : ℝ), 0 < B → m-q=N+2 →
    ∀ (β₀ : ℝ) (β κ : Fin (N+2) → ℝ), 0 < β₀ →
      (∀ j, 0 < β j) → (∀ j, 0 < κ j) → (∀ j, β₀ ≤ κ j) →
      (∀ i j, i < j → β i*κ i ≤ κ j) →
    ∀ (i : Fin (N+2)) (t : ℝ), i.val < N → 100*q ≤ m-(i.val+1) →
      (99/100 : ℝ)*fullSimplexCenter m B (i.val+1) ≤ t →
      t ≤ (101/100 : ℝ)*fullSimplexCenter m B (i.val+1) →
      1 ≤ κ i → κ i ≤ (102/100 : ℝ) →
      volume.real (enlargedSimplex (N+2) B β₀ β ∩
        {u | u i < (91/100 : ℝ)*t ∨ (109/100 : ℝ)*t < u i}) ≤
        (∏ j, κ j)*(C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*
          volume.real (prefixRegion (N+2) B 0 0)) := by
  obtain ⟨C, c, N₀, hC, hc, hconc⟩ := truncated_simplex_concentration hford
  refine ⟨C, c, N₀, hC, hc, ?_⟩
  intro N hN m q B hB hdim β₀ β κ hβ₀ hβ hκ htop hstep i t hi hq htlo hthi hklo hkhi
  have hm : i.val+1 < m := by omega
  have hb : 0 < fullSimplexCenter m B (i.val+1) := by
    unfold fullSimplexCenter
    exact div_pos (mul_pos (mul_pos hB (pow_pos rho_pos _))
      (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hm))) (Nat.cast_pos.mpr (by omega))
  let T := prefixRegion (N+2) B 0 0 ∩ coarseCoordinateBad m B i
  have hT : MeasurableSet T := (measurableSet_prefixRegion _ _ _ _).inter
    (measurableSet_coarseCoordinateBad _ _ _)
  have hTf : volume T ≠ ⊤ := ne_top_of_le_ne_top (prefixRegion_volume_ne_top (by omega) B)
    (measure_mono Set.inter_subset_left)
  have hmap : Set.MapsTo (simplexScale κ)
      (enlargedSimplex (N+2) B β₀ β ∩
        {u | u i < (91/100 : ℝ)*t ∨ (109/100 : ℝ)*t < u i}) T := by
    intro u hu
    refine ⟨enlargedSimplex_mapsTo hβ₀ hβ hκ htop hstep hu.1, ?_⟩
    change simplexScale κ u i < _ ∨ _ < simplexScale κ u i
    rw [simplexScale_apply]
    exact rescaled_band_violation hb ⟨htlo, hthi⟩ ⟨hklo, hkhi⟩ hu.2
  exact (volume_scaled_set_le κ hκ _ T hT hTf hmap).trans
    (mul_le_mul_of_nonneg_left (hconc N hN m q B hB hdim i hi hq)
      (Finset.prod_nonneg (fun j _ => (hκ j).le)))

end TotientAsymptotic

end

end OAI
