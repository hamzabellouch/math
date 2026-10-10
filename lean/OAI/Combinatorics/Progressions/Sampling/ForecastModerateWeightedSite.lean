import OAI.Combinatorics.Progressions.Estimates.WeightedPlateauSiteApproximation

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {K M : ℕ} [NeZero M]
variable (rows : Finset (Finset α)) (F : Finset (rows → Fin M))

noncomputable def forecastModerateWeightedFourierSum
    (H : ℝ) (β : F → ℂ) (shift z : rows → ℤ) : ℂ :=
  (normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K) : ℂ) *
    (((K : ℂ) / M) ^ rows.card * ∑ k : F, β k *
      (rectangularGridCharacter M k.val shift * star (rectangularGridCharacter M k.val z)))

omit [Fintype α] [DecidableEq α] in
theorem forecastModerateWeightedFourier_model (H : ℝ) (hK : 0 < K)
    (D : F → ℕ) [∀ k, NeZero (D k)] (a : F → rows → ℤ) (ω : F → rows → ℝ)
    (hfreq : ∀ k t, (((k.val t).val : ℝ) / M) = (a k t : ℝ) / D k + ω k t / K)
    (β : F → ℂ) (shift z : rows → ℤ) :
    forecastModerateWeightedFourierSum (K := K) rows F H β shift z =
      finiteResidueModeModel D a (fun k => ((K : ℂ) / M) ^ rows.card * β k)
        (fun k => plateauModeMixture (PMF.pure ()) H (D k) K (a k) (ω k) (fun _ => shift))
        (fun k => integerGridResidue (D k) z) (fun t => (z t : ℝ) / K) := by
  unfold forecastModerateWeightedFourierSum finiteResidueModeModel
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hmode := plateauModeMixture_grid_factor (PMF.pure ()) H (D k) K
    (a k) (ω k) (fun _ => shift) z
  simp only [PMF.toMeasure_pure, integral_dirac] at hmode
  have hphase := (plateau_grid_character_split H hK k.val (a k) (ω k)
    (hfreq k) shift z).trans hmode
  calc
    _ = (((K : ℂ) / M) ^ rows.card * β k) *
        ((normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K) : ℂ) *
          (rectangularGridCharacter M k.val shift * star (rectangularGridCharacter M k.val z))) := by ring
    _ = _ := congrArg (fun z => (((K : ℂ) / M) ^ rows.card * β k) * z) hphase

theorem exists_forecastModerate_weighted_sites {Cell : Type*}
    (H : ℝ) (hK : 0 < K) (shift : rows → ℤ)
    (D : F → ℕ) [∀ k, NeZero (D k)] (a : F → rows → ℤ) (ω : F → rows → ℝ)
    (hfreq : ∀ k t, (((k.val t).val : ℝ) / M) = (a k t : ℝ) / D k + ω k t / K)
    (β : Cell → F → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ cell, (∑ k, ‖β cell k‖) ≤ C)
    (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1)
    (W : ℝ≥0) (hW : ∀ k t, |ω k t| ≤ W)
    {R δ P : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hδP : (δ / (C + 1))⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : F → ℕ, (∀ k, (n k : ℝ) ≤ Real.exp (4 * P + 8)) ∧
      (Fintype.card (PlateauSiteIndex α F n) : ℝ) ≤
        F.card * Real.exp (Fintype.card (Finset α) * (4 * P + 8)) ∧
      ∃ (c : Cell → PlateauSiteIndex α F n → ℂ)
        (f : (k : PlateauSiteIndex α F n) → Finset α → ZMod (D k.1) → ℝ → ℂ),
        (∀ cell, (∑ k, ‖c cell k‖) ≤ C *
          Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P)) ∧
        (∀ k u r x, ‖f k u r x‖ ≤ 1) ∧
        (∀ k u r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k u r)) ∧
        ∀ cell (y : Finset α → ℤ), (∀ u, |(y u : ℝ) / K| ≤ R) →
          ‖forecastModerateWeightedFourierSum (K := K) rows F H (β cell) shift
              (fun t => booleanCoefficient y t) -
            ∑ k, c cell k * ∏ u, f k u (y u : ZMod (D k.1)) ((y u : ℝ) / K)‖ ≤ δ := by
  have htol : 0 < δ / (C + 1) := div_pos hδ (by positivity)
  have hex (k : F) := exists_scalar_integer_plateau_site_approximation
    (PMF.pure ()) H (D k) K rows (a k) (ω k) (fun _ => shift) W (hW k)
    hR htol hP hRP hδP hLP
  choose n hn c f hc hf hLf herr using hex
  let b (cell : Cell) (k : F) := ((K : ℂ) / M) ^ rows.card * β cell k
  have hb (cell : Cell) : (∑ k, ‖b cell k‖) ≤ C := by
    simp only [b, norm_mul, norm_pow, norm_div, Complex.norm_natCast, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (hcap cell) (by positivity)).trans
      (mul_le_of_le_one_left hC hscale)
  refine ⟨n, hn, ?_, (fun cell k => b cell k.1 * c k.1 k.2),
    (fun k => f k.1 k.2), ?_, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using plateauSiteIndex_card_le (α := α) n hn
  · intro cell
    exact sigma_sum_coefficient_norm_le (b cell) c (Real.exp_nonneg _) (hb cell) hc
  · intro k u r x
    exact hf k.1 k.2 u r x
  · intro k u r
    exact hLf k.1 k.2 u r
  · intro cell y hy
    rw [forecastModerateWeightedFourier_model rows F H hK D a ω hfreq]
    have herror := sigma_sum_approximation_error (b cell) _ c
      (fun k l => ∏ u, f k l u (y u : ZMod (D k)) ((y u : ℝ) / K))
      htol.le (hb cell) (fun k => herr k y hy)
    apply herror.trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < C + 1)).mpr
    nlinarith only [hC, hδ]

theorem forecastWeightedGridCoefficient_norm_le
    {Ω O : Type*} [Fintype Ω] [Fintype O]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (w : Ω → ℂ)
    (hw : ∀ x, ‖w x‖ ≤ 1) (M : ℕ) [NeZero M] (k : O → Fin M) :
    ‖p.complexMean (fun x => w x * rectangularGridCharacter M k (Y x))‖ ≤ 1 := by
  apply (p.norm_complexMean_le_mean_norm _).trans
  apply (p.mean_mono (fun x => ?_)).trans_eq (p.mean_const 1)
  rw [norm_mul, rectangularGridCharacter_norm, mul_one]
  exact hw x

theorem forecastWeightedGridCoefficient_retained_mass
    {Ω O : Type*} [Fintype Ω] [Fintype O]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (w : Ω → ℂ)
    (hw : ∀ x, ‖w x‖ ≤ 1) (M : ℕ) [NeZero M] (F : Finset (O → Fin M)) :
    (∑ k : F, ‖p.complexMean (fun x => w x * rectangularGridCharacter M k.val (Y x))‖) ≤ F.card := by
  calc
    _ ≤ ∑ _k : F, (1 : ℝ) := Finset.sum_le_sum (fun k _ =>
      forecastWeightedGridCoefficient_norm_le p Y w hw M k.val)
    _ = _ := by simp

end Erdos3

end

end OAI
