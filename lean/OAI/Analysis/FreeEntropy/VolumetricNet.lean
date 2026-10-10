import OAI.Analysis.FreeEntropy.SpectralBlockMask

namespace OAI

universe u1

noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace FiniteEntropySeparation
 variable {E : Type u1} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 theorem separated_card_bound (s : Finset E) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R) (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → ε ≤ ‖c-d‖) :
    (s.card : ℝ) ≤ (1+2*R/ε)^Module.finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := ε/2
  let ρ : ℝ := R+δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A := ⋃ c ∈ s, ball c δ
  have hD : Set.Pairwise (s : Set E) (fun c d => Disjoint (ball c δ) (ball d δ)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    simpa [δ] using hsep c hc d hd hcd
  have hA : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ball_subset_ball' ?_
    rw [dist_zero_right]
    dsimp [ρ]
    linarith [hs x hx]
  have hI : (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E)*μ (ball 0 1) ≤
      ENNReal.ofReal (ρ^Module.finrank ℝ E)*μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ c ∈ s, ball c δ from rfl, measure_biUnion_finset hD (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hA
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have hJ : (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E) ≤ ENNReal.ofReal (ρ^Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 hI
  have hK : (s.card : ℝ)*δ^Module.finrank ℝ E ≤ ρ^Module.finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hJ
  have he : (1+2*R/ε)*δ = ρ := by dsimp [δ,ρ]; field_simp; ring
  apply (mul_le_mul_iff_left₀ (pow_pos hδ _)).mp
  rw [← mul_pow, he]
  exact hK
 theorem compact_finite_net (A : Set E) (hA : IsCompact A) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hAR : ∀ x ∈ A, ‖x‖ ≤ R) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧ (∀ x ∈ A, ∃ y ∈ s, dist x y ≤ ε) ∧
      (s.card : ℝ) ≤ (1+2*R/ε)^Module.finrank ℝ E := by
  classical
  let e : ℝ≥0 := ⟨ε,hε.le⟩
  have he : e/2 ≠ 0 := ne_of_gt (div_pos (show 0 < e from hε) (by norm_num))
  obtain ⟨N,hNA,hNfin,hNcov⟩ := Metric.exists_finite_isCover_of_isCompact (ε := (e/2 : ℝ≥0)) he hA
  have hpn : packingNumber e A ≠ ⊤ := by
    have hb := packingNumber_two_mul_le_externalCoveringNumber (e/2) A
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)] at hb
    exact ne_top_of_le_ne_top hNfin.encard_lt_top.ne (hb.trans hNcov.externalCoveringNumber_le_encard)
  let K := maximalSeparatedSet e A
  have hKfin : K.Finite := Set.encard_ne_top_iff.mp (by simpa [K, encard_maximalSeparatedSet hpn] using hpn)
  refine ⟨hKfin.toFinset, ?_, ?_, ?_⟩
  · intro x hx; exact maximalSeparatedSet_subset (by simpa using hx)
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := isCover_maximalSeparatedSet hpn hx
    refine ⟨y, by simpa using hy, ?_⟩
    exact (edist_le_coe).mp hxy
  · apply separated_card_bound _ hR hε
    · intro x hx; exact hAR x (maximalSeparatedSet_subset (by simpa using hx))
    · intro x hx y hy hxy
      have hh := isSeparated_maximalSeparatedSet (ε := e) (A := A) (by simpa using hx) (by simpa using hy) hxy
      have hh' : e < nndist x y := by simpa only [edist_nndist, ENNReal.coe_lt_coe] using hh
      have hh'' : ε < dist x y := hh'
      simpa only [dist_eq_norm] using hh''.le
end FiniteEntropySeparation

end

end OAI
