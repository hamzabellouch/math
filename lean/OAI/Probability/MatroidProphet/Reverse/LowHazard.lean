import OAI.Probability.MatroidProphet.Reverse.Bands
import OAI.Probability.MatroidProphet.Reverse.Trace
import OAI.Probability.MatroidProphet.HazardCover

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def bandHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ upper : ℝ) (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if p₀ ≤ reverseHazard M hE κ D G q d h k S ∧
      reverseHazard M hE κ D G q d h k S < upper ∧ d ∈ S h
    then reverseHazard M hE κ D G q d h k S else 0

noncomputable def lowHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (η : ℝ) (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if d ∈ S h ∧ reverseHazard M hE κ D G q d h k S < η
    then reverseHazard M hE κ D G q d h k S else 0

lemma bandHazardCost_mean_eq_exit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (p₀ upper : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (bandHazardCost M hE κ D G q d h p₀ upper) m k S =
      reverseMeanCost M hE κ D G n q (bandExitCost M hE κ D G q d h p₀ upper) m k S := by
  apply reverseMeanCost_eq_of_step M hE κ D G n hG q hq0 hq1
  · intro l R hR
    by_cases hb : p₀ ≤ reverseHazard M hE κ D G q d h l R ∧
        reverseHazard M hE κ D G q d h l R < upper ∧ d ∈ R h
    · simp only [bandHazardCost, hb, bitsExpectation_const]
      rw [reverseHazard_eq_step M hE κ D G n hG q d h hh]
      apply bitsExpectation_congr
      intro C hC
      simp only [bandExitCost, hb.1, hb.2.1, hb.2.2, true_and]
    · have hz : ∀ C, bandExitCost M hE κ D G q d h p₀ upper l R
          ((reverseStepTree M hE κ l D R G n).run C) = 0 := by
        intro C
        unfold bandExitCost
        apply ite_eq_right
        intro hc
        exact hb ⟨hc.1, hc.2.1, hc.2.2.1⟩
      simp only [bandHazardCost, hb, ite_false, hz, bitsExpectation_const]
  · exact closed

lemma dyadic_band_hazard_bound (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (l : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q
      (bandHazardCost M hE κ D G q d h (((2:ℝ)^(l+1))⁻¹) (((2:ℝ)^l)⁻¹)) m k S ≤
        hazardBandBound l := by
  rw [bandHazardCost_mean_eq_exit M hE κ D G n hG q hq0 hq1 d h hh _ _ m k S closed]
  have hp : 0 < ((2:ℝ)^(l+1))⁻¹ := by positivity
  have hp1 : ((2:ℝ)^(l+1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hu : 0 ≤ ((2:ℝ)^l)⁻¹ := by positivity
  have hb := reverse_exit_band_bound M hE κ D G n hG q hq0 hq1 d h hh
    (((2:ℝ)^(l+1))⁻¹) (((2:ℝ)^l)⁻¹) hp hp1 hu m k S closed
  have heq : ((2:ℝ)^l)⁻¹ = 2 * ((2:ℝ)^(l+1))⁻¹ := by
    rw [pow_succ]
    field_simp
  rw [heq, hazardBandBound_eq_certificate_bound] at hb
  simpa only [← heq] using hb

theorem reverse_low_hazard_lt_half (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q
      (lowHazardCost M hE κ D G q d h (((2:ℝ)^12)⁻¹)) m k S < (1:ℝ)/2 := by
  let R := traceHazards M hE κ D G n q d h m k S
  obtain ⟨L, hL⟩ := finite_hazard_cover (fun p : {p : ℝ // p ∈ R} => p.val)
  let B : ℕ → ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ := fun i =>
    bandHazardCost M hE κ D G q d h (((2:ℝ)^(12+i+1))⁻¹) (((2:ℝ)^(12+i))⁻¹)
  have hb0 (i : ℕ) (t : ReverseTransition α) : 0 ≤ B i t.time t.before t.after := by
    dsimp only [B, bandHazardCost]
    split_ifs
    · exact reverseHazard_nonneg M hE κ D G q hq0 hq1 d h _ _
    · exact le_rfl
  have hpoint (C : Finset α) :
      reverseCost M hE κ D G n (lowHazardCost M hE κ D G q d h (((2:ℝ)^12)⁻¹)) m k S C ≤
        ∑ i ∈ range L, reverseCost M hE κ D G n (B i) m k S C := by
    rw [← reverseCost_sum]
    apply reverseCost_le_of_trace
    intro t ht
    dsimp only [lowHazardCost]
    by_cases hs : d ∈ t.before h ∧ reverseHazard M hE κ D G q d h t.time t.before < ((2:ℝ)^12)⁻¹
    · rw [ite_eq_left hs]
      have hp0 := reverseHazard_nonneg M hE κ D G q hq0 hq1 d h t.time t.before
      by_cases hz : reverseHazard M hE κ D G q d h t.time t.before = 0
      · rw [hz]
        exact sum_nonneg (fun i hi => hb0 i t)
      · have hp : 0 < reverseHazard M hE κ D G q d h t.time t.before := lt_of_le_of_ne hp0 (Ne.symm hz)
        have hmem : reverseHazard M hE κ D G q d h t.time t.before ∈ R :=
          mem_traceHazards M hE κ D G n q d h m k S C t ht
        obtain ⟨i, hi, hband⟩ := hL ⟨_, hmem⟩ hp hs.2
        have heq : B i t.time t.before t.after = reverseHazard M hE κ D G q d h t.time t.before := by
          simp only [B, bandHazardCost, hband.1, hband.2, hs.1, true_and, ite_true]
        rw [← heq]
        exact single_le_sum (fun j hj => hb0 j t) hi
    · rw [ite_eq_right hs]
      exact sum_nonneg (fun i hi => hb0 i t)
  have hmean : reverseMeanCost M hE κ D G n q
      (lowHazardCost M hE κ D G q d h (((2:ℝ)^12)⁻¹)) m k S ≤
        ∑ i ∈ range L, reverseMeanCost M hE κ D G n q (B i) m k S := by
    unfold reverseMeanCost
    rw [← bitsExpectation_sum]
    exact bitsExpectation_mono q hq0 hq1 univ (fun C _ => hpoint C)
  apply lt_of_le_of_lt hmean
  apply lt_of_le_of_lt _ (hazardBandBound_sum_lt_half L)
  apply sum_le_sum
  intro i hi
  exact dyadic_band_hazard_bound M hE κ D G n hG q hq0 hq1 d h hh (12+i) m k S closed

end MatroidProphet

end OAI
