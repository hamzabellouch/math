import OAI.NumberTheory.JointDickman.Counting.InteriorAmplificationWindows
import OAI.NumberTheory.JointDickman.Counting.CoefficientEventBound

namespace OAI

/-! # A positive first moment strictly inside both coefficient cutoffs -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def amplificationInteriorPairs (B T : ℕ) : Finset (ℕ × ℕ) :=
  (amplificationInteriorC B).biUnion fun c => (amplificationInteriorA T c).image fun a => (a, c)

theorem amplificationInteriorPairs_subset {B T : ℕ} (hB : 0 < B) (hT : 0 < T) :
    amplificationInteriorPairs B T ⊆ amplificationCoefficientPairs B T := by
  intro ac hac
  obtain ⟨c, hc, hca⟩ := mem_biUnion.mp hac
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hca
  exact amplificationInteriorPair_mem hB hT hc ha

theorem amplificationInteriorPairs_sum (B T : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ ac ∈ amplificationInteriorPairs B T, f ac) =
      ∑ c ∈ amplificationInteriorC B, ∑ a ∈ amplificationInteriorA T c, f (a, c) := by
  unfold amplificationInteriorPairs
  rw [sum_biUnion]
  · apply sum_congr rfl
    intro c _
    apply sum_image
    intro a _ b _ hab
    exact (Prod.mk.inj hab).1
  · intro c _ d _ hcd
    apply disjoint_left.mpr
    intro ac hac hdc
    obtain ⟨a, _, rfl⟩ := mem_image.mp hac
    obtain ⟨b, _, hb⟩ := mem_image.mp hdc
    exact hcd (congrArg Prod.snd hb).symm

theorem amplification_interior_c_mass
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ B : ℕ in atTop,
      d ≤ ∑ c ∈ amplificationInteriorC B, primeProductMass (auxiliaryPrimes B) (1 / 2) c := by
  obtain ⟨d, E, hd, _, hbound⟩ := half_primeProduct_interval_lower hSD hM hMP
  refine ⟨d / 8, by positivity, ?_⟩
  have hlim : Tendsto (fun B : ℕ => E * (B : ℝ)^(-(80 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 80)).comp
        tendsto_natCast_atTop_atTop).const_mul E)
  filter_upwards [hbound, hlim.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < d / 8))]
    with B hb hs
  have hh := hb (5 / 4) (3 / 2) (by norm_num) (by norm_num) (by norm_num)
  simp only [mul_comm (B : ℝ) (5 / 4), mul_comm (B : ℝ) (3 / 2), amplificationInteriorC] at hh ⊢
  nlinarith only [hh, hs]

/-- The size-and-ratio event has a positive B-normalized first moment,
uniformly in every admissible amplification scale T. -/
theorem interior_amplification_first_moment_lower
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      d ≤ (B : ℝ) * (∑ ac ∈ amplificationInteriorPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) := by
  obtain ⟨da, hda, ha⟩ := amplification_interior_row_mass_lower hSD hM hMP
  obtain ⟨dc, hdc, hc⟩ := amplification_interior_c_mass hSD hM hMP
  refine ⟨da * dc, mul_pos hda hdc, ?_⟩
  filter_upwards [ha, hc, eventually_gt_atTop 0] with B haB hcB hB
  intro T hT hTsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hrows : da / (B : ℝ) *
      (∑ c ∈ amplificationInteriorC B, primeProductMass (auxiliaryPrimes B) (1 / 2) c) ≤
      ∑ ac ∈ amplificationInteriorPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 := by
    rw [mul_sum, amplificationInteriorPairs_sum]
    apply sum_le_sum
    intro c hc
    dsimp only
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right (haB T c hT hTsize hc) (auxiliaryHalfMass_nonneg B c)
  calc
    da * dc = (B : ℝ) * (da / B * dc) := by field_simp
    _ ≤ (B : ℝ) * (da / B * (∑ c ∈ amplificationInteriorC B,
        primeProductMass (auxiliaryPrimes B) (1 / 2) c)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hrows hB0.le

end JointDickman

end OAI
