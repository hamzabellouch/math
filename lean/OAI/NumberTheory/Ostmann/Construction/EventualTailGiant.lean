import OAI.NumberTheory.Ostmann.Construction.TailGiantBlockSelection
import OAI.NumberTheory.Ostmann.Construction.GiantBlockScales
import OAI.NumberTheory.Ostmann.Construction.GiantNormalizerSharp

namespace OAI

/-! # The initial giant for the actual large summand tails -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- Only the favorable block supply remains as a combinatorial input here.
The endpoint law, collision budget, block margins and normalizer are all
constructed from the actual summands and the cited published inputs. -/
theorem EventuallyPrimeSumset.eventual_giant_from_favorable_blocks
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C γ c : ℝ) (hM : MertensEstimate C) (hγ : 0 < γ) (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ X : ℝ, Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp X →
      ∀ lo : ℝ, Real.exp ((5 / 100 : ℝ) * L) ≤ lo → lo ≤ Real.exp ((9 / 10 : ℝ) * L) →
      ⌈Real.exp (lo + 10 * Real.exp ((1 / 100 : ℝ) * L) + 3)⌉₊ ≤ tailCollisionCutoff X →
      ∀ (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime ∧ lo ≤ Real.log p ∧
        Real.log p ≤ lo + 10 * Real.exp ((1 / 100 : ℝ) * L)),
      (∀ p ∈ F, ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) →
      (∀ p (hp : p ∈ F), let _ : Fact p.Prime := ⟨(hF p hp).1⟩;
        γ ≤ (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (tailDensityMask A N p) b‖) →
      c * (10 * Real.exp ((1 / 100 : ℝ) * L)) ≤ ∑ p ∈ F, Real.log (p : ℝ) / p →
      ∃ G : ℤ, lo - 2 ≤ G ∧ (G : ℝ) ≤ (lo - 2) + 12 * Real.exp ((1 / 100 : ℝ) * L) ∧
        Real.exp (-(91 / 100 : ℝ) * L) ≤ smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
        smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100 : ℝ) * L ∧
        γ * c / 32 < ∑ p : smoothGiantPrimeRange G,
          smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G p *
            tailGiantEndpointMean A N F (summandTail A (summandTailCutoff X) hi) p := by
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hlarge
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff N)
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  refine ⟨a, ha, ?_⟩
  filter_upwards [eventual_giant_block_scales a C γ c hγ hc, P0.giant_normalizer_sharp,
    ht.eventually (eventually_ge_atTop (max X₀ X₁))] with L hscale hnorm hlargeX
  intro X hXlo hXhi hi hhi lo hlo hhiLo hcut F hF hFbal hFγ hFmass
  have hX : 0 < X := (Real.exp_pos _).trans_le hXlo
  have hcuts := hX₁ X ((le_max_right _ _).trans (hlargeX.trans hXlo))
  obtain ⟨hsA, hsB, _, _, _⟩ := hX₀ X ((le_max_left _ _).trans (hlargeX.trans hXlo)) hi hhi
  let width := 10 * Real.exp ((1 / 100 : ℝ) * L)
  let P := smoothGiantPrimeRange (lo + width + 2)
  let E := summandTail A (summandTailCutoff X) hi
  let D := summandTail B (summandTailCutoff X) hi
  have hPprime : ∀ p ∈ P, p.Prime := smoothGiantPrimeRange_prime _
  have hPsub : P ⊆ Nat.primesLE (tailCollisionCutoff X) := by
    intro p hp
    have hpU := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have heq : lo + width + 2 + 1 = lo + width + 3 := by ring
    rw [heq] at hpU
    exact Nat.mem_primesLE.mpr ⟨hpU.trans hcut, hPprime p hp⟩
  have hbudgetAll := uniform_tail_collision_bound hA hB N (summandTailCutoff X) hi a X C
    ha hcuts.1 hcuts.2.1 hhi hcuts.2.2 (fun p hp => hN p (Nat.prime_of_mem_primesLE hp))
    (by simpa only [positiveSummandTail_card] using hsA)
    (by simpa only [negativeSummandTail_card] using hsB) hM.lower
  have hnon (p : ℕ) (hp : p ∈ Nat.primesLE (tailCollisionCutoff X)) :
      0 ≤ Real.log (p : ℝ) * tailCollisionDefect A N p E D
        (fun _ => (E.card : ℝ)⁻¹) (fun _ => (D.card : ℝ)⁻¹) := by
    apply mul_nonneg (Real.log_natCast_nonneg p)
    apply collisionDefect_nonneg
    · exact tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos
    · exact tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos
        (hN p (Nat.prime_of_mem_primesLE hp))
    · exact (tailSupport_card_add_complement A N p).le
  have hbudget : (∑ p ∈ P, Real.log (p : ℝ) * tailCollisionDefect A N p E D
      (fun _ => (E.card : ℝ)⁻¹) (fun _ => (D.card : ℝ)⁻¹)) ≤ tailDefectBudget a C X := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun p hp _ => hnon p hp)).trans
    simpa only [tailDefectBudget, E, D, one_div] using hbudgetAll
  have hB0 : 0 ≤ tailDefectBudget a C X :=
    (Finset.sum_nonneg fun p hp => hnon p (hPsub hp)).trans hbudget
  obtain ⟨hlo5, hwidth, hupper, hsmall, hgeometry⟩ := hscale lo X hlo hhiLo hX hXhi
  obtain ⟨G, hGlo, hGhi, _, hmean⟩ := tail_giant_of_favorable_block hA hB N F E D
    (fun _ => (D.card : ℝ)⁻¹) lo width γ c (tailDefectBudget a C X) C hM hlo5
    (by dsimp [width]; positivity) hγ hc hB0 hwidth hupper
    (fun p hp => hN p (hPprime p hp)) hF hFbal hFγ
    (fun p hp x hx => by
      obtain ⟨hxA, hxlo, _⟩ := (mem_summandTail A _ _ x).mp hx
      refine ⟨hxA, ?_⟩
      have hple := Nat.le_of_mem_primesLE (hPsub hp)
      omega) hbudget hFmass hsmall
  obtain ⟨hGreserve, hG2, hGlower, hGupper⟩ := hgeometry G hGlo hGhi
  obtain ⟨hmass, hcg⟩ := hnorm G hG2 hGlower hGupper
  exact ⟨G, hGlo, hGreserve, hmass, hcg, hmean⟩

end Ostmann

end OAI
