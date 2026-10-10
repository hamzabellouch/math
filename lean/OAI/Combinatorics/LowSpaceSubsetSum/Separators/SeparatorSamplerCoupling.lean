import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSamplerCoupling

namespace OAI

/-! # Bounded sampling of the four actual separator families -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SeparatorExpectation.RoundedParameters

variable {g : ℕ} (S : RoundedParameters g)

private instance sampleNonempty (i : Fin 4) :
    Nonempty (SeparatorSample (Finset.univ : Finset (Fin g)) (S.e i)) :=
  ⟨⟨initialSubset g (S.e i) (S.size_le i),
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, initialSubset_card _ _ _⟩⟩⟩

def samplerCoupling (n : ℕ) : SamplerCoupling (SeparatorCheck.Draws g S.e S.c) :=
  SamplerCoupling.pi 4 (fun i => Fin (S.counts i) →
    SeparatorSample (Finset.univ : Finset (Fin g)) (S.e i))
      (fun i => SamplerCoupling.pi (S.counts i) (fun _ =>
        SeparatorSample (Finset.univ : Finset (Fin g)) (S.e i))
          (fun _ => fixedSizeCoupling n g (S.e i) (S.size_le i)))

theorem samplerCoupling_uniform (n : ℕ) :
    (S.samplerCoupling n).idealLaw = FiniteLaw.uniform := by
  apply SamplerCoupling.pi_uniform
  intro i
  apply SamplerCoupling.pi_uniform
  intro j
  exact fixedSizeCoupling_uniform n g (S.e i) (S.size_le i)

theorem counts_le (i : Fin 4) : S.counts i ≤ 11 * 2 ^ g :=
  rounded_family_size g (S.e i) (S.c i) (S.size_le i) (S.feasible i)
    (separator_denominator_le g (S.e i) (S.c i) (S.count_half i) (S.count_le i))

/-- Each subset uses at most `g` range calls. Repeated subset occurrences
remain independent calls, exactly as in the stored sampled family. -/
theorem samplerCoupling_failure (n : ℕ) :
    (S.samplerCoupling n).failure ≤ (44 * g * 2 ^ g : ℕ) / (2 : ℝ) ^ (n ^ 3) := by
  have hi (i : Fin 4) :
      (SamplerCoupling.pi (S.counts i) (fun _ =>
        SeparatorSample (Finset.univ : Finset (Fin g)) (S.e i))
          (fun _ => fixedSizeCoupling n g (S.e i) (S.size_le i))).failure ≤
        (S.counts i : ℝ) * (g / (2 : ℝ) ^ (n ^ 3)) := by
    simpa using SamplerCoupling.pi_failure_le (S.counts i) (fun _ =>
      SeparatorSample (Finset.univ : Finset (Fin g)) (S.e i))
        (fun _ => fixedSizeCoupling n g (S.e i) (S.size_le i))
        (fun _ => g / (2 : ℝ) ^ (n ^ 3))
        (fun _ => fixedSizeCoupling_failure n g (S.e i) (S.size_le i))
  have h := SamplerCoupling.pi_failure_le 4 (fun i => Fin (S.counts i) →
    SeparatorSample (Finset.univ : Finset (Fin g)) (S.e i))
      (fun i => SamplerCoupling.pi (S.counts i) (fun _ =>
        SeparatorSample (Finset.univ : Finset (Fin g)) (S.e i))
          (fun _ => fixedSizeCoupling n g (S.e i) (S.size_le i)))
      (fun i => (S.counts i : ℝ) * (g / (2 : ℝ) ^ (n ^ 3))) hi
  apply h.trans
  calc
    _ ≤ ∑ _i : Fin 4, ((11 * 2 ^ g : ℕ) : ℝ) * (g / (2 : ℝ) ^ (n ^ 3)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast S.counts_le i) (by positivity)
    _ = _ := by simp; ring

end SeparatorExpectation.RoundedParameters

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def separatorCoupling (h : R.PrimeHistory) (hn : 2200 ≤ n) :
    SamplerCoupling (R.SeparatorDraws h hn) :=
  (separatorParameters h.1.1.2 hn).samplerCoupling n

theorem separatorCoupling_uniform (h : R.PrimeHistory) (hn : 2200 ≤ n) :
    (R.separatorCoupling h hn).idealLaw = R.separatorLaw h hn :=
  (separatorParameters h.1.1.2 hn).samplerCoupling_uniform n

theorem separatorCoupling_failure (h : R.PrimeHistory) (hn : 2200 ≤ n) :
    (R.separatorCoupling h hn).failure ≤
      (44 * (2 * blockHalf n 0) * 2 ^ (2 * blockHalf n 0) : ℕ) / (2 : ℝ) ^ (n ^ 3) :=
  (separatorParameters h.1.1.2 hn).samplerCoupling_failure n

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
