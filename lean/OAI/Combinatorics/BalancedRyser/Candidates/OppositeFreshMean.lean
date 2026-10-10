import OAI.Combinatorics.BalancedRyser.Candidates.OppositeCases
import OAI.Combinatorics.BalancedRyser.Candidates.OppositeFreshConditional

namespace OAI

namespace Balanced.OppositeAssembly

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance : MeasurableSpace F := ⊤

def freshTests (g : Direction F) (D : Finset (Direction F)) : Finset (Label F) :=
  (((eligibleTuples g).product Finset.univ).product Finset.univ).filter
    (fun w => w.2 ∉ D ∧ w.2 ∉ generatorSet w.1.1)

def freshEvent (g : Direction F) (w : Label F) : Set (MergedPairs F) :=
  {M | M ∈ successfulInDirection w.1.1 g ∧
    PairWitness M w.2 (tuplePoint M w.1.1 w.1.2)
      (tuplePoint M w.1.1 (w.1.2+2))}

theorem freshWitnesses_subset_events (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : freshWitnesses g D M ⊆
      (freshTests g D).filter (fun w => M ∈ freshEvent g w) := by
  rintro ⟨⟨T,i⟩,d⟩ hw
  obtain ⟨hw,hd⟩ := Finset.mem_filter.mp hw
  obtain ⟨hT,hs,hdg,hdT,hp⟩ := (mem_witnesses g M T i d).mp hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨hT,Finset.mem_univ _⟩,Finset.mem_univ _⟩,hd,hdT⟩,hs,hp⟩

theorem freshWitnesses_mean_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((freshWitnesses g D M).card : ℝ)) ≤ 327680 * ((m : ℝ)+1)^4 := by
  let μ := (CandidateExposure.exposedLaw D a).toMeasure
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  let p : FourTuple F → ℝ := fun T =>
    ((CandidateExposure.exposedLaw D a).toOuterMeasure (successfulInDirection T g)).toReal
  have hp (T : FourTuple F) : 0 ≤ p T := ENNReal.toReal_nonneg
  have hmean : (∑ T ∈ eligibleTuples g, p T) ≤
      (20480 * ((m : ℝ)+1)^4) * Fintype.card F :=
    successProbabilitySum_le g D a m hD
  have hsum : (∑ w ∈ freshTests g D,
      ((CandidateExposure.exposedLaw D a).toOuterMeasure (freshEvent g w)).toReal) ≤
      8 * ((Fintype.card F : ℝ)+1) / (Fintype.card F : ℝ)^2 *
        ∑ T ∈ eligibleTuples g, p T := by
    calc
      _ ≤ ∑ T ∈ eligibleTuples g, ∑ _i : Fin 4, ∑ _d : Direction F,
          2 * p T / (Fintype.card F : ℝ)^2 := by
        simp only [freshTests, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
        apply Finset.sum_le_sum
        intro T hT
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro d hd
        by_cases hf : d ∉ D ∧ d ∉ generatorSet T
        · simp only [hf]
          exact OppositeFreshConditional.pair_probability_le D a g T d hf.1 hf.2 i (i+2)
        · simp only [hf, ite_false]
          exact div_nonneg (mul_nonneg (by norm_num) (hp T)) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Direction, Fintype.card_option, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        ring
  have hbound : (∫ M, ((freshWitnesses g D M).card : ℝ) ∂μ) ≤
      327680 * ((m : ℝ)+1)^4 := by
    calc
      _ ≤ ∫ M, (((freshTests g D).filter (fun w => M ∈ freshEvent g w)).card : ℝ) ∂μ := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro M
        exact Nat.cast_le.mpr (Finset.card_le_card (freshWitnesses_subset_events g D M))
      _ = ∑ w ∈ freshTests g D,
          ((CandidateExposure.exposedLaw D a).toOuterMeasure (freshEvent g w)).toReal :=
        integral_eventCount_eq_sum _ _ _
      _ ≤ _ := hsum
      _ ≤ 8 * ((Fintype.card F : ℝ)+1) / (Fintype.card F : ℝ)^2 *
          ((20480 * ((m : ℝ)+1)^4) * Fintype.card F) := by
        exact mul_le_mul_of_nonneg_left hmean (by positivity)
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by positivity : 0 < (Fintype.card F : ℝ)^2)).mpr
        have hpos : 0 ≤ ((m : ℝ)+1)^4 := by positivity
        nlinarith [mul_nonneg hpos (mul_nonneg hq.le (sub_nonneg.mpr hq1))]
  rw [PMF.integral_eq_sum] at hbound
  simpa only [smul_eq_mul] using hbound

end
end Balanced.OppositeAssembly

end OAI
