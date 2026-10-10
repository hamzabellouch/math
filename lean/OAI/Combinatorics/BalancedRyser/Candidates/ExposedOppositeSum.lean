import OAI.Combinatorics.BalancedRyser.Probability.ExposedWitnessProbability

namespace OAI

namespace Balanced.ExposedOppositeSum

open CandidateValidityWitness FreshWitnessProbability ExposedWitnessProbability
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def freshTuples (D : Finset (Direction F)) : Finset (FourTuple F) :=
  Finset.univ.filter (fun T => Function.Injective T.generator ∧
    ∀ i, T.generator i ∉ D)

omit [Field F] [DecidableEq F] in

theorem card_fourTuple : Fintype.card (FourTuple F) =
    16 * (Fintype.card F + 1)^4 := by
  let e : FourTuple F ≃ ((Fin 4 → Direction F) × (Fin 4 → Bool)) :=
    { toFun := fun T => (T.generator, T.side)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_prod, Direction, mul_comm]

theorem freshTuples_card_le (D : Finset (Direction F)) :
    (freshTuples D).card ≤ 256 * Fintype.card F ^ 4 := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  calc
    _ ≤ Fintype.card (FourTuple F) := Finset.card_le_univ _
    _ = 16 * (Fintype.card F + 1)^4 := card_fourTuple
    _ ≤ 16 * (2 * Fintype.card F)^4 := by gcongr; omega
    _ = _ := by ring

def oldOppositeFreshSum (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) : ℝ :=
  ∑ T ∈ freshTuples D, ∑ c : F, ∑ d ∈ D.erase g, ∑ i : Fin 4,
    ((exposedLaw D a).toOuterMeasure {M | SuccessfulOn M T (g,c) ∧
      PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2))}).toReal

theorem oldOppositeFreshSum_le_div (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) :
    oldOppositeFreshSum g D a ≤ 2048 * (D.card : ℝ) / Fintype.card F := by
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : ((freshTuples D).card : ℝ) ≤ 256 * (Fintype.card F : ℝ)^4 := by
    exact_mod_cast freshTuples_card_le D
  have hd : ((D.erase g).card : ℝ) ≤ D.card := by
    exact_mod_cast Finset.card_erase_le (s := D) (a := g)
  calc
    _ ≤ ∑ _T ∈ freshTuples D, ∑ _c : F, ∑ _d ∈ D.erase g,
        ∑ _i : Fin 4, 2 * (Fintype.card F : ℝ)⁻¹ ^ 6 := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hinj, hfresh⟩ := (Finset.mem_filter.mp hT).2
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro d hdD
      apply Finset.sum_le_sum
      intro i _
      exact successful_opposite_probability_le D a T hinj hfresh (g,c) d
        (Finset.mem_erase.mp hdD).2 (Finset.mem_erase.mp hdD).1 i
    _ = ((freshTuples D).card : ℝ) * (Fintype.card F : ℝ) *
        ((D.erase g).card : ℝ) * (8 * (Fintype.card F : ℝ)⁻¹ ^ 6) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]
      ring
    _ ≤ (256 * (Fintype.card F : ℝ)^4) * (Fintype.card F : ℝ) *
        (D.card : ℝ) * (8 * (Fintype.card F : ℝ)⁻¹ ^ 6) := by gcongr
    _ = _ := by field_simp; ring

theorem oldOppositeFreshSum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) : oldOppositeFreshSum g D a ≤ 2048 * (D.card : ℝ) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  exact (oldOppositeFreshSum_le_div g D a).trans (div_le_self (by positivity) hq)

def oldOppositeFreshCount (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : ℕ :=
  ∑ T ∈ freshTuples D, ∑ c : F, ∑ d ∈ D.erase g, ∑ i : Fin 4,
    if SuccessfulOn M T (g,c) ∧
      PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2)) then 1 else 0

private theorem probability_eq_weighted_indicator {Ω : Type*} [Fintype Ω]
    (law : PMF Ω) (E : Set Ω) :
    (law.toOuterMeasure E).toReal =
      ∑ ω, (law ω).toReal * (if ω ∈ E then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply_fintype,
    ENNReal.toReal_sum (fun ω _ => by
      by_cases h : ω ∈ E
      · simpa only [Set.indicator_of_mem h] using law.apply_ne_top ω
      · simp [Set.indicator_of_notMem h])]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω ∈ E <;> simp [h]

theorem oldOppositeFreshCount_mean_eq (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∑ M, ((exposedLaw D a) M).toReal * (oldOppositeFreshCount g D M : ℝ)) =
      oldOppositeFreshSum g D a := by
  unfold oldOppositeFreshCount oldOppositeFreshSum
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [probability_eq_weighted_indicator]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h : SuccessfulOn M T (g,c) ∧
      PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2))
  · simp [h]
  · simp [h]

theorem oldOppositeFreshCount_mean_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∑ M, ((exposedLaw D a) M).toReal * (oldOppositeFreshCount g D M : ℝ)) ≤
      2048 * (D.card : ℝ) := by
  rw [oldOppositeFreshCount_mean_eq]
  exact oldOppositeFreshSum_le g D a

end
end Balanced.ExposedOppositeSum

end OAI
