import Mathlib.Probability.Distributions.Binomial
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateMultiplicity

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

section Counting

variable {I F : Type*} [Fintype I] [Fintype F]
variable [DecidableEq I] [DecidableEq F]

theorem card_exact_coordinate_set (target : I → F) (s : Finset I) :
    (Finset.univ.filter (fun ω : I → F =>
      Finset.univ.filter (fun i => ω i = target i) = s)).card =
      (Fintype.card F - 1) ^ (Fintype.card I - s.card) := by
  classical
  have hset : Finset.univ.filter (fun ω : I → F =>
      Finset.univ.filter (fun i => ω i = target i) = s) =
      Fintype.piFinset (fun i =>
        if i ∈ s then {target i} else Finset.univ.erase (target i)) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      have hi : ω i = target i ↔ i ∈ s := by
        simpa using (Finset.ext_iff.mp h i)
      by_cases his : i ∈ s
      · simp [his, hi.mpr his]
      · have hne : ω i ≠ target i := fun he => his (hi.mp he)
        simp [his, hne]
    · intro h
      ext i
      specialize h i
      by_cases his : i ∈ s <;> simp_all
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_singleton,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [Finset.prod_ite]
  simp [← Finset.compl_eq_univ_sdiff, Finset.filter_not, Finset.card_compl]

theorem card_exact_coordinate_matches (target : I → F) (m : ℕ) :
    (Finset.univ.filter (fun ω : I → F =>
      (Finset.univ.filter (fun i => ω i = target i)).card = m)).card =
      (Fintype.card I).choose m *
        (Fintype.card F - 1) ^ (Fintype.card I - m) := by
  classical
  have hsplit := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (I → F)) ((Finset.univ : Finset I).powersetCard m)
    (fun ω => Finset.univ.filter (fun i => ω i = target i))
  have hmem : ∀ ω : I → F,
      (Finset.univ.filter (fun i => ω i = target i)) ∈
        (Finset.univ : Finset I).powersetCard m ↔
      (Finset.univ.filter (fun i => ω i = target i)).card = m := by
    intro ω
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
  simp only [hmem] at hsplit
  rw [← hsplit]
  calc
    _ = ∑ _s ∈ (Finset.univ : Finset I).powersetCard m,
        (Fintype.card F - 1) ^ (Fintype.card I - m) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [card_exact_coordinate_set, (Finset.mem_powersetCard.mp hs).2]
    _ = _ := by simp

theorem uniform_exact_coordinate_matches [Nonempty F] (target : I → F) (m : ℕ) :
    ((PMF.uniformOfFintype (I → F)).toOuterMeasure
      {ω | (Finset.univ.filter (fun i => ω i = target i)).card = m}).toReal =
      ((Fintype.card I).choose m : ℝ) *
        ((Fintype.card F - 1 : ℕ) : ℝ) ^ (Fintype.card I - m) /
          (Fintype.card F : ℝ) ^ Fintype.card I := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    Set.mem_ofPred_eq, Fintype.card_subtype, Fintype.card_fun, Nat.cast_pow]
  rw [card_exact_coordinate_matches]
  simp only [Nat.cast_mul, Nat.cast_pow]

theorem uniform_exact_coordinate_matches_binomial [Nonempty F]
    (target : I → F) (m : ℕ) :
    ((PMF.uniformOfFintype (I → F)).toOuterMeasure
      {ω | (Finset.univ.filter (fun i => ω i = target i)).card = m}).toReal =
      ((Fintype.card I).choose m : ℝ) * (1 / (Fintype.card F : ℝ)) ^ m *
        (1 - 1 / (Fintype.card F : ℝ)) ^ (Fintype.card I - m) := by
  rw [uniform_exact_coordinate_matches]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := F)
  by_cases hm : m ≤ Fintype.card I
  · have hbase : 1 - 1 / (Fintype.card F : ℝ) =
        ((Fintype.card F : ℝ) - 1) / Fintype.card F := by
      field_simp
    rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one, hbase, div_pow, div_pow, one_pow]
    have hpow : (Fintype.card F : ℝ) ^ Fintype.card I =
        (Fintype.card F : ℝ) ^ m * (Fintype.card F : ℝ) ^ (Fintype.card I - m) := by
      rw [← pow_add, Nat.add_sub_of_le hm]
    rw [hpow]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hm)]
    simp

end Counting

section Affine

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def multiplicityParameter (F : Type*) [Fintype F] [Nonempty F] :
    unitInterval :=
  ⟨1 / (Fintype.card F : ℝ), by
    constructor
    · positivity
    · have hq : (1 : ℝ) ≤ Fintype.card F := by
        exact_mod_cast Fintype.card_pos (α := F)
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hq⟩

theorem sampledMultiplicity_atom (p : Point F) (m : ℕ) :
    offsetEventProbability {M : MergedPairs F | sampledMultiplicity M p = m} =
      ((2 * (Fintype.card F + 1)).choose m : ℝ) *
        (1 / (Fintype.card F : ℝ)) ^ m *
        (1 - 1 / (Fintype.card F : ℝ)) ^ (2 * (Fintype.card F + 1) - m) := by
  classical
  let e := Equiv.curry (Direction F) Bool F
  have he := uniform_toOuterMeasure_equiv e
    {M : MergedPairs F | sampledMultiplicity M p = m}
  have h := uniform_exact_coordinate_matches_binomial
    (fun ds : Direction F × Bool => lineEval ds.1 p) m
  unfold offsetEventProbability
  rw [offsetLaw_eq_uniform, ← he]
  simpa [e, Equiv.curry, Function.curry, sampledMultiplicity, OnLine, constituent,
    eq_comm, Fintype.card_prod, Fintype.card_option, Nat.mul_comm] using h

theorem sampledMultiplicity_law (p : Point F) :
    ((offsetLaw F).map (fun M => sampledMultiplicity M p)).toMeasure =
      ProbabilityTheory.binomial (2 * (Fintype.card F + 1)) (multiplicityParameter F) := by
  apply MeasureTheory.Measure.ext_of_measureReal_singleton
  intro m
  rw [ProbabilityTheory.binomial_real_singleton]
  change (((offsetLaw F).map (fun M => sampledMultiplicity M p)).toMeasure {m}).toReal = _
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (measurableSet_singleton _),
    PMF.toOuterMeasure_map_apply]
  exact sampledMultiplicity_atom p m

end Affine

end Balanced

end OAI
