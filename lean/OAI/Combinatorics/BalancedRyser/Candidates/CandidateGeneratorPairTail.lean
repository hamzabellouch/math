import OAI.Combinatorics.BalancedRyser.Candidates.CandidateGeneratorPairMoments

namespace OAI

namespace Balanced.CandidateGeneratorPair

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance : MeasurableSpace F := ⊤

def momentConstant (s : ℕ) : ℝ :=
  (32768 * (((s - 1)*4 : ℕ) + 3)^4 : ℝ)^s

theorem momentConstant_nonneg (s : ℕ) : 0 ≤ momentConstant s := by
  unfold momentConstant
  positivity

theorem count_upper_tail (e : Finset (Direction F)) (he : e.card = 2)
    (s : ℕ) (t : ℝ) (ht : 0 < t) :
    (offsetLaw F).toMeasure.real {M | t ≤ (count e M : ℝ)} ≤
      momentConstant s / t^s := by
  let μ := (offsetLaw F).toMeasure
  have hsub : {M : MergedPairs F | t ≤ (count e M : ℝ)} ⊆
      {M | t^s ≤ (count e M : ℝ)^s} := by
    intro M hM
    exact pow_le_pow_left₀ ht.le hM s
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun M => (count e M : ℝ)^s)
    (Eventually.of_forall (fun _ => by positivity)) Integrable.of_finite (t^s)
  have hmoment : (∫ M, (count e M : ℝ)^s ∂μ) ≤ momentConstant s :=
    count_moment_le e he s
  have hbound : t^s * μ.real {M | t ≤ (count e M : ℝ)} ≤ momentConstant s :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity)).trans
      (hm.trans hmoment)
  apply (le_div_iff₀ (pow_pos ht s)).mpr
  simpa only [mul_comm] using hbound

theorem any_pair_upper_tail (s : ℕ) (t : ℝ) (ht : 0 < t) :
    (offsetLaw F).toMeasure.real
      {M | ∃ e : Finset (Direction F), e.card = 2 ∧ t ≤ (count e M : ℝ)} ≤
      ((Fintype.card F : ℝ) + 1)^2 * (momentConstant s / t^s) := by
  let E : (Direction F × Direction F) → Set (MergedPairs F) :=
    fun z => {M | z.1 ≠ z.2 ∧ t ≤ (count {z.1, z.2} M : ℝ)}
  have hset : {M : MergedPairs F | ∃ e : Finset (Direction F),
      e.card = 2 ∧ t ≤ (count e M : ℝ)} = ⋃ z, E z := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, E]
    constructor
    · rintro ⟨e, he, hM⟩
      obtain ⟨g, h, hgh, rfl⟩ := Finset.card_eq_two.mp he
      exact ⟨(g,h), hgh, hM⟩
    · rintro ⟨⟨g,h⟩, hgh, hM⟩
      exact ⟨{g,h}, by simp [hgh], hM⟩
  rw [hset]
  calc
    _ ≤ ∑ z : Direction F × Direction F, (offsetLaw F).toMeasure.real (E z) :=
      measureReal_iUnion_fintype_le E
    _ ≤ ∑ _z : Direction F × Direction F, momentConstant s / t^s := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : z.1 = z.2
      · simp only [E, hz, ne_eq, not_true_eq_false, false_and,
          Set.ofPred_false, measureReal_empty]
        exact div_nonneg (momentConstant_nonneg s) (by positivity)
      · exact (measureReal_mono (show E z ⊆ {M | t ≤ (count {z.1,z.2} M : ℝ)}
          from fun _ h => h.2)).trans
          (count_upper_tail {z.1,z.2} (by simp [hz]) s t ht)
    _ = _ := by simp [Direction, Fintype.card_option, Fintype.card_prod, pow_two]

private theorem scale_pair_tail (q C : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C) :
    (q + 1)^2 * (C / q^4) ≤ 4 * C / q^2 := by
  have hq0 : 0 < q := by linarith
  calc
    _ ≤ (2*q)^2 * (C / q^4) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith : q + 1 ≤ 2*q) 2)
        (div_nonneg hC (by positivity))
    _ = _ := by field_simp; ring

theorem any_pair_source_tail :
    (offsetLaw F).toMeasure.real
      {M | ∃ e : Finset (Direction F), e.card = 2 ∧
        (Fintype.card F : ℝ)^(1/100 : ℝ) ≤ (count e M : ℝ)} ≤
      4 * momentConstant 400 / (Fintype.card F : ℝ)^2 := by
  let q : ℝ := Fintype.card F
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := F)
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := F)
  have hp : (q^(1/100 : ℝ))^400 = q^4 := by
    rw [← Real.rpow_mul_natCast hq.le]
    norm_num
  have h := any_pair_upper_tail (F := F) 400 (q^(1/100 : ℝ))
    (Real.rpow_pos_of_pos hq _)
  rw [hp] at h
  exact h.trans (scale_pair_tail q (momentConstant 400) hq1 (momentConstant_nonneg 400))

private theorem squared_denominator_le_linear (q C : ℝ)
    (hq : 1 ≤ q) (hC : 0 ≤ C) : C / q^2 ≤ C / q := by
  apply div_le_div_of_nonneg_left hC (by linarith)
  nlinarith

theorem all_pairs_tendsto_one
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hcard : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => (offsetLaw (F n)).toMeasure.real
      {M | ∀ e : Finset (Direction (F n)), e.card = 2 →
        (count e M : ℝ) ≤ (Fintype.card (F n) : ℝ)^(1/100 : ℝ)})
      atTop (𝓝 1) := by
  let bad : ℕ → ℝ := fun n => (offsetLaw (F n)).toMeasure.real
    {M | ∃ e : Finset (Direction (F n)), e.card = 2 ∧
      (Fintype.card (F n) : ℝ)^(1/100 : ℝ) < (count e M : ℝ)}
  have hqR : Tendsto (fun n => (Fintype.card (F n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcard
  have hbound : Tendsto (fun n => 4 * momentConstant 400 /
      (Fintype.card (F n) : ℝ)) atTop (𝓝 0) := hqR.const_div_atTop _
  have hbad : Tendsto bad atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_ hbound
    apply Eventually.of_forall
    intro n
    have hsub : {M : MergedPairs (F n) | ∃ e : Finset (Direction (F n)),
        e.card = 2 ∧ (Fintype.card (F n) : ℝ)^(1/100 : ℝ) < (count e M : ℝ)} ⊆
        {M | ∃ e : Finset (Direction (F n)), e.card = 2 ∧
          (Fintype.card (F n) : ℝ)^(1/100 : ℝ) ≤ (count e M : ℝ)} := by
      rintro M ⟨e, he, hM⟩
      exact ⟨e, he, hM.le⟩
    have hq : (1 : ℝ) ≤ Fintype.card (F n) := by
      exact_mod_cast Fintype.card_pos (α := F n)
    exact ((measureReal_mono hsub).trans (any_pair_source_tail (F := F n))).trans
      (squared_denominator_le_linear _ _ hq
        (mul_nonneg (by norm_num) (momentConstant_nonneg 400)))
  have hall : Tendsto (fun n => 1 - bad n) atTop (𝓝 (1 - 0 : ℝ)) :=
    tendsto_const_nhds.sub hbad
  have heq (n : ℕ) : (offsetLaw (F n)).toMeasure.real
      {M | ∀ e : Finset (Direction (F n)), e.card = 2 →
        (count e M : ℝ) ≤ (Fintype.card (F n) : ℝ)^(1/100 : ℝ)} = 1 - bad n := by
    have hset : {M : MergedPairs (F n) | ∀ e : Finset (Direction (F n)),
        e.card = 2 → (count e M : ℝ) ≤ (Fintype.card (F n) : ℝ)^(1/100 : ℝ)} =
        {M | ∃ e : Finset (Direction (F n)), e.card = 2 ∧
          (Fintype.card (F n) : ℝ)^(1/100 : ℝ) < (count e M : ℝ)}ᶜ := by
      ext M
      simp
    rw [hset, measureReal_compl (Set.toFinite _).measurableSet]
    simp only [probReal_univ, bad]
  simpa only [sub_zero, ← heq] using hall

theorem count_le_ceil_of_source_bound (e : Finset (Direction F)) (M : MergedPairs F)
    (h : (count e M : ℝ) ≤ (Fintype.card F : ℝ)^(1/100 : ℝ)) :
    count e M ≤ Nat.ceil ((Fintype.card F : ℝ)^(1/100 : ℝ)) := by
  exact_mod_cast h.trans (Nat.le_ceil _)

end
end Balanced.CandidateGeneratorPair

end OAI
