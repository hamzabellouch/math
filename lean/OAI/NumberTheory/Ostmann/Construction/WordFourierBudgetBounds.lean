import OAI.NumberTheory.Ostmann.Construction.WordTransferUniformCoefficient

namespace OAI

/-! # Explicit Fourier variation bounds from the actual frequency range -/

namespace Ostmann

open scoped BigOperators Classical SchwartzMap

theorem WordTransferTemplate.weightedLeaves_frequency_mem {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ)
    (z : WeightedWordLeaf σ) (hz : z ∈ template.weightedLeaves t ht env) :
    z.frequency ∈ allFrequencyList n t := by
  induction template generalizing env z with
  | leaf word =>
    have he : z = ⟨true, t, HistoryFormula.listProduct (word.map env)⟩ :=
      List.mem_singleton.mp hz
    subst z
    exact List.mem_singleton_self _
  | @node n d l r ihl ihr =>
    rcases List.mem_append.mp hz with hz | hz
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihl _ _ _ _ hz))
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihr _ _ _ a ha))

theorem WordFourierParameters.frequency_abs_le {σ : Type*} {n : ℕ}
    (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (V : ℝ) (hV : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ V)
    (i : Fin (2 ^ n)) : |p.frequency template t ht i| ≤ V := by
  have hh := hV _ (template.weightedLeaves_frequency_mem t ht .prime _
    (template.leafAt_mem t ht i))
  dsimp only [frequency]
  split_ifs <;> simpa only [abs_neg] using hh

theorem WordFourierParameters.budget_le {σ : Type*} {n : ℕ}
    (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (V H : ℝ) (hV : 0 ≤ V)
    (hf : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ V)
    (hr : ∀ i, p.upper i - p.lower i ≤ H) :
    p.budget template t ht ≤
      (2 * SchwartzMap.seminorm ℝ 0 0 p.profile +
        (SchwartzMap.seminorm ℝ 0 0 p.profile +
          SchwartzMap.seminorm ℝ 0 1 p.profile * V) * H) ^ (2 ^ n) := by
  unfold budget formulaFourierBudget
  have he : (∏ _i : Fin (2 ^ n),
      (2 * SchwartzMap.seminorm ℝ 0 0 p.profile +
        (SchwartzMap.seminorm ℝ 0 0 p.profile +
          SchwartzMap.seminorm ℝ 0 1 p.profile * V) * H)) =
      (2 * SchwartzMap.seminorm ℝ 0 0 p.profile +
        (SchwartzMap.seminorm ℝ 0 0 p.profile +
          SchwartzMap.seminorm ℝ 0 1 p.profile * V) * H) ^ (2 ^ n) := by simp
  rw [← he]
  apply Finset.prod_le_prod₀
  · intro i _
    exact add_nonneg (by positivity) (mul_nonneg (by positivity)
      (sub_nonneg.mpr (p.lower_upper i)))
  · intro i _
    apply add_le_add le_rfl
    apply mul_le_mul _ (hr i) (sub_nonneg.mpr (p.lower_upper i))
      (by positivity)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (p.frequency_abs_le template t ht V hf i) (apply_nonneg _ _))

/-- All variation loss is exponential in the original linear frequency and
bin bounds, uniformly in the reconstructed integers and polynomial coefficients. -/
theorem WordFourierParameters.budget_le_exp {σ : Type*} {n : ℕ}
    (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (S C m : ℝ) (hS : 1 ≤ S) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hS₀ : SchwartzMap.seminorm ℝ 0 0 p.profile ≤ S)
    (hS₁ : SchwartzMap.seminorm ℝ 0 1 p.profile ≤ S)
    (hf : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ Real.exp (C * (1 + m)))
    (hr : ∀ i, p.upper i - p.lower i ≤ Real.exp (C * (1 + m))) :
    p.budget template t ht ≤ Real.exp (((4 * S + 2 * C) * (2 ^ n : ℕ)) * (1 + m)) := by
  let T := Real.exp (C * (1 + m))
  have hT : 1 ≤ T := Real.one_le_exp_iff.mpr (by positivity)
  have hT0 : 0 ≤ T := (by positivity : 0 ≤ Real.exp (C * (1 + m)))
  have hS0 : 0 ≤ S := by linarith
  have hbase : 2 * SchwartzMap.seminorm ℝ 0 0 p.profile +
      (SchwartzMap.seminorm ℝ 0 0 p.profile +
        SchwartzMap.seminorm ℝ 0 1 p.profile * T) * T ≤ 4 * S * T ^ 2 := by
    have h₁ : 2 * SchwartzMap.seminorm ℝ 0 0 p.profile ≤ 2 * S := by linarith
    have h₂ : (SchwartzMap.seminorm ℝ 0 0 p.profile +
        SchwartzMap.seminorm ℝ 0 1 p.profile * T) * T ≤ (S + S * T) * T := by
      gcongr
    have h₃ : S ≤ S * T := le_mul_of_one_le_right hS0 hT
    have h₄ : S * T ≤ S * T ^ 2 := by nlinarith
    nlinarith
  have hexp : 4 * S * T ^ 2 ≤ Real.exp ((4 * S + 2 * C) * (1 + m)) := by
    have hs : 4 * S ≤ Real.exp (4 * S) := (by linarith [Real.add_one_le_exp (4 * S)])
    calc
      _ ≤ Real.exp (4 * S) * T ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg T)
      _ = Real.exp (4 * S + 2 * (C * (1 + m))) := by
        dsimp [T]
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ (2 * SchwartzMap.seminorm ℝ 0 0 p.profile +
        (SchwartzMap.seminorm ℝ 0 0 p.profile +
          SchwartzMap.seminorm ℝ 0 1 p.profile * T) * T) ^ (2 ^ n) :=
      p.budget_le template t ht T T hT0 hf hr
    _ ≤ (Real.exp ((4 * S + 2 * C) * (1 + m))) ^ (2 ^ n) :=
      pow_le_pow_left₀ (by positivity) (hbase.trans hexp) _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end Ostmann

end OAI
