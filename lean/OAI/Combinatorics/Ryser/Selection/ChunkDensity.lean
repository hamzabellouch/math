import OAI.Combinatorics.Ryser.Selection.ChunkTail
import OAI.Combinatorics.Ryser.Selection.ChunkConditioning
import OAI.Combinatorics.Ryser.Selection.ChunkPartition

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem chunkFeasibleSet_congr (data : Data F n)
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K))
    (pool pool' : Pool F n K) (h : ∀ e ∈ E, pool e = pool' e) :
    chunkFeasibleSet data U E pool = chunkFeasibleSet data U E pool' := by
  funext i
  ext b
  simp only [mem_chunkFeasibleSet]
  exact and_congr Iff.rfl (feasible_congr data E pool pool' h i b)

theorem frozenMass_feasibleSet_eq (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (pool : Pool F n K) :
    frozenMass I (feasibleSet data T pool) = (feasibleMass data I T pool : ℝ) := by
  simp only [frozenMass, feasibleMass, Nat.cast_sum]

theorem prob_adaptive_chunk_recurrence_failure_le
    (D : ℕ) (hD : 1 ≤ D) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (P E : Finset (Position n K)) (hPE : Disjoint P E)
    (α γ : ℝ) (hm : 0 < (I.card : ℝ)) (hγ : 0 < γ)
    (hlarge : (Fintype.card F : ℝ) / (4 * equationBound D) < I.card)
    (hhalf : equationBound D * α = 1 / 2)
    (hsize : (E.card : ℝ) ≤ α * Fintype.card F)
    (hcutoff : (K : ℝ) * D * Real.sqrt (Fintype.card F) ≤ γ * Fintype.card F) :
    (poolLaw F n K).prob (fun pool =>
      frozenMass I (feasibleSet data (P ∪ E) pool) <
        frozenMass I (feasibleSet data P pool) / 2 -
          (α + 2 * equationBound D) * γ *
            ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)) ≤
      (2 : ℝ) ^ E.card *
        (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
          Nat.ceil (γ * Fintype.card F) := by
  classical
  let U : ExposedAssignment (F := F) P → Fin n → Finset (Point F) :=
    fun x => feasibleSet data P (frozenPool P x)
  let H : ExposedAssignment (F := F) P → Pool F n K → Prop := fun x pool =>
    frozenMass I (chunkFeasibleSet data (U x) E pool) < frozenMass I (U x) / 2 -
      (α + 2 * equationBound D) * γ * ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)
  let b : ℝ := (2 : ℝ) ^ E.card *
    (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
      Nat.ceil (γ * Fintype.card F)
  have hcongr : ∀ x : ExposedAssignment (F := F) P,
      ∀ pool pool' : Pool F n K,
      (∀ e, e ∉ P → pool e = pool' e) → (H x pool ↔ H x pool') := by
    intro x pool pool' hpool
    have heq : chunkFeasibleSet data (U x) E pool =
        chunkFeasibleSet data (U x) E pool' := by
      apply chunkFeasibleSet_congr
      intro e he
      exact hpool e (fun heP => Finset.disjoint_left.mp hPE heP he)
    dsimp only [H]
    rw [heq]
  have hbound : ∀ x : ExposedAssignment (F := F) P,
      (poolLaw F n K).prob (H x) ≤ b := by
    intro x
    exact prob_chunk_recurrence_failure_le D hD data hdata I (U x) E α γ
      hm hγ hlarge hhalf hsize hcutoff
  refine (FiniteLaw.prob_mono (poolLaw F n K) ?_).trans
    (poolLaw_prob_adaptive_le P H b hcongr hbound)
  intro pool hfailure
  dsimp only [H, U]
  rw [feasibleSet_frozenPool_restrict]
  have hsets : chunkFeasibleSet data (feasibleSet data P pool) E pool =
      feasibleSet data (P ∪ E) pool := by
    funext i
    exact chunkFeasibleSet_feasibleSet data P E pool i
  rw [hsets]
  exact hfailure

theorem prob_feasibleMass_lt_density_le
    (D : ℕ) (hD : 1 ≤ D) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (T : Finset (Position n K)) (L J0 : ℕ) (α γ : ℝ)
    (hm : 0 < (I.card : ℝ)) (hγ : 0 < γ)
    (hlarge : (Fintype.card F : ℝ) / (4 * equationBound D) < I.card)
    (hhalf : equationBound D * α = 1 / 2)
    (hL : 0 < L) (hLsize : (L : ℝ) ≤ α * Fintype.card F)
    (hcutoff : (K : ℝ) * D * Real.sqrt (Fintype.card F) ≤ γ * Fintype.card F)
    (hJ : chunkCount T L ≤ J0)
    (hbudget : 2 * ((α + 2 * equationBound D) * γ) ≤ (1 / 2 : ℝ) ^ (J0 + 1)) :
    (poolLaw F n K).prob (fun pool =>
      (feasibleMass data I T pool : ℝ) <
        (1 / 2 : ℝ) ^ (J0 + 1) * ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)) ≤
      (chunkCount T L : ℝ) * (2 : ℝ) ^ L *
        (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
          Nat.ceil (γ * Fintype.card F) := by
  classical
  let J := chunkCount T L
  let scale : ℝ := (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2
  let err : ℝ := (α + 2 * equationBound D) * γ
  let mass : Pool F n K → ℕ → ℝ :=
    fun pool j => frozenMass I (feasibleSet data (chunkPrefix T L j) pool)
  let b : ℝ := (2 : ℝ) ^ L *
    (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
      Nat.ceil (γ * Fintype.card F)
  have hscale : 0 ≤ scale := by dsimp only [scale]; positivity
  have hC : 0 ≤ equationBound D := by unfold equationBound; positivity
  have hα : 0 ≤ α := by
    by_contra hnot
    have hmul := mul_nonpos_of_nonneg_of_nonpos hC (le_of_lt (lt_of_not_ge hnot))
    rw [hhalf] at hmul
    norm_num at hmul
  have herr : 0 ≤ err :=
    mul_nonneg (add_nonneg hα (mul_nonneg (by norm_num) hC)) hγ.le
  have htail : 0 ≤ (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
      Nat.ceil (γ * Fintype.card F) :=
    pow_nonneg (div_nonneg (regularTailConstant_nonneg D γ) (Real.sqrt_nonneg _)) _
  have hone (j : ℕ) :
      (poolLaw F n K).prob (fun pool =>
        mass pool (j + 1) < mass pool j / 2 - err * scale) ≤ b := by
    have hcard : (candidateChunk T L j).card ≤ L :=
      candidateChunk_card_le T L j hL
    have hsize : ((candidateChunk T L j).card : ℝ) ≤ α * Fintype.card F :=
      (Nat.cast_le.mpr hcard).trans hLsize
    have hchunk := prob_adaptive_chunk_recurrence_failure_le D hD data hdata I
      (chunkPrefix T L j) (candidateChunk T L j)
      (disjoint_chunkPrefix_candidateChunk T L j) α γ hm hγ hlarge hhalf hsize hcutoff
    have hbound : (2 : ℝ) ^ (candidateChunk T L j).card *
        (regularTailConstant D γ / Real.sqrt (Fintype.card F)) ^
          Nat.ceil (γ * Fintype.card F) ≤ b := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard) htail
    simpa only [mass, err, scale, chunkPrefix_succ] using hchunk.trans hbound
  have hstart (pool : Pool F n K) : scale ≤ mass pool 0 := by
    dsimp only [mass, scale]
    rw [chunkPrefix_zero]
    simp only [feasibleSet_empty, frozenMass, Finset.card_univ,
      card_point, Nat.cast_pow, Finset.sum_const, nsmul_eq_mul]; exact le_rfl
  have hterminal (pool : Pool F n K) :
      mass pool J = (feasibleMass data I T pool : ℝ) := by
    dsimp only [mass, J]
    rw [chunkPrefix_count, frozenMass_feasibleSet_eq]
  have hsubset (pool : Pool F n K)
      (hfailure : (feasibleMass data I T pool : ℝ) < (1 / 2 : ℝ) ^ (J0 + 1) * scale) :
      ∃ j ∈ Finset.range J, mass pool (j + 1) < mass pool j / 2 - err * scale := by
    by_contra hnone
    have hstep : ∀ j < J, mass pool j / 2 - err * scale ≤ mass pool (j + 1) := by
      intro j hj
      by_contra hbad
      exact hnone ⟨j, Finset.mem_range.mpr hj, lt_of_not_ge hbad⟩
    have hdensity := mass_after_chunks_ge_density (mass pool) scale err J J0
      hscale herr (hstart pool) hstep hJ hbudget
    rw [hterminal pool] at hdensity
    exact (not_lt_of_ge hdensity) hfailure
  calc
    _ ≤ (poolLaw F n K).prob (fun pool =>
        ∃ j ∈ Finset.range J, mass pool (j + 1) < mass pool j / 2 - err * scale) :=
      (poolLaw F n K).prob_mono hsubset
    _ ≤ ∑ j ∈ Finset.range J, (poolLaw F n K).prob
        (fun pool => mass pool (j + 1) < mass pool j / 2 - err * scale) :=
      prob_exists_mem_le _ _ _
    _ ≤ ∑ _j ∈ Finset.range J, b := Finset.sum_le_sum (fun j _ => hone j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, J, b]; ring

end RyserCoveringCounterexample.Selection

end

end OAI
