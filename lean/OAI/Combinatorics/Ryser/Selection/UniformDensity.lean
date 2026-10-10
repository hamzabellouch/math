import OAI.Combinatorics.Ryser.Selection.ChunkDensity
import OAI.Combinatorics.Ryser.Selection.DensityConstants
import OAI.Combinatorics.Ryser.Selection.ChunkPartitionBounds
import OAI.Combinatorics.Ryser.Selection.ChunkTailAsymptotics

namespace OAI

universe u

namespace RyserCoveringCounterexample.Selection

theorem prob_feasibleMass_lt_densityDelta_le (D : ℕ) (hD : 1 ≤ D) (K : ℕ) :
    ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (n : ℕ) (data : Data F n), Bounded D data → Q ≤ Fintype.card F →
      ∀ (I : Finset (Fin n)) (T : Finset (Position n K)),
      (Fintype.card F : ℝ) / (4 * equationBound D) < I.card →
      T.card ≤ 2 * I.card →
      (poolLaw F n K).prob (fun pool =>
        (feasibleMass data I T pool : ℝ) <
          densityDelta D * ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)) ≤
        (densityChunkCount D : ℝ) *
          Real.exp (-densityRate D * (Fintype.card F : ℝ) *
            Real.log (Fintype.card F : ℝ)) := by
  have hα := densityAlpha_pos D hD
  have hγ := densityGamma_pos D hD
  have hB := regularTailConstant_pos D hD (densityGamma D) hγ
  obtain ⟨Q₀, hQ₀⟩ := exists_threshold_chunk_tail_and_pool_budget
    (densityAlpha D) (densityGamma D) (regularTailConstant D (densityGamma D))
    (K : ℝ) (D : ℝ) hα.le hγ hB
  refine ⟨max Q₀ (Nat.ceil (2 / densityAlpha D)), ?_⟩
  intro F _ _ _ n data hdata hq I T hlarge hT
  have hqpos : (0 : ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  have hqtail : Q₀ ≤ Fintype.card F := (le_max_left _ _).trans hq
  obtain ⟨htail, hpool⟩ := hQ₀ (Fintype.card F) hqtail
  have hqfloor : Nat.ceil (2 / densityAlpha D) ≤ Fintype.card F :=
    (le_max_right _ _).trans hq
  have hratio : 2 / densityAlpha D ≤ (Fintype.card F : ℝ) :=
    (Nat.le_ceil (2 / densityAlpha D)).trans (Nat.cast_le.mpr hqfloor)
  have hfloorlarge : 2 ≤ densityAlpha D * (Fintype.card F : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hα).mp hratio
  have hLpos : 0 < Nat.floor (densityAlpha D * (Fintype.card F : ℝ)) :=
    floor_chunkSize_pos (densityAlpha D) (Fintype.card F : ℝ) hfloorlarge
  have hLle : (Nat.floor (densityAlpha D * (Fintype.card F : ℝ)) : ℝ) ≤
      densityAlpha D * (Fintype.card F : ℝ) :=
    floor_chunkSize_le (densityAlpha D) (Fintype.card F : ℝ) hα hqpos
  have hIcard : I.card ≤ D * Fintype.card F := by
    have hIn : I.card ≤ n := by simpa only [Fintype.card_fin] using I.card_le_univ
    exact hIn.trans hdata.1
  have hTcard : T.card ≤ 2 * D * Fintype.card F := by
    calc
      T.card ≤ 2 * I.card := hT
      _ ≤ 2 * (D * Fintype.card F) := Nat.mul_le_mul_left 2 hIcard
      _ = _ := by ring
  have hTreal : (T.card : ℝ) ≤ 2 * (D : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast hTcard
  have hJreal := chunkCount_floor_le T (densityAlpha D) (Fintype.card F : ℝ)
    (D : ℝ) hα hqpos hfloorlarge hTreal (Nat.cast_nonneg D)
  rw [← density_chunkCount_identity D] at hJreal
  have hJ : chunkCount T (Nat.floor (densityAlpha D * (Fintype.card F : ℝ))) ≤
      densityChunkCount D := by exact_mod_cast hJreal
  have hC : 0 < equationBound D := by
    have hDr : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
    unfold equationBound
    positivity
  have hm : 0 < (I.card : ℝ) :=
    (div_pos hqpos (mul_pos (by norm_num) hC)).trans hlarge
  have hfinite := prob_feasibleMass_lt_density_le D hD data hdata I T
    (Nat.floor (densityAlpha D * (Fintype.card F : ℝ))) (densityChunkCount D)
    (densityAlpha D) (densityGamma D) hm hγ hlarge
    (equationBound_mul_densityAlpha D hD) hLpos hLle hpool hJ
    (density_error_budget D hD).le
  have hsmall := chunk_tail_le_exp_of_length_le
    (densityAlpha D) (densityGamma D) (regularTailConstant D (densityGamma D))
    (Fintype.card F : ℝ) (Nat.floor (densityAlpha D * (Fintype.card F : ℝ)))
    hB.le hLle htail
  have hcombined :
      (poolLaw F n K).prob (fun pool =>
        (feasibleMass data I T pool : ℝ) <
          densityDelta D * ((I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)) ≤
      (chunkCount T (Nat.floor (densityAlpha D * (Fintype.card F : ℝ))) : ℝ) *
        Real.exp (-(densityGamma D / 4) * (Fintype.card F : ℝ) *
          Real.log (Fintype.card F : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hsmall
      (Nat.cast_nonneg (chunkCount T (Nat.floor (densityAlpha D * (Fintype.card F : ℝ)))))
    simpa only [densityDelta] using
      hfinite.trans (by simpa only [mul_assoc] using hmul)
  calc
    _ ≤ (chunkCount T (Nat.floor (densityAlpha D * (Fintype.card F : ℝ))) : ℝ) *
        Real.exp (-(densityGamma D / 4) * (Fintype.card F : ℝ) *
          Real.log (Fintype.card F : ℝ)) := hcombined
    _ ≤ (densityChunkCount D : ℝ) *
        Real.exp (-(densityGamma D / 4) * (Fintype.card F : ℝ) *
          Real.log (Fintype.card F : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hJ) (Real.exp_pos _).le
    _ = _ := rfl

end RyserCoveringCounterexample.Selection

end OAI
