import OAI.Combinatorics.ProgressionColoring.OuterChoiceDefinitions
import OAI.Combinatorics.ProgressionColoring.WordDichotomy
import OAI.Combinatorics.ProgressionColoring.ConstructionHeavyLabelReturn
import OAI.Combinatorics.ProgressionColoring.ConstructionDichotomyScales
import OAI.Combinatorics.ProgressionColoring.ConstructionHeavyLight
import OAI.Combinatorics.ProgressionColoring.HeavyReturnWidth
import OAI.Combinatorics.ProgressionColoring.HeavyReturnFinPath
import OAI.Combinatorics.ProgressionColoring.ShortPeriodPath

namespace OAI

/-!
# The actual outer-coloring dichotomy

The coloring is the selected coloring of literal full labels. A progression
with many light positions is balanced by its global word test. Otherwise its
actual closest heavy-label return supplies a primitive rational path. Short
periods lift affinely; long periods satisfy the actual eligible block tests.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

/-- Every actual cyclic progression is either rich in both outer colors or
has an affine lift in the second representative system. -/
theorem OuterChoice.rich_or_affine {k : ℕ} (s : Data k) (hk : 3 ≤ k)
    (o : OuterChoice s hk) (hg : GeometryScales k) (a d : Group s) :
    (∀ b : Bool, k ≤ 100 * (Finset.univ.filter fun j : Fin k =>
      o.color (fullLabelWord s hk (a, d) j) = b).card) ∨
    ∃ A B : Fin (dimension k) → ℝ, ∀ j : Fin k,
      yRep s.q (dimension k) (lambda k) (a + (j.val : Group s) * d) =
        fun i => A i + (j.val : ℝ) * B i := by
  classical
  rcases rich_or_heavy_word (fullLabelWord s hk (a, d)) o.color
    (o.balanced.global_words _ (o.word_mem (a, d))) with hrich | ⟨hfew, r, hr⟩
  · exact Or.inl hrich
  obtain ⟨j, h, R⟩ := exists_selected_heavy_label_return_of_word s hk hg a d
    (fullLabelWord s hk (a, d) r) hr
  let u : Fin (dimension k) → ℝ := fun i =>
    xRep s.q (dimension k) (a + (j + h) • d) i -
      xRep s.q (dimension k) (a + j • d) i
  let v : Fin (dimension k) → ℝ := fun i =>
    yRep s.q (dimension k) (lambda k) (a + (j + h) • d) i -
      yRep s.q (dimension k) (lambda k) (a + j • d) i
  have hvu : ∀ i, v i = (lambda k : ℝ) * u i := R.dilation_eq
  have hv : ∀ i, |v i| ≤ 4 * cutoff k * (mesh s hk).H / k := R.y_rate
  by_cases hshort : h ≤ dimension k ^ 2
  · right
    obtain ⟨T, _, _, _, hY⟩ := R.primitive_return_path s.pos
    have hmotion : ∀ i, (k : ℝ) * |(lambda k : ℝ) * u i / h| < 1 / 2 := by
      intro i
      rw [← hvu i]
      exact velocity_div_small s hk hg R.gap_pos (hv i)
    have hsmall : 2 * (mesh s hk).H * ((k : ℝ) + 1) < 1 := by
      simpa only [mesh_H] using hg.mesh_lift
    have hsame : ∀ i,
        (mesh s hk).meshLabel
          (yRep s.q (dimension k) (lambda k) (a + j • d) i) =
        (mesh s hk).meshLabel
          (yRep s.q (dimension k) (lambda k) (a + (j + h) • d) i) := by
      intro i
      exact congrArg (fun L => L.2 i) (R.start_label.trans R.end_label.symm)
    have hlift := (mesh s hk).short_period_path_lift s.pos a d T u R.gap_pos
      (short_period_dvd_lambda R.gap_pos R.gap_le hshort) hY
      (mesh_alpha_le s hk) hmotion hsmall
      (show j ≠ j + h by have := R.gap_pos; omega) R.start_lt R.end_lt hsame
    refine ⟨yRep s.q (dimension k) (lambda k) a,
      fun i => (lambda k : ℝ) * u i / h, ?_⟩
    intro z
    simpa only [nsmul_eq_mul] using hlift z.val z.isLt
  · left
    obtain ⟨t, hprimitive, hX, hY⟩ := R.exists_fin_return_path s.pos
    have hfirst : ∀ i, |u i| ≤ 1 / (uniformCount k : ℝ) :=
      literalFullLabel_same_first_distance (mesh s hk) s.q (dimension k)
        (lambda k) (uniformCount k) (uniformCount_pos hk)
        (R.end_label.trans R.start_label.symm)
    have hseparate : 4 * (cutoff k : ℝ) * (mesh s hk).H < 1 := by
      have he : 4 * (cutoff k : ℝ) * (mesh s hk).H < 1 / 2 := by
        simpa only [mesh_H] using hg.rational_separation
      linarith
    have hheavy := R.every_heavy_relative_width s.pos (geometry_cutoff_pos hk)
      (geometry_two_cutoff_le_length hg) (uniformWidth_le_meshH s hk)
      hseparate (lattice_error_small s hk hg R.gap_pos)
    have hblocksmall : (h : ℝ) ≤ (k : ℝ) / 10 := by
      have hh : (h : ℝ) ≤ 2 * cutoff k := by exact_mod_cast R.gap_le
      exact hh.trans hg.heavy_return
    have hperiodmem : h ∈ Finset.Ioc (dimension k ^ 2) (2 * cutoff k) :=
      Finset.mem_Ioc.mpr ⟨Nat.lt_of_not_ge hshort, R.gap_le⟩
    have hlong := literal_long_period_balanced (mesh s hk) s.q (dimension k)
      (lambda k) (uniformCount k) k h (uniformCount_pos hk) a d (cutoff k) u v t
      R.gap_pos (geometry_dimension_ge_three hg) o.color hprimitive
      (fun z _ i => hX z i) (fun z _ i => hY z i) hfirst
      (twice_period_uniformWidth_lt_one s hk hg R.gap_le)
      (fun i _ => velocity_le_mesh s hk hg (hv i))
      (fun i _ => velocity_lt_cut s hk hg (hv i))
      (fun i hi => reducedDenominator_gt_of_not_dvd R.gap_pos R.gap_le hi)
      hg.block_loss hheavy (selected_lightCount_le_of_few s hk a d hfew)
      hblocksmall (o.balanced.eligible_patterns h hperiodmem t)
    intro b
    have hc : (k : ℝ) ≤ 100 *
        ((Finset.univ.filter fun z : Fin k =>
          o.color (fullLabelWord s hk (a, d) z) = b).card : ℝ) := by
      have he : (k : ℝ) / 100 ≤
          ((Finset.univ.filter fun z : Fin k =>
            o.color (fullLabelWord s hk (a, d) z) = b).card : ℝ) := by
        refine (hlong b).trans_eq ?_
        apply congrArg (fun n : ℕ => (n : ℝ))
        apply congrArg (Finset.card : Finset (Fin k) → ℕ)
        apply Finset.ext
        intro z
        constructor
        · intro hz
          apply (@Finset.mem_filter _ _ _ _ _).mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa only [fullLabelWord, fullLabel, nsmul_eq_mul] using
            ((@Finset.mem_filter _ _ _ _ _).mp hz).2
        · intro hz
          apply (@Finset.mem_filter _ _ _ _ _).mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa only [fullLabelWord, fullLabel, nsmul_eq_mul] using
            ((@Finset.mem_filter _ _ _ _ _).mp hz).2
      linarith
    exact_mod_cast hc

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
