import OAI.MeasureTheory.Falconer.Recursion.ParallelProfile

namespace OAI

/-! # Literal parallel-test good sets and their directional buffer -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

theorem finiteTubeCount_direction_transfer {d : ℕ} {ι : Type*}
    (S : Finset ι) (v : ι → Space d) {w u : Sphere d}
    {δ M W₀ W₁ : ℝ} (hδ : 0 ≤ δ) (_hM : 0 ≤ M)
    (hclose : dist w u ≤ δ) (hbound : ∀ i ∈ S, ‖v i‖ ≤ M)
    (hwidth : W₁+2*δ*M ≤ W₀) :
    finiteTubeCount S v W₁ u ≤ finiteTubeCount S v W₀ w := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,ht⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hi,?_⟩
  change ‖perpendicularPart (w:Space d) (v i)‖ ≤ W₀
  have herror := perpendicularPart_direction_error (sphere_norm w) (sphere_norm u) (v i)
  have hdist : ‖(w:Space d)-(u:Space d)‖ ≤ δ := by
    simpa only [Subtype.dist_eq,dist_eq_norm] using hclose
  have hb : 2*‖(w:Space d)-(u:Space d)‖*‖v i‖ ≤ 2*δ*M :=
    mul_le_mul (mul_le_mul_of_nonneg_left hdist (by norm_num)) (hbound i hi)
      (norm_nonneg _) (mul_nonneg (by norm_num) hδ)
  have htri := norm_sub_le_norm_sub_add_norm_sub (perpendicularPart (w:Space d) (v i))
    (perpendicularPart (u:Space d) (v i)) 0
  simp only [sub_zero] at htri
  change ‖perpendicularPart (u:Space d) (v i)‖ ≤ W₁ at ht
  linarith

namespace Regularization
variable {d : ℕ}

noncomputable def parallelGoodSet (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) (W T : ℝ) : Set (Sphere d) :=
  if 0 < ρ (Q.descendant P).carrier then
    {w | (parallelTestCount Q ρ g p P W w : ℝ≥0∞) ≤ ENNReal.ofReal T} else ∅

theorem parallelGoodSet_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) (W T : ℝ) :
    MeasurableSet (parallelGoodSet Q ρ g p P W T) := by
  classical
  unfold parallelGoodSet
  split_ifs
  · exact measurableSet_le (finiteTubeCount_measurable _ _ _) measurable_const
  · exact MeasurableSet.empty

theorem parallelGoodSet_buffer (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) {W₀ W₁ T δ : ℝ} (hδ : 0 ≤ δ)
    (hwidth : W₁+2*δ*(10*((d:ℝ)+1)/(2:ℝ)^g) ≤ W₀)
    {w u : Sphere d} (hw : w ∈ parallelGoodSet Q ρ g p P W₀ T)
    (hclose : dist w u ≤ δ) : u ∈ parallelGoodSet Q ρ g p P W₁ T := by
  classical
  by_cases hocc : 0 < ρ (Q.descendant P).carrier
  · simp only [parallelGoodSet,ite_eq_left hocc,mem_ofPred_eq] at hw ⊢
    have hc := finiteTubeCount_direction_transfer (parallelTestCells Q ρ g p P)
      (fun c => (Q.descendant c).center-(Q.descendant P).center) hδ
      (by positivity : 0 ≤ 10*((d:ℝ)+1)/(2:ℝ)^g) hclose ?_ hwidth
    · exact (Nat.cast_le.mpr hc).trans hw
    · intro c hc
      have h := (mem_ball.mp (Finset.mem_filter.mp hc).2.2).le
      simpa only [dist_eq_norm] using h
  · simp only [parallelGoodSet,ite_eq_right hocc,mem_empty_iff_false] at hw

theorem parallelGoodSet_exceptional (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) (hocc : 0 < ρ (Q.descendant P).carrier)
    (W : ℝ) {T : ℝ} (hT : 0 < T) (ν : Measure (Sphere d)) :
    ν (parallelGoodSet Q ρ g p P W T)ᶜ ≤
      (∫⁻ w, (parallelTestCount Q ρ g p P W w : ℝ≥0∞) ∂ν)/ENNReal.ofReal T := by
  classical
  have he : (parallelGoodSet Q ρ g p P W T)ᶜ =
      {w | ENNReal.ofReal T < (parallelTestCount Q ρ g p P W w : ℝ≥0∞)} := by
    ext w
    simp only [parallelGoodSet,ite_eq_left hocc,mem_compl_iff,mem_ofPred_eq,not_le]
  rw [he]
  exact (finiteTubeCount_exceptional _ _ _ ν (by positivity) ENNReal.ofReal_ne_top).trans_eq
    (by rw [← finiteTubeCount_mean]; rfl)

end Regularization
end Falconer

end OAI
