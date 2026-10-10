import OAI.Geometry.RuledCovering.Frames

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Closed outer neighborhoods recover a closed set even when its frontier has positive measure. -/
lemma inter_reciprocal_cthickening {E : Type*} [MetricSpace E] (K : Set E)
    (hK : IsClosed K) :
    (⋂ n : ℕ, cthickening (1 / ((n : ℝ) + 1)) K) = K := by
  apply Subset.antisymm
  · intro x hx
    have hxn : ∀ n : ℕ, infEDist x K ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      simpa only [mem_iInter, mem_cthickening_iff] using hx
    have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hz : infEDist x K = 0 := le_antisymm (ge_of_tendsto ht (.of_forall hxn)) bot_le
    exact hK.closure_subset (mem_closure_iff_infEDist_zero.mpr hz)
  · exact subset_iInter fun _ => self_subset_cthickening K

/-- Small open outer neighborhoods, not regularity of the label boundary, justify the weighted
lattice count for arbitrary compact label sets. -/
theorem exists_nice_outer_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] [SFinite (volume : Measure E)]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : E → ℝ} (hF : Continuous F) (hFpos : ∀ x, 0 ≤ F x)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ S : Set E, IsOpen S ∧ Bornology.IsBounded S ∧ K ⊆ S ∧ S ⊆ U ∧
      volume (frontier S) = 0 ∧ (∫ x in S, F x) < (∫ x in K, F x) + eps := by
  let R : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hR : ∀ n, 0 < R n := fun n => by dsimp [R]; positivity
  have hRlim : Tendsto R atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let K' : ℕ → Set E := fun n => cthickening (R n) K
  have hK' : ∀ n, IsCompact (K' n) := fun _ => hK.cthickening
  have hanti : Antitone K' := by
    intro n m hnm
    apply cthickening_mono _ K
    dsimp [R]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hInt : Tendsto (fun n => ∫ x in K' n, F x) atTop (𝓝 (∫ x in K, F x)) := by
    have ht := tendsto_setIntegral_of_antitone (μ := volume)
      (fun n => (hK' n).measurableSet) hanti
      ⟨0, hF.continuousOn.integrableOn_compact (μ := volume) (hK' 0)⟩
    rwa [show (⋂ n, K' n) = K from inter_reciprocal_cthickening K hK.isClosed] at ht
  obtain ⟨d, hd, hdU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hevent : ∀ᶠ n in atTop, (∫ x in K' n, F x) < (∫ x in K, F x) + eps ∧ R n < d :=
    (hInt.eventually (Iio_mem_nhds (lt_add_of_pos_right _ heps))).and
      (hRlim.eventually (Iio_mem_nhds hd))
  obtain ⟨n, hnInt, hnd⟩ := hevent.exists
  obtain ⟨r, hr, hrnull⟩ := exists_null_frontier_thickening volume K (hR n)
  refine ⟨thickening r K, isOpen_thickening, hK.isBounded.thickening,
    self_subset_thickening hr.1 K, ?_, hrnull, ?_⟩
  · exact (thickening_subset_cthickening r K).trans
      ((cthickening_mono (hr.2.le.trans hnd.le) K).trans hdU)
  · have hsub : thickening r K ⊆ K' n :=
      (thickening_subset_cthickening r K).trans (cthickening_mono hr.2.le K)
    exact (setIntegral_mono_set
      (hF.continuousOn.integrableOn_compact (μ := volume) (hK' n))
      (.of_forall hFpos) (.of_forall hsub)).trans_lt hnInt

/-- The square lattice in the displayed (possibly nonorthonormal) parameter coordinates. -/
def coordinateGrid (n : ℕ) : Set (Fin 2 → ℝ) :=
  (n : ℝ)⁻¹ • (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2))) : Set (Fin 2 → ℝ))

lemma finite_inter_coordinateGrid {S : Set (Fin 2 → ℝ)} (hS : Bornology.IsBounded S)
    {n : ℕ} (hn : n ≠ 0) : (S ∩ coordinateGrid n).Finite := by
  classical
  unfold coordinateGrid
  rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (Nat.cast_ne_zero.mpr hn))]
  exact ZSpan.setFinite_inter _ hS

/-- A finite lattice retained around any compact label set has arbitrarily accurate weighted
cost. The finite set is the intersection with a fixed regular outer neighborhood, so no
assumption on the boundary or positive area of `K` occurs here. -/
theorem finite_weighted_grid_outer {K U : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : (Fin 2 → ℝ) → ℝ} (hF : Continuous F) (hFpos : ∀ x, 0 ≤ F x)
    (R : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ S : Set (Fin 2 → ℝ), S.Finite ∧
      S ⊆ U ∩ coordinateGrid n ∧
      (∀ b ∈ coordinateGrid n, (∃ p ∈ K, dist b p ≤ R / n) → b ∈ S) ∧
      (∑' b : S, F b) / (n : ℝ) ^ 2 < (∫ p in K, F p) + eps := by
  obtain ⟨O, hOo, hOb, hKO, hOU, hOf, hOI⟩ :=
    exists_nice_outer_integral hK hU hKU hF hFpos (half_pos heps)
  obtain ⟨d, hd, hdO⟩ := hK.exists_cthickening_subset_open hOo hKO
  have hsum := tendsto_tsum_div_pow_atTop_integral O F hF hOb hOo.measurableSet hOf
  have hcost : ∀ᶠ n : ℕ in atTop,
      (∑' b : ↑(O ∩ coordinateGrid n), F b) / (n : ℝ) ^ 2 <
        (∫ p in O, F p) + eps / 2 := by
    simpa only [coordinateGrid, Fintype.card_fin] using
      hsum.eventually (Iio_mem_nhds (lt_add_of_pos_right _ (half_pos heps)))
  have hsmall : ∀ᶠ n : ℕ in atTop, R / (n : ℝ) < d := by
    have ht : Tendsto (fun n : ℕ => R / (n : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) :
        Tendsto (fun n : ℕ => R * (n : ℝ)⁻¹) atTop (𝓝 (R * 0)))
    exact ht.eventually (Iio_mem_nhds hd)
  filter_upwards [eventually_gt_atTop 0, hcost, hsmall] with n hn hcost hnsmall
  refine ⟨hn, O ∩ coordinateGrid n, finite_inter_coordinateGrid hOb hn.ne',
    Set.inter_subset_inter_left _ hOU, ?_, ?_⟩
  · intro b hb ⟨p, hp, hbp⟩
    exact ⟨hdO ((thickening_subset_cthickening d K)
      (mem_thickening_iff.mpr ⟨p, hp, hbp.trans_lt hnsmall⟩)), hb⟩
  · linarith

end RuledApproximation

end

end OAI
