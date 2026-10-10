import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionFunctions.FiniteSpectralIntegralCommuting
import OAI.Analysis.JiangSu.DimensionFunctions.FiniteSpectralIntegralRootBounds
import OAI.Analysis.JiangSu.Comparison.FiniteLscComparison

namespace OAI

noncomputable section


namespace Pureness
open TraceCone MeasureTheory Set OrderedSemigroup
open scoped ENNReal NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteSpectralIntegral_cut_lower_bound
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) (ε : ℝ≥0) :
    d (finitePositiveClass n (Positive.cut ε M)) * (ε : ℝ≥0∞) ≤ finiteSpectralIntegral d n M := by
  rw [← ENNReal.ofReal_coe_nnreal,← positive_halfline_indicator_integral]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  by_cases htε : t < ε
  · rw [Set.indicator_of_mem (show t ∈ Iio (ε : ℝ) from htε)]
    have hle : t.toNNReal ≤ ε := by
      change (t.toNNReal : ℝ) ≤ ε
      rw [Real.coe_toNNReal t (le_of_lt ht)]
      exact htε.le
    exact finiteCutValue_antitone d hd n M hle
  · rw [Set.indicator_of_notMem (show t ∉ Iio (ε : ℝ) from htε)]
    exact bot_le

theorem finiteSpectralIntegral_pos
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n))
    (hpos : 0 < regularizedFiniteDimension d hd (finitePositiveClass n M)) :
    0 < finiteSpectralIntegral d n M := by
  rw [regularizedFiniteDimension_eval] at hpos
  obtain ⟨ε,hε⟩ := lt_iSup_iff.mp hpos
  obtain ⟨hεpos,hcut⟩ := lt_iSup_iff.mp hε
  exact (ENNReal.mul_pos hcut.ne' (by exact_mod_cast hεpos.ne')).trans_le
    (finiteSpectralIntegral_cut_lower_bound d hd n M ε)

variable [Nontrivial A]

theorem regularizedState_positive_nonzero (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
    (x : finiteCuntzSubmonoid (A := A)) (hx : x ≠ 0) :
    0 < regularizedFiniteDimension f.toAddHom f.monotone x := by
  apply pos_iff_ne_zero.mpr
  intro hz
  obtain ⟨k,hk⟩ := finiteCuntz_nonzero_orderUnit hsimple x hx finiteUnitClass
  have h := regularizedFiniteDimension_monotone f.toAddHom f.monotone hk
  rw [map_nsmul,hz,nsmul_zero] at h
  exact (not_le_of_gt (finiteState_regularized_unit hsimple y hy f).1) h

omit [Nontrivial A] in
theorem regularizedState_integral_finite (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    finiteSpectralIntegral (regularizedFiniteDimension f.toAddHom f.monotone) n M ≠ ⊤ := by
  apply finiteSpectralIntegral_ne_top _ (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
  exact ne_top_of_le_ne_top (finiteCuntz_state_finite hsimple y hy f _)
    (regularizedFiniteDimension_le f.toAddHom f.monotone _)

theorem regularizedState_integral_positive (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
    (n : ℕ) (M : Positive (FinMatrix A n)) (hM : M.1 ≠ 0) :
    0 < finiteSpectralIntegral (regularizedFiniteDimension f.toAddHom f.monotone) n M := by
  apply finiteSpectralIntegral_pos _ (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
  erw [regularizedFiniteDimension_idempotent]
  exact regularizedState_positive_nonzero hsimple y hy f _
    (fun h => hM ((finitePositiveClass_eq_zero_iff n M).mp h))

omit [Nontrivial A] in
theorem regularizedState_integral_unit (y : finiteCuntzSubmonoid (A := A)) (f : StateSpace y) :
    finiteSpectralIntegral (regularizedFiniteDimension f.toAddHom f.monotone) 1 ⟨1,zero_le_one⟩ =
      f.1 finiteUnitClass := by
  rw [finiteSpectralIntegral_projection _ _ _ (by simp [IsIdempotentElem])]
  exact regularizedFiniteDimension_projection f.toAddHom f.monotone 1 ⟨1,zero_le_one⟩ (by simp [IsIdempotentElem])

end Pureness


namespace Pureness
open TraceCone MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finiteSpectralIntegral_root_cut_lower
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) (hM : ‖M.1‖ ≤ 1)
    (δ r α : ℝ≥0) (hr : 0 < r) (hα : (α : ℝ) < (δ : ℝ)^(r : ℝ)) :
    d (finitePositiveClass n (Positive.cut δ M)) * (α : ℝ≥0∞) ≤
      finiteSpectralIntegral d n (Positive.power r M) := by
  have hc : CuntzBelow (Positive.cut δ M) (Positive.cut α (Positive.power r M)) :=
    CuntzBelow.of_le_smul _ _ _ (one_div_nonneg.mpr (sub_pos.mpr hα).le)
      (positive_cut_le_smul_root_cut M hM δ r α hr hα)
  have h := hd ((finitePositiveClass_le_iff n _ _).mpr ((cuntzSubequiv_iff_shared _ _).mpr hc))
  exact (mul_le_mul h (le_refl (α : ℝ≥0∞)) bot_le bot_le).trans (finiteSpectralIntegral_cut_lower_bound d hd n _ α)

theorem finiteSpectralIntegral_cut_le_iSup_roots
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) (hM : ‖M.1‖ ≤ 1)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    d (finitePositiveClass n (Positive.cut δ M)) ≤
      ⨆ k, finiteSpectralIntegral d n (Positive.power (Positive.rootExponent k) M) := by
  let R := ⨆ k, finiteSpectralIntegral d n (Positive.power (Positive.rootExponent k) M)
  have hb (α : ℝ≥0) (hα : α < 1) :
      d (finitePositiveClass n (Positive.cut δ M))*(α : ℝ≥0∞) ≤ R := by
    have he : Tendsto (fun k => (δ : ℝ)^(Positive.rootExponent k : ℝ)) atTop (𝓝 1) := by
      have hexp : Tendsto (fun k => (Positive.rootExponent k : ℝ)) atTop (𝓝 0) := by
        simpa [Positive.rootExponent] using (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun k : ℕ => 1/((k : ℝ)+1)) atTop (𝓝 0))
      simpa using tendsto_const_nhds.rpow hexp (Or.inl (show (δ : ℝ) ≠ 0 by exact_mod_cast hδ.ne'))
    obtain ⟨k,hk⟩ := ((tendsto_order.mp he).1 α hα).exists
    exact (finiteSpectralIntegral_root_cut_lower d hd n M hM δ _ α
      (Positive.rootExponent_pos k) hk).trans (le_iSup (fun j => finiteSpectralIntegral d n (Positive.power (Positive.rootExponent j) M)) k)
  let α : ℕ → ℝ≥0 := fun k => (1-(Positive.rootExponent k : ℝ)).toNNReal
  have hα (k : ℕ) : α k < 1 := by
    dsimp [α]
    change ((1-(Positive.rootExponent k : ℝ)).toNNReal : ℝ) < 1
    have hh : (0 : ℝ) ≤ 1-(Positive.rootExponent k : ℝ) :=
      sub_nonneg.mpr (show (Positive.rootExponent k : ℝ) ≤ 1 from Positive.rootExponent_le_one k)
    rw [Real.coe_toNNReal _ hh]
    exact sub_lt_self 1 (Positive.rootExponent_pos k)
  have ht : Tendsto (fun k => (α k : ℝ≥0∞)) atTop (𝓝 1) := by
    have he : Tendsto (fun k => (Positive.rootExponent k : ℝ)) atTop (𝓝 0) := by
      simpa [Positive.rootExponent] using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => 1/((k : ℝ)+1)) atTop (𝓝 0))
    change Tendsto (fun k => ENNReal.ofReal (1-(Positive.rootExponent k : ℝ))) atTop (𝓝 1)
    simpa only [Function.comp_def,sub_zero,ENNReal.ofReal_one] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := (1 : ℝ))).sub he)
  have hlim := ENNReal.Tendsto.mul
    (tendsto_const_nhds (x := d (finitePositiveClass n (Positive.cut δ M))))
    (Or.inr ENNReal.one_ne_top) ht (Or.inl one_ne_zero)
  simpa only [mul_one] using le_of_tendsto hlim (Eventually.of_forall (fun k => hb (α k) (hα k)))

theorem finiteSpectralIntegral_iSup_roots
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (n : ℕ) (M : Positive (FinMatrix A n)) (hM : ‖M.1‖ ≤ 1) :
    (⨆ k, finiteSpectralIntegral d n (Positive.power (Positive.rootExponent k) M)) =
      d (finitePositiveClass n M) := by
  apply le_antisymm (iSup_le (finiteSpectralIntegral_root_le d hd n M hM))
  have he : d (finitePositiveClass n M) = finiteRegularizedValue d n M := by
    rw [← regularizedFiniteDimension_eval d hd n M, regularizedFiniteDimension_eq_of_lowerSemicontinuous d hd hlsc]
  rw [he]
  exact iSup_le fun δ => iSup_le fun hδ => finiteSpectralIntegral_cut_le_iSup_roots d hd n M hM δ hδ

theorem finiteSpectralIntegral_roots_tendsto_contraction
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (n : ℕ) (M : Positive (FinMatrix A n)) (hM : ‖M.1‖ ≤ 1) :
    Tendsto (fun k => finiteSpectralIntegral d n (Positive.power (Positive.rootExponent k) M)) atTop
      (𝓝 (d (finitePositiveClass n M))) := by
  rw [← finiteSpectralIntegral_iSup_roots d hd hlsc n M hM]
  exact tendsto_atTop_iSup (finiteSpectralIntegral_roots_monotone d hd n M hM)


theorem finiteSpectralIntegral_roots_tendsto
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    Tendsto (fun k => finiteSpectralIntegral d n (Positive.power (Positive.rootExponent k) M)) atTop
      (𝓝 (d (finitePositiveClass n M))) := by
  let s : ℝ≥0 := max ‖M.1‖₊ 1
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have he : Positive.smul s (Positive.normalize M) = M := by
    apply Subtype.ext
    change (s : ℝ) • ((s⁻¹ : ℝ≥0) : ℝ) • M.1 = M.1
    rw [NNReal.coe_inv, smul_smul, mul_inv_cancel₀ (show (s : ℝ) ≠ 0 by exact_mod_cast hs.ne'), one_smul]
  have hc : finitePositiveClass n (Positive.normalize M) = finitePositiveClass n M :=
    finitePositiveClass_smul n M s⁻¹ (inv_pos.mpr hs)
  have hlim := finiteSpectralIntegral_roots_tendsto_contraction d hd hlsc n (Positive.normalize M)
    (Positive.normalize_norm_le_one M)
  rw [hc] at hlim
  have hscalar := TraceCone.ExtendedTrace.root_scalars_tendsto_one s hs
  have h := ENNReal.Tendsto.mul hscalar (Or.inl one_ne_zero) hlim (Or.inr ENNReal.one_ne_top)
  simp only [one_mul] at h
  convert h using 1
  funext k
  nth_rw 1 [← he]
  rw [Positive.power_smul _ (Positive.rootExponent_pos k),finiteSpectralIntegral_smul d hd]

theorem finiteSpectralIntegral_root_rank
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    liminf (fun k => finiteSpectralIntegral d n (Positive.power (Positive.rootExponent k) M)) atTop =
      d (finitePositiveClass n M) :=
  (finiteSpectralIntegral_roots_tendsto d hd hlsc n M).liminf_eq

theorem regularizedFiniteDimension_integral_roots_tendsto
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    Tendsto (fun k => finiteSpectralIntegral (regularizedFiniteDimension d hd) n
      (Positive.power (Positive.rootExponent k) M)) atTop
      (𝓝 (regularizedFiniteDimension d hd (finitePositiveClass n M))) := by
  apply finiteSpectralIntegral_roots_tendsto _ (regularizedFiniteDimension_monotone d hd)
  intro m
  simpa only [regularizedFiniteDimension_eval] using finiteRegularizedValue_lowerSemicontinuous d hd m

end Pureness

end

end OAI
