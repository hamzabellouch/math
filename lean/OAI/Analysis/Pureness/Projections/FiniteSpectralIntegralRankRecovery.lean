import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralRootBounds
import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralPositivity

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace MeasureTheory Set Filter
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
end CuntzPureness

end

end OAI
