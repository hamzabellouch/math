import OAI.Probability.GammaPassage.MeanLimit
import OAI.Probability.FirstPassage.Reversal

namespace OAI

namespace GammaFPP
open MeasureTheory Filter Topology PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Undirected reversal followed by translation, on the actual passage times. -/
theorem GammaEnvironment.integral_passageTime_neg
    (h : GammaEnvironment shape rate P τ) (z : Vertex) :
    (∫ ω, passageTime (fun e => τ e ω) 0 (-z) ∂P) =
      ∫ ω, passageTime (fun e => τ e ω) 0 z ∂P := by
  have hr : (∫ ω, passageTime (fun e => τ e ω) 0 (-z) ∂P) =
      ∫ ω, passageTime (fun e => τ e ω) (-z) 0 ∂P := by
    apply integral_congr_ae
    filter_upwards [h.ae_positive] with ω hω
    exact passageTime_symm _ (fun e => (hω e).le) 0 (-z)
  have ht := h.integral_passageTime_translate (-z) 0 z
  simp only [add_zero, neg_add_cancel] at ht
  exact hr.trans ht

theorem GammaEnvironment.meanPassageSequence_neg
    (h : GammaEnvironment shape rate P τ) (z : Vertex) (n : ℕ) :
    meanPassageSequence P τ (-z) n = meanPassageSequence P τ z n := by
  simpa only [meanPassageSequence, smul_neg] using
    h.integral_passageTime_neg (n • z)

theorem GammaEnvironment.directionalMeanConstant_neg
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    directionalMeanConstant h hs hr (-z) = directionalMeanConstant h hs hr z := by
  have hn := h.meanPassageSequence_tendsto hs hr (-z)
  simp only [h.meanPassageSequence_neg] at hn
  exact tendsto_nhds_unique hn (h.meanPassageSequence_tendsto hs hr z)

/-- Limit order applied to finite, integrable mean subadditivity. -/
theorem GammaEnvironment.directionalMeanConstant_add_le
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (x y : Vertex) :
    directionalMeanConstant h hs hr (x + y) ≤
      directionalMeanConstant h hs hr x + directionalMeanConstant h hs hr y := by
  apply le_of_tendsto_of_tendsto (h.meanPassageSequence_tendsto hs hr (x + y))
    ((h.meanPassageSequence_tendsto hs hr x).add
      (h.meanPassageSequence_tendsto hs hr y))
  apply Filter.Eventually.of_forall
  intro n
  have hb := h.mean_passageTime_subadditive hs hr (n • x) (n • y)
  have hd := div_le_div_of_nonneg_right hb (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [meanPassageSequence, smul_add, add_div] using hd

/-- Cofinality of positive natural multiples, proved without a real-index limit. -/
private theorem tendsto_nat_right_multiple (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => n * k) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  refine ⟨b, ?_⟩
  intro n hn
  exact hn.trans (by simpa only [Nat.succ_eq_add_one, zero_add, mul_one] using
    Nat.mul_le_mul_left n (Nat.succ_le_iff.mpr hk))

/-- Natural homogeneity follows from the cofinal subsequence n*k, not an
assumed homogeneous extension. The zero multiplier is a separate case. -/
theorem GammaEnvironment.directionalMeanConstant_nsmul
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) (k : ℕ) :
    directionalMeanConstant h hs hr (k • z) =
      (k : ℝ) * directionalMeanConstant h hs hr z := by
  by_cases hk : k = 0
  · subst k
    simpa only [zero_smul, Nat.cast_zero, zero_mul] using
      h.directionalMeanConstant_zero hs hr
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have ht := ((h.meanPassageSequence_tendsto hs hr z).comp
    (tendsto_nat_right_multiple k (Nat.pos_of_ne_zero hk))).const_mul (k : ℝ)
  have he : (fun n : ℕ => (k : ℝ) *
      (meanPassageSequence P τ z (n * k) / ((n * k : ℕ) : ℝ))) =
      (fun n : ℕ => meanPassageSequence P τ (k • z) n / (n : ℝ)) := by
    funext n
    have hsml : meanPassageSequence P τ z (n * k) =
        meanPassageSequence P τ (k • z) n := by
      simp only [meanPassageSequence, mul_smul]
    rw [hsml, Nat.cast_mul, ← mul_div_assoc,
      mul_comm (k : ℝ) (meanPassageSequence P τ (k • z) n),
      mul_div_mul_right _ _ hkR]
  change Tendsto (fun n : ℕ => (k : ℝ) *
    (meanPassageSequence P τ z (n * k) / ((n * k : ℕ) : ℝ)))
    atTop (𝓝 ((k : ℝ) * directionalMeanConstant h hs hr z)) at ht
  rw [he] at ht
  exact tendsto_nhds_unique (h.meanPassageSequence_tendsto hs hr (k • z)) ht

/-- Integer homogeneity, with |k| represented by its exact natural absolute
value. This includes k=0, negative multipliers, and the zero direction. -/
theorem GammaEnvironment.directionalMeanConstant_zsmul
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) (k : ℤ) :
    directionalMeanConstant h hs hr (k • z) =
      (k.natAbs : ℝ) * directionalMeanConstant h hs hr z := by
  cases k with
  | ofNat n =>
      simpa only [Int.ofNat_eq_natCast, natCast_zsmul, Int.natAbs_natCast] using
        h.directionalMeanConstant_nsmul hs hr z n
  | negSucc n =>
      change directionalMeanConstant h hs hr (Int.negSucc n • z) =
        ((n + 1 : ℕ) : ℝ) * directionalMeanConstant h hs hr z
      rw [negSucc_zsmul, h.directionalMeanConstant_neg hs hr]
      exact h.directionalMeanConstant_nsmul hs hr z (n + 1)

end GammaFPP

end OAI
