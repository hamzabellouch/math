import OAI.Geometry.IsometricImmersion.Estimates.ActualRemainderFactors

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def chainProductL2Budget (B : ℝ) (H : ℝ≥0) (V : Set Coord) (ell : ℕ) : ℝ≥0∞ :=
  ‖B ^ ell‖ₑ * ((H : ℝ≥0∞) + (volume V) ^ (1 / (2 : ℝ)))

def chainWordL2Budget (C B : ℝ) (H : ℝ≥0) (V : Set Coord) (ell : ℕ)
    (w : ChainWord) : ℝ≥0∞ :=
  ∑ _r : Fin w.arity → Fin 6, ‖C‖ₑ * chainProductL2Budget B H V ell

def chainSumL2Budget (C B : ℝ) (H : ℝ≥0) (V : Set Coord) (ell : ℕ)
    (ws : List ChainWord) : ℝ≥0∞ :=
  (ws.map (chainWordL2Budget C B H V ell)).sum

def firstJetPairL2Budget (C : ℝ) (H : ℝ≥0) : ℝ≥0∞ :=
  ‖C‖ₑ * (H : ℝ≥0∞) + ‖C‖ₑ * (H : ℝ≥0∞)

def actualHighRemainderL2Budget (C Cfirst B : ℝ) (H : ℝ≥0) (V : Set Coord)
    (m : ℕ) : ℝ≥0∞ :=
  chainSumL2Budget C B H V (m + 3) (topResidualWords m) +
    ‖(m + 3 : ℝ)‖ₑ * firstJetPairL2Budget Cfirst H

theorem enorm_pow_mono_of_one_le {B : ℝ} (hB : 1 ≤ B) {a b : ℕ} (hab : a ≤ b) :
    ‖B ^ a‖ₑ ≤ ‖B ^ b‖ₑ := by
  rw [enorm_le_iff_norm_le, Real.norm_of_nonneg (pow_nonneg (by linarith) _),
    Real.norm_of_nonneg (pow_nonneg (by linarith) _)]
  exact pow_le_pow_right₀ hB hab

theorem chainProductL2Budget_lt_top (B : ℝ) (H : ℝ≥0) {V : Set Coord}
    (hVfinite : volume V < (⊤ : ℝ≥0∞)) (ell : ℕ) : chainProductL2Budget B H V ell < (⊤ : ℝ≥0∞) := by
  unfold chainProductL2Budget
  exact ENNReal.mul_lt_top (by finiteness)
    (ENNReal.add_lt_top.mpr ⟨by finiteness,
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hVfinite.ne⟩)

theorem chainWordL2Budget_lt_top (C B : ℝ) (H : ℝ≥0) {V : Set Coord}
    (hVfinite : volume V < (⊤ : ℝ≥0∞)) (ell : ℕ) (w : ChainWord) :
    chainWordL2Budget C B H V ell w < (⊤ : ℝ≥0∞) := by
  unfold chainWordL2Budget
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.mul_lt_top (by finiteness)
    (chainProductL2Budget_lt_top B H hVfinite ell))

theorem chainSumL2Budget_lt_top (C B : ℝ) (H : ℝ≥0) {V : Set Coord}
    (hVfinite : volume V < (⊤ : ℝ≥0∞)) (ell : ℕ) (ws : List ChainWord) :
    chainSumL2Budget C B H V ell ws < (⊤ : ℝ≥0∞) := by
  induction ws with
  | nil => simp [chainSumL2Budget]
  | cons w ws ih =>
      exact ENNReal.add_lt_top.mpr ⟨chainWordL2Budget_lt_top C B H hVfinite ell w, ih⟩

theorem actualHighRemainderL2Budget_lt_top (C Cfirst B : ℝ) (H : ℝ≥0)
    {V : Set Coord} (hVfinite : volume V < (⊤ : ℝ≥0∞)) (m : ℕ) :
    actualHighRemainderL2Budget C Cfirst B H V m < (⊤ : ℝ≥0∞) := by
  unfold actualHighRemainderL2Budget firstJetPairL2Budget
  exact ENNReal.add_lt_top.mpr
    ⟨chainSumL2Budget_lt_top C B H hVfinite (m + 3) (topResidualWords m), by finiteness⟩

theorem scalar_coefficient_eLpNorm_two {V : Set Coord} (hV : MeasurableSet V)
    {a f : Coord → ℝ} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ p ∈ V, |a p| ≤ C) :
    eLpNorm' (fun p => a p * f p) (2 : ℝ) (volume.restrict V) ≤
      ‖C‖ₑ * eLpNorm' f (2 : ℝ) (volume.restrict V) := by
  have hdom : ∀ᵐ p ∂(volume.restrict V), ‖a p * f p‖ ≤ ‖C * f p‖ := by
    filter_upwards [ae_restrict_mem hV] with p hp
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (ha p hp) (abs_nonneg _)
  calc
    _ ≤ eLpNorm' (fun p => C * f p) (2 : ℝ) (volume.restrict V) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := eLpNorm'_const_smul (𝕜 := ℝ) (F := ℝ) (f := f) C (by norm_num)

theorem scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
    {V : Set Coord} (hV : MeasurableSet V)
    {a f : Coord → ℝ} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ p ∈ V, |a p| ≤ C)
    (hmeas : AEStronglyMeasurable (fun p => a p * f p) (volume.restrict V)) :
    eLpNorm (fun p => a p * f p) 2 (volume.restrict V) ≤
      ‖C‖ₑ * eLpNorm f 2 (volume.restrict V) := by
  have hraw : eLpNorm' f (2 : ℝ) (volume.restrict V) ≤
      eLpNorm f 2 (volume.restrict V) := by
    by_cases hf : AEStronglyMeasurable f (volume.restrict V)
    · rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hf, ENNReal.toReal_ofNat]
    · rw [eLpNorm_of_not_aestronglyMeasurable hf]
      exact le_top
  calc
    _ = eLpNorm' (fun p => a p * f p) (2 : ℝ) (volume.restrict V) := by
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmeas, ENNReal.toReal_ofNat]
    _ ≤ ‖C‖ₑ * eLpNorm' f (2 : ℝ) (volume.restrict V) :=
      scalar_coefficient_eLpNorm_two hV hC ha
    _ ≤ _ := mul_le_mul' le_rfl hraw

theorem bounded_real_eLpNorm_two {V : Set Coord} (hV : MeasurableSet V)
    {f : Coord → ℝ} {B : ℝ} (hB : 0 ≤ B) (hf : ∀ p ∈ V, ‖f p‖ ≤ B) :
    eLpNorm' f (2 : ℝ) (volume.restrict V) ≤ ‖B‖ₑ * (volume V) ^ (1 / (2 : ℝ)) := by
  have hdom : ∀ᵐ p ∂(volume.restrict V), ‖f p‖ ≤ ‖B‖ := by
    filter_upwards [ae_restrict_mem hV] with p hp
    simpa only [Real.norm_of_nonneg hB] using hf p hp
  calc
    _ ≤ eLpNorm' (fun _ : Coord => B) (2 : ℝ) (volume.restrict V) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := by
      rw [eLpNorm'_const B (by norm_num), Measure.restrict_apply_univ]

theorem bounded_real_eLpNorm_two_of_aestronglyMeasurable
    {V : Set Coord} (hV : MeasurableSet V)
    {f : Coord → ℝ} {B : ℝ} (hB : 0 ≤ B) (hf : ∀ p ∈ V, ‖f p‖ ≤ B)
    (hmeas : AEStronglyMeasurable f (volume.restrict V)) :
    eLpNorm f 2 (volume.restrict V) ≤ ‖B‖ₑ * (volume V) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmeas, ENNReal.toReal_ofNat]
  exact bounded_real_eLpNorm_two hV hB hf

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

theorem coordinateChainFactor_memLp_two
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hVfinite : volume V < (⊤ : ℝ≥0∞))
    {m : ℕ} {B : ℝ} (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    {w : ChainWord} (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6)
    (i : Fin w.arity) : MemLp (coordinateChainFactor z w r i) 2 (volume.restrict V) := by
  obtain ⟨hpos, -, horders⟩ := topResidualWords_properties m w hw
  have htop := (residual_scalar_factor_orders hw r).1 i
  by_cases hi : m + 2 ≤ chainFactorOrder w r i
  · exact (vertical_state_component_high_eLpNorm hU hz hV hVU hheight
      (w.order i) (hpos i) (horders i) (r i) hi htop).trans_lt (by finiteness)
  · have hilo : chainFactorOrder w r i ≤ m + 1 := by omega
    have hb : ∀ p ∈ V, ‖coordinateChainFactor z w r i p‖ ≤ B := fun p hp =>
      vertical_state_component_low_bound hU hz hVU hB hlow
        (w.order i) (hpos i) (r i) hilo hp
    exact (bounded_real_eLpNorm_two_of_aestronglyMeasurable hV (by linarith) hb
      (((coordinateChainFactor_continuousOn hU hz w r i).mono hVU).aestronglyMeasurable
        (μ := volume) hV)).trans_lt
      (ENNReal.mul_lt_top (by finiteness)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hVfinite.ne))

theorem residual_product_eLpNorm_two
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} (hm : 8 ≤ m + 3) {B : ℝ} (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    {w : ChainWord} (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) :
    eLpNorm (fun p => ∏ i, coordinateChainFactor z w r i p) 2 (volume.restrict V) ≤
      chainProductL2Budget B H V (m + 3) := by
  classical
  obtain ⟨hpos, -, horders⟩ := topResidualWords_properties m w hw
  obtain ⟨hfactorOrders, harity⟩ := residual_scalar_factor_orders hw r
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hmeas : AEStronglyMeasurable (fun p => ∏ i, coordinateChainFactor z w r i p)
      (volume.restrict V) :=
    Finset.univ.aestronglyMeasurable_fun_prod (fun index _ =>
      ((coordinateChainFactor_continuousOn hU hz w r index).mono hVU).aestronglyMeasurable
        (μ := volume) hV)
  by_cases hhigh : ∃ j, m + 2 ≤ chainFactorOrder w r j
  · obtain ⟨j, hj⟩ := hhigh
    have hlowOther : ∀ i ∈ (Finset.univ : Finset (Fin w.arity)).erase j,
        ∀ p ∈ V, ‖coordinateChainFactor z w r i p‖ ≤ B := by
      intro i hi p hp
      have hiorder : chainFactorOrder w r i ≤ m + 1 := by
        by_contra hiorder
        have hieq := residual_scalar_high_unique (i := i) (j := j) hm hw r (by omega) hj
        exact (Finset.mem_erase.mp hi).1 hieq
      exact vertical_state_component_low_bound hU hz hVU hB hlow
        (w.order i) (hpos i) (r i) hiorder hp
    have hjL2 : eLpNorm (coordinateChainFactor z w r j) 2 (volume.restrict V) ≤
        (H : ℝ≥0∞) :=
      vertical_state_component_high_eLpNorm hU hz hV hVU hheight
        (w.order j) (hpos j) (horders j) (r j) hj (hfactorOrders j)
    have hcard : ((Finset.univ : Finset (Fin w.arity)).erase j).card ≤ m + 3 := by
      have he := Finset.card_le_card (Finset.erase_subset j (Finset.univ : Finset (Fin w.arity)))
      have he' : ((Finset.univ : Finset (Fin w.arity)).erase j).card ≤ w.arity := by
        simpa only [Finset.card_univ, Fintype.card_fin] using he
      exact he'.trans harity
    have hp := finite_product_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (coordinateChainFactor z w r) (Finset.mem_univ j) hB0 hV hlowOther hmeas
    calc
      _ ≤ ‖B ^ ((Finset.univ : Finset (Fin w.arity)).erase j).card‖ₑ *
          eLpNorm (coordinateChainFactor z w r j) 2 (volume.restrict V) := hp
      _ ≤ ‖B ^ (m + 3)‖ₑ * ((H : ℝ≥0∞) + (volume V) ^ (1 / (2 : ℝ))) :=
        mul_le_mul' (enorm_pow_mono_of_one_le hB hcard)
          (hjL2.trans (le_add_of_nonneg_right (by positivity)))
      _ = _ := rfl
  · have hlowAll : ∀ i ∈ (Finset.univ : Finset (Fin w.arity)),
        ∀ p ∈ V, ‖coordinateChainFactor z w r i p‖ ≤ B := by
      intro i _ p hp
      have hiorder : chainFactorOrder w r i ≤ m + 1 := by
        have hni : ¬ m + 2 ≤ chainFactorOrder w r i := fun hi => hhigh ⟨i, hi⟩
        omega
      exact vertical_state_component_low_bound hU hz hVU hB hlow
        (w.order i) (hpos i) (r i) hiorder hp
    have hp := finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable
      (μ := volume) Finset.univ (coordinateChainFactor z w r) hB0 hV hlowAll hmeas
    calc
      _ ≤ ‖B ^ w.arity‖ₑ * (volume V) ^ (1 / (2 : ℝ)) := by
        simpa only [Finset.card_univ, Fintype.card_fin] using hp
      _ ≤ ‖B ^ (m + 3)‖ₑ * ((H : ℝ≥0∞) + (volume V) ^ (1 / (2 : ℝ))) :=
        mul_le_mul' (enorm_pow_mono_of_one_le hB harity)
          (le_add_of_nonneg_left (by positivity))
      _ = _ := rfl

theorem coordinateChainTerm_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} (hm : 8 ≤ m + 3) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    {w : ChainWord} (hw : w ∈ topResidualWords m)
    (hcoeff : ∀ r, ∀ p ∈ V, |coordinateChainCoefficient g z w r p| ≤ C) :
    eLpNorm (coordinateChainTerm g z w) 2 (volume.restrict V) ≤
      chainWordL2Budget C B H V (m + 3) w := by
  classical
  have hmeas (r : Fin w.arity → Fin 6) :
      AEStronglyMeasurable (fun p => coordinateChainCoefficient g z w r p *
        ∏ i, coordinateChainFactor z w r i p) (volume.restrict V) :=
    ((coordinateScalarTerm_continuousOn hg hU hz hyy w r).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hterm (r : Fin w.arity → Fin 6) :
      eLpNorm (fun p => coordinateChainCoefficient g z w r p *
        ∏ i, coordinateChainFactor z w r i p) 2 (volume.restrict V) ≤
        ‖C‖ₑ * chainProductL2Budget B H V (m + 3) :=
    (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable hV hC (hcoeff r) (hmeas r)).trans
      (mul_le_mul' le_rfl (residual_product_eLpNorm_two hU hz hV hVU hm hB hlow hheight hw r))
  have he : coordinateChainTerm g z w = fun p =>
      ∑ r : Fin w.arity → Fin 6, coordinateChainCoefficient g z w r p *
        ∏ i, coordinateChainFactor z w r i p :=
    funext (coordinateChainTerm_scalar_expansion g z w)
  rw [he]
  exact finite_sum_eLpNorm_two Finset.univ _
    (fun _ => ‖C‖ₑ * chainProductL2Budget B H V (m + 3))
    (fun indices _ => hmeas indices) (fun indices _ => hterm indices)

theorem coordinateChainSum_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} (hm : 8 ≤ m + 3) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C)
    (ws : List ChainWord) (hws : ∀ w ∈ ws, w ∈ topResidualWords m) :
    eLpNorm (coordinateChainSum g z ws) 2 (volume.restrict V) ≤
      chainSumL2Budget C B H V (m + 3) ws := by
  induction ws with
  | nil =>
      change eLpNorm (0 : Coord → ℝ) 2 (volume.restrict V) ≤ 0
      simp
  | cons w ws ih =>
      have hw := hws w List.mem_cons_self
      have ht := coordinateChainTerm_eLpNorm_two hg hU hz hyy hV hVU hm hC hB
        hlow hheight hw (hcoeff w hw)
      have hs := ih (fun v hv => hws v (List.mem_cons_of_mem _ hv))
      change eLpNorm (fun p => coordinateChainTerm g z w p + coordinateChainSum g z ws p)
        2 (volume.restrict V) ≤
          chainWordL2Budget C B H V (m + 3) w + chainSumL2Budget C B H V (m + 3) ws
      exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
        (add_le_add ht hs)

theorem firstJetPairRemainder_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (n : ℕ) :
    ContinuousOn (firstJetPairRemainder g z n) U := by
  have h0 := (partial_contDiffOn (heightPFirst_contDiffOn hg hU hz hyy 0) hU 1).continuousOn
  have h1 := (partial_contDiffOn (heightPFirst_contDiffOn hg hU hz hyy 1) hU 1).continuousOn
  exact (h0.mul (heightStateFactor_contDiffOn hU hz n 0).continuousOn).add
    (h1.mul (heightStateFactor_contDiffOn hU hz n 1).continuousOn)

theorem coordinateChainSum_memLp_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hVfinite : volume V < (⊤ : ℝ≥0∞))
    {m : ℕ} (hm : 8 ≤ m + 3) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C) :
    MemLp (coordinateChainSum g z (topResidualWords m)) 2 (volume.restrict V) := by
  exact (coordinateChainSum_eLpNorm_two hg hU hz hyy hV hVU hm hC hB hlow hheight hcoeff
    (topResidualWords m) (fun _ hw => hw)).trans_lt
      (chainSumL2Budget_lt_top C B H hVfinite (m + 3) (topResidualWords m))

theorem firstJetPairRemainder_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} {Cfirst : ℝ} (hCfirst : 0 ≤ Cfirst) {H : ℝ≥0}
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hfirst : ∀ i : Fin 2, ∀ p ∈ V, |coordPartial 1 (heightPFirst g z i) p| ≤ Cfirst) :
    eLpNorm (firstJetPairRemainder g z (m + 2)) 2 (volume.restrict V) ≤
      firstJetPairL2Budget Cfirst H := by
  have h0 : eLpNorm (heightStateFactor z (m + 2) 0) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) :=
    hheight (m + 2) 0 (by norm_num [heightStateBaseOrder])
  have h1 : eLpNorm (heightStateFactor z (m + 2) 1) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) :=
    hheight (m + 2) 1 (by norm_num [heightStateBaseOrder])
  have hm (i : Fin 2) : AEStronglyMeasurable
      (fun p => coordPartial 1 (heightPFirst g z i) p * coordPartial i (verticalJet z (m + 2)) p)
      (volume.restrict V) :=
    (((partial_contDiffOn (heightPFirst_contDiffOn hg hU hz hyy i) hU 1).continuousOn.mul
      (partial_contDiffOn (verticalJet_contDiffOn hU hz (m + 2)) hU i).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hb0 := (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
    (f := heightStateFactor z (m + 2) 0) hV hCfirst (hfirst 0) (hm 0)).trans
    (mul_le_mul' le_rfl h0)
  have hb1 := (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
    (f := heightStateFactor z (m + 2) 1) hV hCfirst (hfirst 1) (hm 1)).trans
    (mul_le_mul' le_rfl h1)
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
    (add_le_add hb0 hb1)

theorem actualHighRemainder_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (m : ℕ) :
    ContinuousOn (actualHighRemainder g z m) U :=
  (coordinateChainSum_continuousOn hg hU hz hyy (topResidualWords m)).add
    (continuousOn_const.mul (firstJetPairRemainder_continuousOn hg hU hz hyy (m + 2)))

theorem actualHighRemainder_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} (hm : 8 ≤ m + 3) {C Cfirst B : ℝ}
    (hC : 0 ≤ C) (hCfirst : 0 ≤ Cfirst) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C)
    (hfirst : ∀ i : Fin 2, ∀ p ∈ V, |coordPartial 1 (heightPFirst g z i) p| ≤ Cfirst) :
    eLpNorm (actualHighRemainder g z m) 2 (volume.restrict V) ≤
      actualHighRemainderL2Budget C Cfirst B H V m := by
  have hs := coordinateChainSum_eLpNorm_two hg hU hz hyy hV hVU hm hC hB
    hlow hheight hcoeff (topResidualWords m) (fun _ hw => hw)
  have hp := firstJetPairRemainder_eLpNorm_two hg hU hz hyy hV hVU hCfirst hheight hfirst
  have hscaled : eLpNorm (fun p => (m + 3 : ℝ) * firstJetPairRemainder g z (m + 2) p)
      2 (volume.restrict V) ≤ ‖(m + 3 : ℝ)‖ₑ * firstJetPairL2Budget Cfirst H := by
    change eLpNorm ((m + 3 : ℝ) • firstJetPairRemainder g z (m + 2))
      2 (volume.restrict V) ≤ _
    rw [eLpNorm_const_smul (𝕜 := ℝ) (F := ℝ)]
    exact mul_le_mul' le_rfl hp
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add hs hscaled)

theorem actualHighRemainder_memLp_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hVfinite : volume V < (⊤ : ℝ≥0∞))
    {m : ℕ} (hm : 8 ≤ m + 3) {C Cfirst B : ℝ}
    (hC : 0 ≤ C) (hCfirst : 0 ≤ Cfirst) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C)
    (hfirst : ∀ i : Fin 2, ∀ p ∈ V, |coordPartial 1 (heightPFirst g z i) p| ≤ Cfirst) :
    MemLp (actualHighRemainder g z m) 2 (volume.restrict V) := by
  exact (actualHighRemainder_eLpNorm_two hg hU hz hyy hV hVU hm hC hCfirst hB
    hlow hheight hcoeff hfirst).trans_lt
      (actualHighRemainderL2Budget_lt_top C Cfirst B H hVfinite m)

end SmoothLocal.HighEquation

end

end OAI
