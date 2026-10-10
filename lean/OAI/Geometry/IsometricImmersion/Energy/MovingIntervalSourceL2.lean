import OAI.Geometry.IsometricImmersion.Energy.MovingIntervalSobolev
import OAI.Geometry.IsometricImmersion.Energy.FiniteSumL2

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Analytic

def spatialProduct {ι : Type*} {n : ℕ} (F : ι → Coord → ℝ)
    (slot : Fin n → ι) (order : Fin n → ℕ) (p : Coord) : ℝ :=
  ∏ i, spatialJet (F (slot i)) (order i) p

def spatialSourceTerm {ι : Type*} {n : ℕ} (coeff : Coord → ℝ) (F : ι → Coord → ℝ)
    (slot : Fin n → ι) (order : Fin n → ℕ) (p : Coord) : ℝ :=
  coeff p * spatialProduct F slot order p

def spatialLowFactorBound (lengthFloor : ℝ) (H : ℝ≥0) : ℝ :=
  max 1 (Real.sqrt (2 + 1 / lengthFloor) * (H : ℝ))

def spatialProductL2Budget (lengthFloor left right : ℝ) (H : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ‖spatialLowFactorBound lengthFloor H ^ n‖ₑ *
    ((H : ℝ≥0∞) + (volume (Icc left right)) ^ (1 / (2 : ℝ)))

theorem spatialProductL2Budget_lt_top (lengthFloor left right : ℝ) (H : ℝ≥0) (n : ℕ) :
    spatialProductL2Budget lengthFloor left right H n < (⊤ : ℝ≥0∞) := by
  unfold spatialProductL2Budget
  rw [Real.volume_Icc]
  finiteness

theorem spatialProduct_contDiffOn
    {ι : Type*} {n : ℕ} {F : ι → Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) U)
    (slot : Fin n → ι) (order : Fin n → ℕ) :
    ContDiffOn ℝ ∞ (spatialProduct F slot order) U := by
  apply contDiffOn_prod
  intro index _
  exact spatialJet_contDiffOn hU (hF (slot index)) (order index)

theorem spatialProduct_eLpNorm_two
    {ι : Type*} {n N : ℕ} {F : ι → Coord → ℝ} {U : Set Coord}
    {theta left right lengthFloor : ℝ} {H : ℝ≥0}
    (hU : IsOpen U) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hL2 : SpatialSliceL2Bound F theta left right N H)
    (slot : Fin n → ι) (order : Fin n → ℕ)
    (horder : ∀ i, order i ≤ N)
    (hunique : ∀ i j, order i = N → order j = N → i = j) :
    eLpNorm (fun x => spatialProduct F slot order (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ spatialProductL2Budget lengthFloor left right H n := by
  classical
  have hmeas := (smooth_slice_memLp_two
    (spatialProduct_contDiffOn hU hF slot order).continuousOn hseg).aestronglyMeasurable
  let B := spatialLowFactorBound lengthFloor H
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hlow (i : Fin n) (hi : order i + 1 ≤ N) (x : ℝ) (hx : x ∈ Icc left right) :
      ‖spatialJet (F (slot i)) (order i) (coordinatePoint x theta)‖ ≤ B := by
    rw [Real.norm_eq_abs]
    exact (hL2.pointwise_below_top hU hF hseg hlength hwidth (slot i) (order i) hi hx).trans
      (le_max_right _ _)
  by_cases hh : ∃ j, order j = N
  · obtain ⟨j, hj⟩ := hh
    have hb (i : Fin n) (hi : i ∈ (Finset.univ : Finset (Fin n)).erase j)
        (x : ℝ) (hx : x ∈ Icc left right) :
        ‖spatialJet (F (slot i)) (order i) (coordinatePoint x theta)‖ ≤ B := by
      apply hlow i _ x hx
      have hi_ne : i ≠ j := (Finset.mem_erase.mp hi).1
      have hnot : order i ≠ N := fun hie => hi_ne (hunique i j hie hj)
      have hoi := horder i
      omega
    have hprod := finite_product_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (fun i x => spatialJet (F (slot i)) (order i) (coordinatePoint x theta))
      (Finset.mem_univ j) hB0 measurableSet_Icc hb hmeas
    have hcard : ((Finset.univ : Finset (Fin n)).erase j).card ≤ n := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.erase_subset j (Finset.univ : Finset (Fin n)))
    have hpow : ‖B ^ ((Finset.univ : Finset (Fin n)).erase j).card‖ₑ ≤ ‖B ^ n‖ₑ := by
      rw [enorm_le_iff_norm_le, Real.norm_of_nonneg (pow_nonneg hB0 _),
        Real.norm_of_nonneg (pow_nonneg hB0 _)]
      exact pow_le_pow_right₀ hB1 hcard
    calc
      _ ≤ ‖B ^ ((Finset.univ : Finset (Fin n)).erase j).card‖ₑ *
          eLpNorm (fun x => spatialJet (F (slot j)) (order j) (coordinatePoint x theta)) 2
            (volume.restrict (Icc left right)) := hprod
      _ ≤ ‖B ^ n‖ₑ * (H : ℝ≥0∞) := mul_le_mul' hpow (hL2 (slot j) (order j) (horder j))
      _ ≤ _ := mul_le_mul' le_rfl (le_add_of_nonneg_right (by positivity))
  · have hb (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n)))
        (x : ℝ) (hx : x ∈ Icc left right) :
        ‖spatialJet (F (slot i)) (order i) (coordinatePoint x theta)‖ ≤ B := by
      apply hlow i _ x hx
      have hnot : order i ≠ N := fun hie => hh ⟨i, hie⟩
      have hoi := horder i
      omega
    have hprod := finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable
      (μ := volume) Finset.univ
      (fun i x => spatialJet (F (slot i)) (order i) (coordinatePoint x theta))
      hB0 measurableSet_Icc hb hmeas
    calc
      _ ≤ ‖B ^ n‖ₑ * (volume (Icc left right)) ^ (1 / (2 : ℝ)) := by
        simpa only [spatialProduct, Finset.card_univ, Fintype.card_fin] using hprod
      _ ≤ _ := mul_le_mul' le_rfl (le_add_of_nonneg_left (by positivity))

theorem real_interval_coefficient_eLpNorm_two
    {a f : ℝ → ℝ} {left right C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ x ∈ Icc left right, |a x| ≤ C) :
    eLpNorm' (fun x => a x * f x) (2 : ℝ) (volume.restrict (Icc left right)) ≤
      ‖C‖ₑ * eLpNorm' f (2 : ℝ) (volume.restrict (Icc left right)) := by
  have hdom : ∀ᵐ x ∂volume.restrict (Icc left right), ‖a x * f x‖ ≤ ‖C * f x‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (ha x hx) (abs_nonneg _)
  calc
    _ ≤ eLpNorm' (fun x => C * f x) (2 : ℝ) (volume.restrict (Icc left right)) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := eLpNorm'_const_smul (𝕜 := ℝ) (F := ℝ) (f := f) C (by norm_num)

theorem real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable
    {coefficient factor : ℝ → ℝ} {left right bound : ℝ} (hbound : 0 ≤ bound)
    (hcoefficient : ∀ point ∈ Icc left right, |coefficient point| ≤ bound)
    (hmeas : AEStronglyMeasurable (fun point => coefficient point * factor point)
      (volume.restrict (Icc left right))) :
    eLpNorm (fun point => coefficient point * factor point) 2
      (volume.restrict (Icc left right)) ≤
      ‖bound‖ₑ * eLpNorm factor 2 (volume.restrict (Icc left right)) := by
  have hfactor : eLpNorm' factor (2 : ℝ) (volume.restrict (Icc left right)) ≤
      eLpNorm factor 2 (volume.restrict (Icc left right)) := by
    by_cases hfactorMeas : AEStronglyMeasurable factor (volume.restrict (Icc left right))
    · rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hfactorMeas]
      norm_num
    · rw [eLpNorm_of_not_aestronglyMeasurable hfactorMeas]
      exact le_top
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmeas, ENNReal.toReal_ofNat]
  exact (real_interval_coefficient_eLpNorm_two hbound hcoefficient).trans
    (mul_le_mul_right hfactor _)

theorem spatialSourceTerm_memLp_two
    {ι : Type*} {n : ℕ} {F : ι → Coord → ℝ} {coeff : Coord → ℝ} {U : Set Coord}
    {theta left right : ℝ}
    (hU : IsOpen U) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) U)
    (hc : ContDiffOn ℝ ∞ coeff U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (slot : Fin n → ι) (order : Fin n → ℕ) :
    MemLp (fun x => spatialSourceTerm coeff F slot order (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) :=
  smooth_slice_memLp_two (hc.mul (spatialProduct_contDiffOn hU hF slot order)).continuousOn hseg

theorem spatialSourceTerm_eLpNorm_two
    {ι : Type*} {n N : ℕ} {F : ι → Coord → ℝ} {coeff : Coord → ℝ} {U : Set Coord}
    {theta left right lengthFloor C : ℝ} {H : ℝ≥0}
    (hU : IsOpen U) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hL2 : SpatialSliceL2Bound F theta left right N H) (hC : 0 ≤ C)
    (hc : ∀ x ∈ Icc left right, |coeff (coordinatePoint x theta)| ≤ C)
    (slot : Fin n → ι) (order : Fin n → ℕ)
    (horder : ∀ i, order i ≤ N)
    (hunique : ∀ i j, order i = N → order j = N → i = j) :
    eLpNorm' (fun x => spatialSourceTerm coeff F slot order (coordinatePoint x theta)) (2 : ℝ)
      (volume.restrict (Icc left right)) ≤
      ‖C‖ₑ * spatialProductL2Budget lengthFloor left right H n := by
  have hproduct := spatialProduct_eLpNorm_two hU hF hseg hlength hwidth hL2
    slot order horder hunique
  have hmeas := (smooth_slice_memLp_two
    (spatialProduct_contDiffOn hU hF slot order).continuousOn hseg).aestronglyMeasurable
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmeas,
    ENNReal.toReal_ofNat] at hproduct
  exact (real_interval_coefficient_eLpNorm_two hC hc).trans
    (mul_le_mul' le_rfl hproduct)

theorem spatialSourceTerm_eLpNorm_two_of_aestronglyMeasurable
    {ι : Type*} {n N : ℕ} {F : ι → Coord → ℝ} {coeff : Coord → ℝ} {U : Set Coord}
    {theta left right lengthFloor C : ℝ} {H : ℝ≥0}
    (hU : IsOpen U) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hL2 : SpatialSliceL2Bound F theta left right N H) (hC : 0 ≤ C)
    (hc : ∀ x ∈ Icc left right, |coeff (coordinatePoint x theta)| ≤ C)
    (slot : Fin n → ι) (order : Fin n → ℕ)
    (horder : ∀ i, order i ≤ N)
    (hunique : ∀ i j, order i = N → order j = N → i = j)
    (hmeas : AEStronglyMeasurable
      (fun x => spatialSourceTerm coeff F slot order (coordinatePoint x theta))
      (volume.restrict (Icc left right))) :
    eLpNorm (fun x => spatialSourceTerm coeff F slot order (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤
      ‖C‖ₑ * spatialProductL2Budget lengthFloor left right H n := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmeas, ENNReal.toReal_ofNat]
  exact spatialSourceTerm_eLpNorm_two hU hF hseg hlength hwidth hL2 hC hc
    slot order horder hunique

def spatialSourceSum {ι : Type*} {m : ℕ} (arity : Fin m → ℕ)
    (coeff : Fin m → Coord → ℝ) (F : ι → Coord → ℝ)
    (slot : (k : Fin m) → Fin (arity k) → ι)
    (order : (k : Fin m) → Fin (arity k) → ℕ) (p : Coord) : ℝ :=
  ∑ k, spatialSourceTerm (coeff k) F (slot k) (order k) p

theorem spatialSourceSum_eLpNorm_two
    {ι : Type*} {m N : ℕ} {F : ι → Coord → ℝ} {coeff : Fin m → Coord → ℝ} {U : Set Coord}
    {theta left right lengthFloor : ℝ} {H : ℝ≥0}
    (hU : IsOpen U) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) U)
    (hcSmooth : ∀ k, ContDiffOn ℝ ∞ (coeff k) U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hL2 : SpatialSliceL2Bound F theta left right N H) (C : Fin m → ℝ)
    (hC : ∀ k, 0 ≤ C k)
    (hc : ∀ k x, x ∈ Icc left right → |coeff k (coordinatePoint x theta)| ≤ C k)
    (arity : Fin m → ℕ) (slot : (k : Fin m) → Fin (arity k) → ι)
    (order : (k : Fin m) → Fin (arity k) → ℕ)
    (horder : ∀ k i, order k i ≤ N)
    (hunique : ∀ k i j, order k i = N → order k j = N → i = j) :
    eLpNorm (fun x => spatialSourceSum arity coeff F slot order (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤
      ∑ k, ‖C k‖ₑ * spatialProductL2Budget lengthFloor left right H (arity k) := by
  exact finite_sum_eLpNorm_two (μ := volume) (U := Icc left right) Finset.univ
    (fun k x => spatialSourceTerm (coeff k) F (slot k) (order k) (coordinatePoint x theta))
    (fun k => ‖C k‖ₑ * spatialProductL2Budget lengthFloor left right H (arity k))
    (fun k _ => (spatialSourceTerm_memLp_two hU hF (hcSmooth k) hseg
      (slot k) (order k)).aestronglyMeasurable)
    (fun k _ => spatialSourceTerm_eLpNorm_two_of_aestronglyMeasurable
      hU hF hseg hlength hwidth hL2 (hC k)
      (hc k) (slot k) (order k) (horder k) (hunique k)
      (spatialSourceTerm_memLp_two hU hF (hcSmooth k) hseg
        (slot k) (order k)).aestronglyMeasurable)

end SmoothLocal.Hyperbolic

end

end OAI
