import Mathlib
import OAI.Analysis.Conductivity.Flux.TwoFluxColumns

namespace OAI

noncomputable section

namespace ScalarConductivity

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
section

lemma fderiv_equiv_symm_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm) (x : E) :
    (fderiv ℝ X.symm (X x)).comp (fderiv ℝ X x) = ContinuousLinearMap.id ℝ E := by
  rw [← fderiv_comp x (hXi _) (hX _)]
  have hx : (X.symm ∘ X : E → E) = id := funext X.symm_apply_apply
  rw [hx, fderiv_id]

lemma fderiv_equiv_comp_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm) (x : E) :
    (fderiv ℝ X x).comp (fderiv ℝ X.symm (X x)) = ContinuousLinearMap.id ℝ E := by
  simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using
    fderiv_equiv_symm_comp X.symm hXi hX (X x)

def derivativeEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm) (x : E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse' (fderiv ℝ X x) (fderiv ℝ X.symm (X x))
    (fderiv_equiv_comp_symm X hX hXi x) (fderiv_equiv_symm_comp X hX hXi x)

lemma fderiv_equiv_det_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm) (x : E) :
    (fderiv ℝ X x).det ≠ 0 := by
  have hc := congrArg (fun L : E →L[ℝ] E => L.det) (fderiv_equiv_symm_comp X hX hXi x)
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.coe_id, LinearMap.det_comp, LinearMap.det_id] at hc
  exact right_ne_zero_of_mul_eq_one hc

lemma piolaFlux_derivative_pairing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm)
    (u : E → ℝ) (hu : Differentiable ℝ u) (F : E → E) (y : E) :
    fderiv ℝ (u ∘ X.symm) y (piolaFlux X F y) =
      |(fderiv ℝ X (X.symm y)).det|⁻¹ * fderiv ℝ u (X.symm y) (F (X.symm y)) := by
  rw [fderiv_comp y (hu _) (hXi _)]
  simp only [piolaFlux, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
  congr 1
  have hc := fderiv_equiv_symm_comp X hX hXi (X.symm y)
  rw [X.apply_symm_apply] at hc
  exact congrArg (fun L : E →L[ℝ] E => fderiv ℝ u (X.symm y) (L (F (X.symm y)))) hc

def smoothEquivHomeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm) : E ≃ₜ E :=
  { X with continuous_toFun := hX.continuous, continuous_invFun := hXi.continuous }

lemma piolaFlux_hasCompactSupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E ≃ E) (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm)
    (F : E → E) (hF : HasCompactSupport F) : HasCompactSupport (piolaFlux X F) := by
  apply (hF.comp_homeomorph (smoothEquivHomeomorph X hX hXi).symm).mono
  intro y hy
  contrapose! hy
  simp only [Function.mem_support, not_not] at hy ⊢
  change F (X.symm y) = 0 at hy
  simp only [piolaFlux, hy, map_zero, smul_zero]

lemma piolaFlux_zero_pairing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : E ≃ E) (hX : ContDiff ℝ (↑(⊤ : ℕ∞)) X)
    (hXi : ContDiff ℝ (↑(⊤ : ℕ∞)) X.symm) (F : E → E)
    (hF : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0)
    (ψ : E → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) :
    (∫ y, fderiv ℝ ψ y (piolaFlux X F y) ∂μ) = 0 := by
  rw [piolaFlux_pairing μ X (hX.differentiable (by simp))
    (fderiv_equiv_det_ne_zero X (hX.differentiable (by simp)) (hXi.differentiable (by simp)))
    F ψ (hψ.differentiable (by simp))]
  exact hF _ (hψ.comp hX)

lemma equiv_mapsTo_of_fixed_compl {E : Type*} (X : E ≃ E) (Q : Set E)
    (hX : ∀ x ∉ Q, X x = x) : Set.MapsTo X Q Q ∧ Set.MapsTo X.symm Q Q := by
  have hi : ∀ x ∉ Q, X.symm x = x := by
    intro x hx
    exact (X.symm_apply_eq).2 (hX x hx).symm
  constructor
  · intro x hx
    by_contra hn
    have he : X (X x) = X x := hX (X x) hn
    exact hn ((X.injective he).symm ▸ hx)
  · intro x hx
    by_contra hn
    have he : X.symm (X.symm x) = X.symm x := hi (X.symm x) hn
    exact hn ((X.symm.injective he).symm ▸ hx)

end

open Set MeasureTheory Filter Topology
open scoped BigOperators

def flatPulse (θ δ t : ℝ) : ℝ :=
  Real.smoothTransition (t / δ) - Real.smoothTransition ((t - θ) / δ)

lemma flatPulse_smooth (θ δ : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (flatPulse θ δ) := by
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)).sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ))

lemma flatPulse_zero_left {θ δ t : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) (ht : t ≤ 0) :
    flatPulse θ δ t = 0 := by
  rw [flatPulse, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht hδ.le),
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le), sub_self]

lemma flatPulse_zero_right {θ δ t : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) (ht : θ + δ ≤ t) :
    flatPulse θ δ t = 0 := by
  rw [flatPulse, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith)), sub_self]

lemma flatPulse_one {θ δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) (htθ : t ≤ θ) :
    flatPulse θ δ t = 1 := by
  rw [flatPulse, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith)),
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htθ) hδ.le), sub_zero]

lemma flatPulse_bounds {θ δ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ) (t : ℝ) :
    0 ≤ flatPulse θ δ t ∧ flatPulse θ δ t ≤ 1 := by
  by_cases ht : t ≤ θ
  · rw [flatPulse, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hδ.le), sub_zero]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · rw [flatPulse, Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hδ).2 (by linarith))]
    exact ⟨sub_nonneg.2 (Real.smoothTransition.le_one _),
      sub_le_self _ (Real.smoothTransition.nonneg _)⟩

lemma flatPulse_support {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    Function.support (flatPulse θ δ) ⊆ Ioo 0 (θ + δ) := by
  intro t ht
  constructor
  · by_contra hn
    exact ht (flatPulse_zero_left hθ hδ (not_lt.mp hn))
  · by_contra hn
    exact ht (flatPulse_zero_right hθ hδ (not_lt.mp hn))

def periodicPulse (θ δ t : ℝ) : ℝ := ∑ᶠ n : ℤ, flatPulse θ δ (t - n)

lemma pulse_translates_locallyFinite {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    LocallyFinite (fun n : ℤ => Function.support (fun t : ℝ => flatPulse θ δ (t - n))) := by
  have hl : Tendsto (fun n : ℤ => (n : ℝ)) atTop atTop := tendsto_intCast_atTop_atTop
  have hu : Tendsto (fun n : ℤ => (n : ℝ) + (θ + δ)) atBot atBot := by
    exact tendsto_atBot_add_const_right _ _ (tendsto_intCast_atBot_iff.2 tendsto_id)
  apply (locallyFinite_Icc_of_tendsto hl hu).subset
  intro n t ht
  have ht' := flatPulse_support hθ hδ ht
  exact ⟨by linarith [ht'.1], by linarith [ht'.2]⟩

lemma periodicPulse_smooth {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (periodicPulse θ δ) := by
  rw [← contMDiff_iff_contDiff]
  exact contMDiff_finsum (fun n =>
    (contMDiff_iff_contDiff).2 ((flatPulse_smooth θ δ).comp (contDiff_id.sub contDiff_const)))
      (pulse_translates_locallyFinite hθ hδ)

lemma periodicPulse_periodic (θ δ : ℝ) : Function.Periodic (periodicPulse θ δ) 1 := by
  intro t
  unfold periodicPulse
  calc
    _ = ∑ᶠ n : ℤ, flatPulse θ δ (t + 1 - (n + 1 : ℤ)) :=
      (finsum_comp_equiv (Equiv.addRight (1 : ℤ))).symm
    _ = _ := by congr 1; funext n; congr 1; push_cast; ring

lemma periodicPulse_eq {θ δ t : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hwidth : θ + δ ≤ 1) (ht : t ∈ Icc 0 1) : periodicPulse θ δ t = flatPulse θ δ t := by
  unfold periodicPulse
  have hz : ∀ n : ℤ, n ≠ 0 → flatPulse θ δ (t - n) = 0 := by
    intro n hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · apply flatPulse_zero_right hθ hδ
      have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      linarith [ht.1]
    · apply flatPulse_zero_left hθ hδ
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith [ht.2]
  simpa using finsum_eq_single _ 0 hz

lemma periodicPulse_bounds {θ δ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ)
    (hwidth : θ + δ ≤ 1) (t : ℝ) :
    0 ≤ periodicPulse θ δ t ∧ periodicPulse θ δ t ≤ 1 := by
  have ht : t - (⌊t⌋ : ℤ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Int.floor_le t)
    · linarith [Int.lt_floor_add_one t]
  have he : periodicPulse θ δ (t - (⌊t⌋ : ℤ)) = periodicPulse θ δ t := by
    simpa using (periodicPulse_periodic θ δ).sub_zsmul_eq (x := t) ⌊t⌋
  rw [← he, periodicPulse_eq (hδ.le.trans hδθ) hδ hwidth ht]
  exact flatPulse_bounds hδ hδθ _

lemma smoothStep_integral {δ a b : ℝ} (hδ : 0 < δ) (ha : a ≤ 0) (hb : δ ≤ b) :
    (∫ t in a..b, Real.smoothTransition (t / δ)) =
      (∫ t in (0 : ℝ)..δ, Real.smoothTransition (t / δ)) + (b - δ) := by
  have hs : Continuous (fun t : ℝ => Real.smoothTransition (t / δ)) := by fun_prop
  have hl : (∫ t in a..0, Real.smoothTransition (t / δ)) = 0 := by
    calc
      _ = ∫ _t in a..0, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le ha] at ht
        exact Real.smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg ht.2 hδ.le)
      _ = 0 := by simp
  have hr : (∫ t in δ..b, Real.smoothTransition (t / δ)) = b - δ := by
    calc
      _ = ∫ _t in δ..b, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply Real.smoothTransition.one_of_one_le
        apply (le_div_iff₀ hδ).2
        rw [uIcc_of_le hb] at ht
        simpa only [one_mul] using ht.1
      _ = _ := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hs.intervalIntegrable a 0)
    (hs.intervalIntegrable 0 b),
    ← intervalIntegral.integral_add_adjacent_intervals (hs.intervalIntegrable 0 δ)
    (hs.intervalIntegrable δ b), hl, hr, zero_add]

lemma flatPulse_integral {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hwidth : θ + δ ≤ 1) : (∫ t in (0 : ℝ)..1, flatPulse θ δ t) = θ := by
  have hs : Continuous (fun t : ℝ => Real.smoothTransition (t / δ)) := by fun_prop
  have hs' : Continuous (fun t : ℝ => Real.smoothTransition ((t - θ) / δ)) := by fun_prop
  simp only [flatPulse]
  rw [intervalIntegral.integral_sub (hs.intervalIntegrable _ _)
    (hs'.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => Real.smoothTransition (t / δ)) θ]
  rw [smoothStep_integral (δ := δ) (a := 0) (b := 1) hδ le_rfl (by linarith),
    smoothStep_integral (δ := δ) (a := 0 - θ) (b := 1 - θ) hδ (by linarith) (by linarith)]
  ring

lemma periodicPulse_integral {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hwidth : θ + δ ≤ 1) : (∫ t in (0 : ℝ)..1, periodicPulse θ δ t) = θ := by
  convert flatPulse_integral hθ hδ hwidth using 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact periodicPulse_eq hθ hδ hwidth (by simpa using ht)

theorem exists_two_state_wave {θ δ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ)
    (hwidth : θ + δ ≤ 1) :
    ∃ h : ℝ → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) h ∧ Function.Periodic h 1 ∧
      (∫ t in (0 : ℝ)..1, h t) = 0 ∧
      (∀ t, -θ ≤ h t ∧ h t ≤ 1 - θ) ∧
      (∀ t ∈ Icc 0 1, h t ≠ -θ → h t ≠ 1 - θ →
        t ∈ Ioo 0 δ ∪ Ioo θ (θ + δ)) := by
  have hθ : 0 ≤ θ := hδ.le.trans hδθ
  refine ⟨fun t => periodicPulse θ δ t - θ,
    (periodicPulse_smooth hθ hδ).sub contDiff_const, ?_, ?_, ?_, ?_⟩
  · intro t
    change periodicPulse θ δ (t + 1) - θ = periodicPulse θ δ t - θ
    rw [show periodicPulse θ δ (t + 1) = periodicPulse θ δ t from periodicPulse_periodic θ δ t]
  · rw [intervalIntegral.integral_sub ((periodicPulse_smooth hθ hδ).continuous.intervalIntegrable _ _)
      intervalIntegrable_const, periodicPulse_integral hθ hδ hwidth]
    simp
  · intro t
    obtain ⟨hl, hu⟩ := periodicPulse_bounds hδ hδθ hwidth t
    constructor <;> linarith
  · intro t ht hl hu
    change periodicPulse θ δ t - θ ≠ -θ at hl
    change periodicPulse θ δ t - θ ≠ 1 - θ at hu
    rw [periodicPulse_eq hθ hδ hwidth ht] at hl hu
    by_cases htd : t < δ
    · left
      refine ⟨?_, htd⟩
      by_contra hn
      exact hl (by rw [flatPulse_zero_left hθ hδ (not_lt.mp hn)]; ring)
    · right
      refine ⟨?_, ?_⟩
      · by_contra hn
        exact hu (by rw [flatPulse_one hδ (not_lt.mp htd) (not_lt.mp hn)])
      · by_contra hn
        exact hl (by rw [flatPulse_zero_right hθ hδ (not_lt.mp hn)]; ring)

end ScalarConductivity

end

end OAI
