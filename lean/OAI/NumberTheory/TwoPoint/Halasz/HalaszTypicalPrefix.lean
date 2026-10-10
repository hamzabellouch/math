import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalScale
import OAI.NumberTheory.TwoPoint.Halasz.HalaszCenteredPrefix

namespace OAI

/-! Uniform centered typical prefixes. The distance and frequency range
are still imposed at the original cutoff, while the typical bands remain
fixed as the prefix varies. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem halasz_typical_centered_prefix : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ X : ℕ, X ≤ N^3 →
      ∀ F : ℕ → ℂ, F 1=1 →
      (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ t T M : ℝ, 0 ≤ M → |t|+Real.log (2*N:ℕ)^8 ≤ T →
      (∀ u : ℝ, |u| ≤ T → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      ∀ {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, ∀ p ∈ P j, p.Prime) → Set.PairwiseDisjoint (J : Set ι) P →
      (∀ j ∈ J, ∀ p ∈ P j, (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) 0 k‖  ≤
        C*(Real.exp (-2*M/5)+(Real.log N)^(-1/4:ℝ))*k := by
  obtain ⟨C₀,X₀,hC₀,hmean⟩ := halasz_typical_mean_value
  obtain ⟨K,hK,hcut⟩ := halasz_distance_cutoff_loss
  let C := C₀*(10*Real.exp (2*K/5)+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  obtain ⟨N₀,hscale⟩ := eventually_atTop.mp halasz_typical_cutoff_scale
  have hx : ∀ᶠ N : ℕ in atTop, X₀ ≤ (N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop X₀)
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop N₀,eventually_ge_atTop 2,hx,hl]
    with N hNN hN2 hXN hLN
  intro X hX F hF1 hFm hFb t T M _hM hT hdist ι J P hP hdis hupper k hk
  have hNk := (mem_Icc.mp hk).1
  have hk2 : 2 ≤ k := hN2.trans hNk
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hlogk : Real.log (N:ℝ) ≤ Real.log (k:ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (by exact_mod_cast hNk)
  have hlk : 0 < Real.log (k:ℝ) := by linarith
  obtain ⟨hR,hRlo,hRhi,herr⟩ := hscale k (hNN.trans hNk)
  let G := halaszTwistedFunction F t
  let M' := max 0 (M-K)
  have hPk : ∀ j ∈ J, P j ⊆ primesUpTo k := by
    intro j hj p hp
    have hu := (hupper j hj p hp).trans
      (Real.exp_le_exp.mpr (Real.sqrt_le_sqrt hlogk))
    have hpN : (p:ℝ) ≤ k := hu.trans (hRhi.trans (by linarith))
    exact mem_filter.mpr ⟨mem_range.mpr (by exact_mod_cast (show (p:ℝ) < (k:ℝ)+1 by linarith)),hP j hj p hp⟩
  have hd : ∀ u ∈ Set.Icc (-(Real.log (k:ℝ)^8)) (Real.log (k:ℝ)^8),
      M' ≤ squaredDistance G (mrtArchimedeanTwist u) k := by
    intro u hu
    rw [halasz_twisted_distance]
    apply max_le
    · exact halasz_distance_nonneg F hFb k (t+u)
    · have hloghi : Real.log (k:ℝ) ≤ Real.log (2*N:ℕ) :=
        Real.log_le_log hk0 (by exact_mod_cast (mem_Icc.mp hk).2)
      have hheight : |t+u| ≤ T := calc
        |t+u| ≤ |t|+|u| := abs_add_le _ _
        _  ≤  |t|+Real.log (k:ℝ)^8 := add_le_add le_rfl (abs_le.mpr hu)
        _  ≤  |t|+Real.log (2*N:ℕ)^8 := by gcongr
        _  ≤  T := hT
      have hb := hdist (t+u) hheight
      by_cases hkX : k ≤ X
      · have hc := hcut F hFb k X hk2 hkX (hX.trans (by gcongr)) (t+u)
        linarith
      · have hc := halasz_distance_monotone F hFb (t+u) (by omega : X ≤ k)
        linarith
  have hh := hmean k (hXN.trans (by exact_mod_cast hNk)) G
    (halasz_twisted_one F hF1 t) (halasz_twisted_mul F hFm t)
    (halasz_twisted_oneBounded F hFb t) J P hPk hdis
    (Real.exp (Real.sqrt (Real.log (k:ℝ)))) hR hRlo hRhi
    (fun j hj p hp => (hupper j hj p hp).trans
      (Real.exp_le_exp.mpr (Real.sqrt_le_sqrt hlogk))) M' (le_max_left _ _) hd
  have hdec : (M'+1)*Real.exp (-M'/2) ≤
      10*Real.exp (2*K/5)*Real.exp (-2*M/5) := by
    apply (halasz_typical_decay (le_max_left 0 (M-K))).trans
    calc
      10*Real.exp (-2*M'/5) ≤ 10*Real.exp (-2*(M-K)/5) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        have := le_max_right 0 (M-K)
        dsimp [M']
        linarith
      _ = _ := by
        rw [show -2*(M-K)/5 = 2*K/5 + (-2*M/5) by ring,Real.exp_add]
        ring
  have hpow : (Real.log (k:ℝ))^(-1/4:ℝ) ≤ (Real.log N)^(-1/4:ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hlogk (by norm_num)
  have hfinal : C₀*((M'+1)*Real.exp (-M'/2)+
      (1+Real.log (Real.exp (Real.sqrt (Real.log (k:ℝ)))))*Real.log (Real.log k)/Real.log k)  ≤
      C*(Real.exp (-2*M/5)+(Real.log N)^(-1/4:ℝ)) := by
    have he : 0 ≤ Real.exp (-2*M/5) := (Real.exp_pos _).le
    have hp : 0 ≤ (Real.log N)^(-1/4:ℝ) := Real.rpow_nonneg (by linarith) _
    have hc : 0 ≤ 10*Real.exp (2*K/5) := by positivity
    calc
      _ ≤ C₀*(10*Real.exp (2*K/5)*Real.exp (-2*M/5)+(Real.log N)^(-1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hdec (herr.trans hpow)) hC₀.le
      _ ≤ C₀*((10*Real.exp (2*K/5)+1)*(Real.exp (-2*M/5)+(Real.log N)^(-1/4:ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hC₀.le
        nlinarith [mul_nonneg hc hp]
      _ = _ := by dsimp [C]; ring
  have heq : halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient J P F) t) 0 k =
      ∑ n ∈ Icc 1 k, mrtTypicalCoefficient J P G n := by
    rw [halasz_typical_twist]
    simp [halaszPhaseMean,halaszPowerPhase]
  rw [heq]
  apply hh.trans
  calc
    _ = (C₀*((M'+1)*Real.exp (-M'/2)+
      (1+Real.log (Real.exp (Real.sqrt (Real.log (k:ℝ)))))*Real.log (Real.log k)/Real.log k))*k := by ring
    _  ≤  _ := mul_le_mul_of_nonneg_right hfinal hk0.le

end TwoPointCorrelations

end OAI
