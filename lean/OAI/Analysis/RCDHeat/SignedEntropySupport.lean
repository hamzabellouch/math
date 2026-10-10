import Mathlib
import OAI.Analysis.RCDHeat.VolumeComparison

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: SignedEntropySupport. -/



open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace RegularPointCoordinates

 theorem sinh_le_mul_cosh_real {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x*Real.cosh x := by
  let F : ℝ → ℝ := fun u => u*Real.cosh u-Real.sinh u
  have hD : ∀ u : ℝ, HasDerivAt F (u*Real.sinh u) u := by
    intro u
    convert ((hasDerivAt_id u).mul (Real.hasDerivAt_cosh u)).sub
      (Real.hasDerivAt_sinh u) using 1 <;> first | rfl | (dsimp; ring)
  have hm : MonotoneOn F (Ici (0:ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
      (show ContinuousOn F (Ici (0:ℝ)) by dsimp [F]; fun_prop)
      (fun u _ => (hD u).hasDerivWithinAt)
    intro u hu
    have hu0 : 0 ≤ u := (interior_subset hu)
    exact mul_nonneg hu0 (Real.sinh_nonneg_iff.mpr hu0)
  have hh := hm (show (0:ℝ) ∈ Ici (0:ℝ) by simp) hx hx
  dsimp [F] at hh
  simp only [zero_mul, Real.sinh_zero, sub_zero] at hh
  linarith

 

theorem sinh_gaussian_derivative_sign {x : ℝ} (hx : 0 ≤ x) :
    x*Real.cosh x ≤ (1+x^2/3)*Real.sinh x := by
  let F : ℝ → ℝ := fun u => (1+u^2/3)*Real.sinh u-u*Real.cosh u
  have hD : ∀ u : ℝ, HasDerivAt F (u/3*(u*Real.cosh u-Real.sinh u)) u := by
    intro u
    convert ((((hasDerivAt_id u).pow 2).div_const 3).const_add 1 |>.mul
      (Real.hasDerivAt_sinh u)).sub
      ((hasDerivAt_id u).mul (Real.hasDerivAt_cosh u)) using 1 <;>
      first | rfl | (dsimp; ring)
  have hm : MonotoneOn F (Ici (0:ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
      (show ContinuousOn F (Ici (0:ℝ)) by dsimp [F]; fun_prop)
      (fun u _ => (hD u).hasDerivWithinAt)
    intro u hu
    have hu0 : 0 ≤ u := (interior_subset hu)
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (sinh_le_mul_cosh_real hu0))
  have hh := hm (show (0:ℝ) ∈ Ici (0:ℝ) by simp) hx hx
  dsimp [F] at hh
  simpa using hh

noncomputable def sharpSinhRatio (x : ℝ) : ℝ := Real.sinh x*Real.exp (-(x^2)/6)/x

 theorem sharpSinhRatio_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt sharpSinhRatio
      (Real.exp (-(x^2)/6)/x^2 * (x*Real.cosh x-(1+x^2/3)*Real.sinh x)) x := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (-(u^2)/6))
      (Real.exp (-(x^2)/6)*(-x/3)) x := by
    convert (((hasDerivAt_id x).pow 2).neg.div_const 6).exp using 1 <;> first | rfl | (dsimp; ring)
  change HasDerivAt (fun u : ℝ => Real.sinh u*Real.exp (-(u^2)/6)/u) _ x
  convert ((Real.hasDerivAt_sinh x).mul he).div (hasDerivAt_id x) hx.ne' using 1 <;>
    first | rfl | (dsimp; field_simp; ring)

 theorem sharpSinhRatio_antitone : AntitoneOn sharpSinhRatio (Ioi (0:ℝ)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi (0:ℝ))
  · intro x hx
    exact (sharpSinhRatio_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (sharpSinhRatio_hasDerivAt (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have hx0 : 0 < x := interior_subset hx
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.mpr (sinh_gaussian_derivative_sign hx0.le))

 theorem sinh_mul_sharp_gaussian_lower {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t*Real.exp (((t*a)^2-a^2)/6) ≤ Real.sinh (t*a)/Real.sinh a := by
  rcases eq_or_lt_of_le ht with h | htpos
  · subst t
    simp
  have hta : 0 < t*a := mul_pos htpos ha
  have hta_a : t*a ≤ a := by nlinarith
  have hh := sharpSinhRatio_antitone hta ha hta_a
  dsimp [sharpSinhRatio] at hh
  have hsinha : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hhe := (div_le_div_iff₀ ha hta).mp hh
  have he : Real.exp (((t*a)^2-a^2)/6) =
      Real.exp (-(a^2)/6)/Real.exp (-((t*a)^2)/6) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he]
  apply (le_div_iff₀ hsinha).mpr
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (-((t*a)^2)/6))).mp
  field_simp
  apply (mul_le_mul_iff_left₀ ha).mp
  convert hhe using 1 <;> ring_nf

 
theorem sigma_gaussian_lower (K N θ t : ℝ) (hN : 1 < N)
    (hθ : 0 ≤ θ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal (t*Real.exp (-|K| *θ^2*(1-t^2)/(6*(N-1)))) ≤ sigma K N t θ := by
  have hNm : 0 < N-1 := sub_pos.mpr hN
  have hexp : -|K| *θ^2*(1-t^2)/(6*(N-1)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have ht2 : 0 ≤ 1-t^2 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _)) (sq_nonneg _)) ht2
  have hlin : t*Real.exp (-|K| *θ^2*(1-t^2)/(6*(N-1))) ≤ t := by
    calc
      _ ≤ t*1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hexp) ht
      _ = t := mul_one _
  unfold sigma
  split_ifs with hz hconj hK
  · exact ENNReal.ofReal_le_ofReal hlin
  · exact le_top
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm (not_or.mp hz).1)
    have hroot : 0 < Real.sqrt (K/(N-1)) := Real.sqrt_pos.mpr (div_pos hK hNm)
    have ha0 : 0 < θ*Real.sqrt (K/(N-1)) := mul_pos hθpos hroot
    have hasq : (θ*Real.sqrt (K/(N-1)))^2 = K*θ^2/(N-1) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hK.le hNm.le)]
      ring
    have hasq_lt : (θ*Real.sqrt (K/(N-1)))^2 < Real.pi^2 := by
      rw [hasq, div_lt_iff₀ hNm]
      nlinarith [lt_of_not_ge hconj]
    have haπ : θ*Real.sqrt (K/(N-1)) < Real.pi := by nlinarith [Real.pi_pos]
    apply ENNReal.ofReal_le_ofReal
    exact hlin.trans (by simpa only [mul_assoc] using sin_mul_div_sin_ge ha0 haπ ht ht1)
  · have hKneg : K < 0 := lt_of_le_of_ne (le_of_not_gt hK) (not_or.mp hz).2
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm (not_or.mp hz).1)
    have hroot : 0 < Real.sqrt (-K/(N-1)) := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) hNm)
    apply ENNReal.ofReal_le_ofReal
    have hh := sinh_mul_sharp_gaussian_lower (mul_pos hθpos hroot) ht ht1
    have he : ((t*(θ*Real.sqrt (-K/(N-1))))^2-(θ*Real.sqrt (-K/(N-1)))^2)/6 =
        -|K| *θ^2*(1-t^2)/(6*(N-1)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg (neg_nonneg.mpr hKneg.le) hNm.le),
        abs_of_neg hKneg]
      field_simp
      ring
    simpa only [he, mul_assoc] using hh

 

theorem tau_gaussian_lower (K N θ t : ℝ) (hN : 1 < N)
    (hθ : 0 ≤ θ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal (t*Real.exp (-|K| *θ^2*(1-t^2)/(6*N))) ≤ tau K N t θ := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hNm : N-1 ≠ 0 := (sub_pos.mpr hN).ne'
  have hβ : 0 ≤ 1-1/N := by
    have := (div_le_one hN0).mpr hN.le
    linarith
  unfold tau
  split_ifs with ht0 htone
  · simp [ht0]
  · simp [htone]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hbound := mul_le_mul' (le_refl ((ENNReal.ofReal t)^(1/N)))
      (ENNReal.rpow_le_rpow (sigma_gaussian_lower K N θ t hN hθ ht ht1) hβ)
    refine le_trans (le_of_eq ?_) hbound
    rw [ENNReal.ofReal_rpow_of_pos htpos,
      ENNReal.ofReal_rpow_of_pos (mul_pos htpos (Real.exp_pos _)),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht _)]
    congr 1
    rw [Real.mul_rpow ht (Real.exp_pos _).le, ← mul_assoc,
      ← Real.rpow_add htpos, show 1/N+(1-1/N) = (1:ℝ) by ring,
      Real.rpow_one, ← Real.exp_mul]
    congr 2
    field_simp

 
theorem mul_cos_le_sin_real {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    x*Real.cos x ≤ Real.sin x := by
  let F : ℝ → ℝ := fun u => Real.sin u-u*Real.cos u
  have hD : ∀ u : ℝ, HasDerivAt F (u*Real.sin u) u := by
    intro u
    convert (Real.hasDerivAt_sin u).sub ((hasDerivAt_id u).mul
      (Real.hasDerivAt_cos u)) using 1 <;> first | rfl | (dsimp; ring)
  have hm : MonotoneOn F (Icc (0:ℝ) Real.pi) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) Real.pi)
      (show ContinuousOn F (Icc (0:ℝ) Real.pi) by dsimp [F]; fun_prop)
      (fun u _ => (hD u).hasDerivWithinAt)
    intro u hu
    have hu' : u ∈ Icc (0:ℝ) Real.pi := interior_subset hu
    exact mul_nonneg hu'.1 (Real.sin_nonneg_of_nonneg_of_le_pi hu'.1 hu'.2)
  have hh := hm (show (0:ℝ) ∈ Icc (0:ℝ) Real.pi by simp [Real.pi_pos.le]) ⟨hx,hxπ⟩ hx
  dsimp [F] at hh
  simp only [Real.sin_zero, zero_mul, sub_self] at hh
  linarith

 theorem sin_gaussian_derivative_sign {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    x*Real.cos x ≤ (1-x^2/3)*Real.sin x := by
  let F : ℝ → ℝ := fun u => (1-u^2/3)*Real.sin u-u*Real.cos u
  have hD : ∀ u : ℝ, HasDerivAt F (u/3*(Real.sin u-u*Real.cos u)) u := by
    intro u
    convert ((((hasDerivAt_id u).pow 2).div_const 3).const_sub 1 |>.mul
      (Real.hasDerivAt_sin u)).sub
      ((hasDerivAt_id u).mul (Real.hasDerivAt_cos u)) using 1 <;>
      first | rfl | (dsimp; ring)
  have hm : MonotoneOn F (Icc (0:ℝ) Real.pi) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) Real.pi)
      (show ContinuousOn F (Icc (0:ℝ) Real.pi) by dsimp [F]; fun_prop)
      (fun u _ => (hD u).hasDerivWithinAt)
    intro u hu
    have hu' : u ∈ Icc (0:ℝ) Real.pi := interior_subset hu
    exact mul_nonneg (div_nonneg hu'.1 (by norm_num))
      (sub_nonneg.mpr (mul_cos_le_sin_real hu'.1 hu'.2))
  have hh := hm (show (0:ℝ) ∈ Icc (0:ℝ) Real.pi by simp [Real.pi_pos.le]) ⟨hx,hxπ⟩ hx
  dsimp [F] at hh
  simpa using hh

noncomputable def sharpSinRatio (x : ℝ) : ℝ := Real.sin x*Real.exp (x^2/6)/x

 theorem sharpSinRatio_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt sharpSinRatio
      (Real.exp (x^2/6)/x^2 * (x*Real.cos x-(1-x^2/3)*Real.sin x)) x := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (u^2/6))
      (Real.exp (x^2/6)*(x/3)) x := by
    convert (((hasDerivAt_id x).pow 2).div_const 6).exp using 1 <;> first | rfl | (dsimp; ring)
  change HasDerivAt (fun u : ℝ => Real.sin u*Real.exp (u^2/6)/u) _ x
  convert ((Real.hasDerivAt_sin x).mul he).div (hasDerivAt_id x) hx.ne' using 1 <;>
    first | rfl | (dsimp; field_simp; ring)

 theorem sharpSinRatio_antitone : AntitoneOn sharpSinRatio (Ioo (0:ℝ) Real.pi) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo (0:ℝ) Real.pi)
  · intro x hx
    exact (sharpSinRatio_hasDerivAt hx.1).continuousAt.continuousWithinAt
  · intro x hx
    exact (sharpSinRatio_hasDerivAt (interior_subset hx).1).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Ioo (0:ℝ) Real.pi := interior_subset hx
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.mpr (sin_gaussian_derivative_sign hx'.1.le hx'.2.le))

 theorem sin_mul_sharp_gaussian_lower {a t : ℝ} (ha : 0 < a) (haπ : a < Real.pi)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t*Real.exp ((a^2-(t*a)^2)/6) ≤ Real.sin (t*a)/Real.sin a := by
  rcases eq_or_lt_of_le ht with h | htpos
  · subst t
    simp
  have hta : 0 < t*a := mul_pos htpos ha
  have hta_a : t*a ≤ a := by nlinarith
  have hh := sharpSinRatio_antitone ⟨hta,lt_of_le_of_lt hta_a haπ⟩ ⟨ha,haπ⟩ hta_a
  dsimp [sharpSinRatio] at hh
  have hsina : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha haπ
  have hhe := (div_le_div_iff₀ ha hta).mp hh
  have he : Real.exp ((a^2-(t*a)^2)/6) =
      Real.exp (a^2/6)/Real.exp ((t*a)^2/6) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he]
  apply (le_div_iff₀ hsina).mpr
  apply (mul_le_mul_iff_left₀ (Real.exp_pos ((t*a)^2/6))).mp
  field_simp
  apply (mul_le_mul_iff_left₀ ha).mp
  convert hhe using 1 <;> ring_nf

 
theorem sigma_signed_gaussian_lower (K N θ t : ℝ) (hN : 1 < N)
    (hθ : 0 ≤ θ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal (t*Real.exp (K*θ^2*(1-t^2)/(6*(N-1)))) ≤ sigma K N t θ := by
  by_cases hK : 0 < K
  · have hNm : 0 < N-1 := sub_pos.mpr hN
    unfold sigma
    split_ifs with hz hconj
    · rcases hz with hz | hz <;> simp [hz]
    · exact le_top
    · have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm (not_or.mp hz).1)
      have hroot : 0 < Real.sqrt (K/(N-1)) := Real.sqrt_pos.mpr (div_pos hK hNm)
      have ha0 : 0 < θ*Real.sqrt (K/(N-1)) := mul_pos hθpos hroot
      have hasq : (θ*Real.sqrt (K/(N-1)))^2 = K*θ^2/(N-1) := by
        rw [mul_pow, Real.sq_sqrt (div_nonneg hK.le hNm.le)]
        ring
      have hasq_lt : (θ*Real.sqrt (K/(N-1)))^2 < Real.pi^2 := by
        rw [hasq, div_lt_iff₀ hNm]
        nlinarith [lt_of_not_ge hconj]
      have haπ : θ*Real.sqrt (K/(N-1)) < Real.pi := by nlinarith [Real.pi_pos]
      apply ENNReal.ofReal_le_ofReal
      have hh := sin_mul_sharp_gaussian_lower ha0 haπ ht ht1
      have he : ((θ*Real.sqrt (K/(N-1)))^2-(t*(θ*Real.sqrt (K/(N-1))))^2)/6 =
          K*θ^2*(1-t^2)/(6*(N-1)) := by
        rw [mul_pow t, hasq]
        field_simp
      simpa only [he, mul_assoc, ite_eq_left hK] using hh
  · have habs : -|K| = K := by rw [abs_of_nonpos (le_of_not_gt hK), neg_neg]
    simpa only [habs] using sigma_gaussian_lower K N θ t hN hθ ht ht1

theorem tau_signed_gaussian_lower (K N θ t : ℝ) (hN : 1 < N)
    (hθ : 0 ≤ θ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal (t*Real.exp (K*θ^2*(1-t^2)/(6*N))) ≤ tau K N t θ := by
  have hNpos : 0 < N := lt_trans zero_lt_one hN
  have hNm : N-1 ≠ 0 := (sub_pos.mpr hN).ne'
  have hβ : 0 ≤ 1-1/N := by rw [sub_nonneg]; exact (div_le_one hNpos).mpr hN.le
  unfold tau
  split_ifs with ht0 htone
  · simp [ht0]
  · simp [htone]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hbound := mul_le_mul' (le_refl ((ENNReal.ofReal t)^(1/N)))
      (ENNReal.rpow_le_rpow (sigma_signed_gaussian_lower K N θ t hN hθ ht ht1) hβ)
    refine le_trans (le_of_eq ?_) hbound
    rw [ENNReal.ofReal_rpow_of_pos htpos,
      ENNReal.ofReal_rpow_of_pos (mul_pos htpos (Real.exp_pos _)),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht _)]
    congr 1
    rw [Real.mul_rpow ht (Real.exp_pos _).le, ← mul_assoc,
      ← Real.rpow_add htpos, show 1/N+(1-1/N) = (1:ℝ) by ring,
      Real.rpow_one, ← Real.exp_mul]
    congr 2
    field_simp

 
theorem ennreal_rpow_le_one_add (a : ℝ≥0∞) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    a^q ≤ 1+a := by
  by_cases ha : a ≤ 1
  · exact (ENNReal.rpow_le_one ha hq).trans (le_add_right le_rfl)
  · have hh := ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge ha) hq1
    rw [ENNReal.rpow_one] at hh
    exact hh.trans (le_add_left le_rfl)

 
theorem ennreal_rpow_tendsto_one {a : ℝ≥0∞} (ha : a ≠ ∞) (q : ℕ → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hq1 : Tendsto q atTop (𝓝 1)) :
    Tendsto (fun i => a^(q i)) atTop (𝓝 a) := by
  have hh : Tendsto (fun i => a.toReal^(q i)) atTop (𝓝 (a.toReal^(1:ℝ))) :=
    Filter.Tendsto.rpow tendsto_const_nhds hq1 (Or.inr zero_lt_one)
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  simpa only [Function.comp_def, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (hq _),
    ENNReal.ofReal_toReal ha, Real.rpow_one] using h

 

theorem lintegral_rpow_tendsto_mass {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ρ : X → ℝ≥0∞) (hρ : Measurable ρ)
    (hρfin : ∫⁻ x, ρ x ∂μ ≠ ∞) (s : Set X) (hs : MeasurableSet s) (hsfin : μ s ≠ ∞)
    (hsupp : ∀ᵐ x ∂μ, ρ x ≠ 0 → x ∈ s) (q : ℕ → ℝ)
    (hq : ∀ i, 0 < q i) (hqle : ∀ i, q i ≤ 1) (hqlim : Tendsto q atTop (𝓝 1)) :
    Tendsto (fun i => ∫⁻ x, (ρ x)^(q i) ∂μ) atTop (𝓝 (∫⁻ x, ρ x ∂μ)) := by
  apply tendsto_lintegral_of_dominated_convergence
    (fun x => s.indicator (fun _ => (1:ℝ≥0∞)) x + ρ x)
    (fun i => hρ.pow_const _)
  · intro i
    filter_upwards [hsupp] with x hx
    by_cases hxs : x ∈ s
    · simpa [hxs] using ennreal_rpow_le_one_add (ρ x) (hq i).le (hqle i)
    · have hz : ρ x = 0 := not_not.mp (mt hx hxs)
      simp [hxs, hz, ENNReal.zero_rpow_of_pos (hq i)]
  · rw [lintegral_add_left (measurable_const.indicator hs), lintegral_indicator hs]
    simpa using ENNReal.add_ne_top.mpr ⟨hsfin, hρfin⟩
  · filter_upwards [ae_lt_top hρ hρfin] with x hx
    exact ennreal_rpow_tendsto_one hx.ne q (fun i => (hq i).le) hqlim

 

theorem renyi_rnDeriv_tendsto_mass {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SigmaFinite μ] [IsFiniteMeasure ν]
    (s : Set X) (hs : MeasurableSet s) (hsfin : μ s ≠ ∞) (hsupp : ∀ᵐ x ∂ν, x ∈ s)
    (q : ℕ → ℝ) (hq : ∀ i, 0 < q i) (hqle : ∀ i, q i ≤ 1)
    (hqlim : Tendsto q atTop (𝓝 1)) :
    Tendsto (fun i => ∫⁻ x, (ν.rnDeriv μ x)^(q i) ∂μ) atTop
      (𝓝 (∫⁻ x, ν.rnDeriv μ x ∂μ)) := by
  exact lintegral_rpow_tendsto_mass μ (ν.rnDeriv μ) (Measure.measurable_rnDeriv _ _)
    (ne_top_of_le_ne_top (measure_ne_top _ _) Measure.lintegral_rnDeriv_le)
    s hs hsfin (Measure.ae_rnDeriv_ne_zero_imp_of_ae μ hsupp) q hq hqle hqlim

 

theorem ennreal_rpow_tendsto_zero {a : ℝ≥0∞} (ha0 : a ≠ 0) (ha : a ≠ ∞)
    (q : ℕ → ℝ) (hq : Tendsto q atTop (𝓝 0)) :
    Tendsto (fun i => a^(q i)) atTop (𝓝 1) := by
  have haR : 0 < a.toReal := ENNReal.toReal_pos ha0 ha
  have hh : Tendsto (fun i => a.toReal^(q i)) atTop (𝓝 (a.toReal^(0:ℝ))) :=
    Filter.Tendsto.rpow tendsto_const_nhds hq (Or.inl haR.ne')
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  simpa only [Function.comp_def, ← ENNReal.ofReal_rpow_of_pos haR,
    ENNReal.ofReal_toReal ha, Real.rpow_zero, ENNReal.ofReal_one] using h

 
theorem absolutelyContinuous_of_rnDeriv_mass_one {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SigmaFinite μ] [IsProbabilityMeasure ν]
    (hmass : ∫⁻ x, ν.rnDeriv μ x ∂μ = 1) : ν.AbsolutelyContinuous μ := by
  have hle := Measure.withDensity_rnDeriv_le ν μ
  have hmass' : (μ.withDensity (ν.rnDeriv μ)) univ = ν univ := by
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      measure_univ] using hmass
  let : IsFiniteMeasure (μ.withDensity (ν.rnDeriv μ)) := ⟨by rw [hmass']; simp⟩
  exact Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mpr
    (Measure.eq_of_le_of_measure_univ_eq hle hmass')

theorem dimension_reciprocal_tendsto (n : ℕ) :
    Tendsto (fun i : ℕ => 1/((n:ℝ)+i+2)) atTop (𝓝 0) := by
  have hadd : Tendsto (fun i : ℕ => (n:ℝ)+i+2) atTop atTop := by
    apply tendsto_atTop_mono (f := fun i : ℕ => (i:ℝ))
    · intro i
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · exact tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hadd

 
theorem gaussian_density_tendsto (n : ℕ) (K t d : ℝ) (ρ : ℝ≥0∞)
    (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ∞) :
    Tendsto (fun i : ℕ => ENNReal.ofReal
      (t*Real.exp (-|K| *d^2*(1-t^2)/(6*((n:ℝ)+i+2)))) *
      ρ^(-(1/((n:ℝ)+i+2)))) atTop (𝓝 (ENNReal.ofReal t)) := by
  have hrec := dimension_reciprocal_tendsto n
  have hx : Tendsto (fun i : ℕ => -|K| *d^2*(1-t^2)/(6*((n:ℝ)+i+2)))
      atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hrec using 1
    · ext i
      show _ = (-|K| *d^2*(1-t^2)/6) * (1/((n:ℝ)+i+2))
      field_simp
    · simp
  have he : Tendsto (fun i : ℕ => ENNReal.ofReal
      (t*Real.exp (-|K| *d^2*(1-t^2)/(6*((n:ℝ)+i+2)))))
      atTop (𝓝 (ENNReal.ofReal t)) := by
    simpa only [Function.comp_def, Real.exp_zero, mul_one] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := t)).mul (Real.continuous_exp.continuousAt.tendsto.comp hx))
  have hr : Tendsto (fun i : ℕ => ρ^(-(1/((n:ℝ)+i+2)))) atTop (𝓝 1) :=
    ennreal_rpow_tendsto_zero hρ0 hρtop _ (by simpa using hrec.neg)
  simpa only [mul_one] using ENNReal.Tendsto.mul he (Or.inr ENNReal.one_ne_top) hr
    (Or.inl one_ne_zero)

theorem ofReal_integral_le_lintegral_ofReal {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f : A → ℝ) (hf : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have hp : Integrable (fun x => max (f x) 0) μ := hf.sup (integrable_zero _ _ _)
  calc
    _ ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂μ) :=
      ENNReal.ofReal_le_ofReal (integral_mono hf hp (fun x => le_max_left _ _))
    _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hp (Eventually.of_forall fun x => le_max_right _ _)
    _ = _ := by congr 1; ext x; simp

 

theorem tau_density_entropy_lower (K N θ t : ℝ) (hN : 1 < N)
    (hθ : 0 ≤ θ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (ρ : ℝ≥0∞)
    (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ∞) :
    ENNReal.ofReal (t - (t/N)*Real.log ρ.toReal -
      (t/N)*((-K) *θ^2*(1-t^2)/6)) ≤ tau K N t θ * ρ^(-(1/N)) := by
  have hρ : 0 < ρ.toReal := ENNReal.toReal_pos hρ0 hρtop
  have hpow : ρ^(-(1/N)) = ENNReal.ofReal (ρ.toReal^(-(1/N))) := by
    rw [← ENNReal.ofReal_rpow_of_pos hρ, ENNReal.ofReal_toReal hρtop]
  calc
    _ ≤ ENNReal.ofReal (t*Real.exp
        (-(-K) *θ^2*(1-t^2)/(6*N) + Real.log ρ.toReal * (-(1/N)))) := by
      apply ENNReal.ofReal_le_ofReal
      have h := mul_le_mul_of_nonneg_left
        (Real.add_one_le_exp (-(-K) *θ^2*(1-t^2)/(6*N) +
          Real.log ρ.toReal * (-(1/N)))) ht
      calc
        _ = t * (-(-K) *θ^2*(1-t^2)/(6*N) + Real.log ρ.toReal * (-(1/N)) + 1) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        _ ≤ _ := h
    _ = ENNReal.ofReal (t*Real.exp (-(-K) *θ^2*(1-t^2)/(6*N))) *
        ρ^(-(1/N)) := by
      rw [hpow, ← ENNReal.ofReal_mul (mul_nonneg ht (Real.exp_pos _).le),
        Real.rpow_def_of_pos hρ, Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by simpa only [neg_neg] using
      mul_le_mul' (tau_signed_gaussian_lower K N θ t hN hθ ht ht1) (le_refl (ρ^(-(1/N))))

end RegularPointCoordinates

end OAI
