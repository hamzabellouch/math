import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedCollisionBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedCollisionHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.MediumStateCollision
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceGrowthBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.VolterraFubini
import OAI.MathematicalPhysics.Boltzmann.Jets.JetEnvelopeTimeIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

namespace OAI

section

/-! # Weak calculus for the actual damped characteristic formula -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

def damped (L c : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-L*t) * (c + ∫ r in 0..t, Real.exp (L*r)*g r)

theorem damped_eq (L c : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    damped L c g t = Real.exp (-L*t)*c +
      ∫ r in 0..t, Real.exp (-L*(t-r))*g r := by
  unfold damped
  rw [mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  dsimp
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem damped_continuousOn {T : ℝ} (hT : 0 ≤ T) (L c : ℝ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T) : ContinuousOn (damped L c g) (Icc 0 T) := by
  have he : Continuous (fun r : ℝ => Real.exp (L*r)) := by fun_prop
  have hi := hg.continuousOn_mul he.continuousOn
  have hp := intervalIntegral.continuousOn_primitive_interval' hi (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
  rw [uIcc_of_le hT] at hp
  exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-L*t))).continuousOn.mul
    (continuousOn_const.add hp)

theorem primitive_integration_by_parts {a b c : ℝ} (hab : a ≤ b) {h h' g : ℝ → ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt h (h' t) t)
    (hh' : IntervalIntegrable h' volume a b) (hg : IntervalIntegrable g volume a b)
    (hh : ContinuousOn h (Icc a b)) :
    (∫ t in a..b, h' t * (c + ∫ r in a..t, g r)) + (∫ t in a..b, h t*g t) =
      h b*(c + ∫ r in a..b, g r) - h a*c := by
  have hp := intervalIntegral.continuousOn_primitive_interval' hg (left_mem_uIcc : a ∈ uIcc a b)
  have hhg := hg.continuousOn_mul (by simpa only [uIcc_of_le hab] using hh)
  have hb := integral_deriv_mul_primitive hab hd hh' hg hhg
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le hab] using ht)) hh'
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add (hh'.mul_const c) (hh'.mul_continuousOn hp),
    intervalIntegral.integral_mul_const, hi, hb]
  ring

/-- Weak integration by parts for measurable characteristic forcing. -/
theorem damped_integration_by_parts {T L c : ℝ} (hT : 0 ≤ T) {g ψ ψ' : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T)
    (hψ : ContinuousOn ψ (Icc 0 T)) (hψ' : ContinuousOn ψ' (Icc 0 T))
    (hdψ : ∀ t ∈ Icc 0 T, HasDerivAt ψ (ψ' t) t) :
    (∫ t in 0..T, ψ' t*damped L c g t + ψ t*(g t-L*damped L c g t)) =
      ψ T*damped L c g T - ψ 0*c := by
  let h : ℝ → ℝ := fun t => ψ t*Real.exp (-L*t)
  let h' : ℝ → ℝ := fun t => (ψ' t-L*ψ t)*Real.exp (-L*t)
  let G : ℝ → ℝ := fun t => Real.exp (L*t)*g t
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt h (h' t) t := by
    intro t ht
    have he : HasDerivAt (fun r : ℝ => Real.exp (-L*r))
        (-L*Real.exp (-L*t)) t := by
      simpa only [id_eq, neg_mul, mul_comm, mul_one] using ((hasDerivAt_id t).const_mul (-L)).exp
    convert (hdψ t ht).mul he using 1
    dsimp [h,h']
    ring
  have hc : ContinuousOn h (Icc 0 T) := hψ.mul (by fun_prop)
  have hc' : ContinuousOn h' (Icc 0 T) := (hψ'.sub (hψ.const_mul L)).mul (by fun_prop)
  have hGi : IntervalIntegrable G volume 0 T :=
    hg.continuousOn_mul (by fun_prop)
  have hh'i : IntervalIntegrable h' volume 0 T :=
    (hc'.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  have H := primitive_integration_by_parts (c := c) hT hd hh'i hGi hc
  have he (t : ℝ) : Real.exp (-L*t)*Real.exp (L*t) = 1 := by
    rw [← Real.exp_add]
    simp only [neg_mul, neg_add_cancel, Real.exp_zero]
  have hfirst (t : ℝ) : h' t*(c+∫ r in 0..t, G r) =
      ψ' t*damped L c g t - L*ψ t*damped L c g t := by
    dsimp [h',damped,G]
    ring
  have hsecond (t : ℝ) : h t*G t = ψ t*g t := by
    dsimp [h,G]
    calc
      _ = ψ t*(Real.exp (-L*t)*Real.exp (L*t))*g t := by ring
      _ = _ := by rw [he]; ring
  have h3i : IntervalIntegrable (fun t => h' t*(c+∫ r in 0..t,G r)) volume 0 T := by
    apply hh'i.mul_continuousOn
    exact continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval' hGi left_mem_uIcc)
  have h4i : IntervalIntegrable (fun t => h t*G t) volume 0 T :=
    hGi.continuousOn_mul (by simpa only [uIcc_of_le hT] using hc)
  rw [← intervalIntegral.integral_add h3i h4i] at H
  have heq : (∫ t in 0..T, ψ' t*damped L c g t + ψ t*(g t-L*damped L c g t)) =
      ∫ t in 0..T, h' t*(c+∫ r in 0..t,G r) + h t*G t := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [hfirst,hsecond]
    ring
  rw [heq,H]
  dsimp [h,damped,G]
  simp only [mul_zero, neg_mul, Real.exp_zero, mul_one]
  ring

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Uniformly positive finite branching blocks in a nearby measurable medium -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedMediumBlockMass (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) (p : TimeFlightState)
    (κ d : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, ∫⁻ a, dampedMediumBlockIntegrand C b endTime p κ d n a ∂parameterWordMeasure T n

theorem damped_finite_history_block_transfer (Cmax : ℝ≥0) (N : ℕ) (T : ℝ) {κ d : ℝ}
    (hκ : 0 < κ) (hd : 0 < d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ C : ℝ≥0, referenceClock ≤ C → C ≤ Cmax →
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc 0 T, ∀ z : FlightState,
      (7 : ℝ≥0∞) < (∑ n ∈ Finset.range N, eventHistory C (branchingAt C)
        (flightSeed C ((blockTarget z.1 A κ d).indicator 1)) n (A,z)) →
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ n < N, ∀ a : ParameterWord n, GoodReferenceWord n (A,z) a →
        WordNearby b endTime ε n (embedFlightState (A,z)) a) →
      (6 : ℝ≥0∞) < dampedMediumBlockMass C b endTime T (A,z) κ d N := by
  obtain ⟨r,hr,hrsmall⟩ := dampedFiniteHistoryError_small Cmax N T
  let L : ℝ := (N:ℝ)+1
  have hL : 0 < L := by dsimp [L]; positivity
  let ε₀ := min (1/4:ℝ) (min (1/L) (min ((d*κ/8)/L) r))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    simp only [lt_min_iff]
    exact ⟨by norm_num,one_div_pos.mpr hL,by positivity,hr⟩
  refine ⟨ε₀,hε₀,?_⟩
  intro C hC hCmax ε hε A hA z href b endTime hnear
  have hcut : ε ≤ min (1/4:ℝ) (min (1/L) (min ((d*κ/8)/L) r)) := hε.2
  have hquarter := hcut.trans (min_le_left _ _)
  have htail := hcut.trans (min_le_right _ _)
  have hεL := htail.trans (min_le_left _ _)
  have htail' := htail.trans (min_le_right _ _)
  have hεd := htail'.trans (min_le_left _ _)
  have hεr := htail'.trans (min_le_right _ _)
  have hmass := hrsmall ε ⟨hε.1,hεr⟩
  have hsum : (∑ n ∈ Finset.range N, eventHistory C (branchingAt C)
      (flightSeed C ((blockTarget z.1 A κ d).indicator 1)) n (A,z)) ≤
      dampedMediumBlockMass C b endTime T (A,z) κ d N+dampedFiniteHistoryError Cmax N T ε := by
    calc
      _ ≤ ∑ n ∈ Finset.range N,
          ((∫⁻ a, dampedMediumBlockIntegrand C b endTime (A,z) κ d n a ∂parameterWordMeasure T n)+
            dampedHistoryPerturbationError Cmax n ε*(3*ENNReal.ofReal T)^n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN := (Finset.mem_range.mp hn).le
        have hnL : (n:ℝ) ≤ L :=
          (Nat.cast_le.mpr hnN).trans (le_add_of_nonneg_right (by norm_num))
        have hv : (n:ℝ)*ε ≤ 1 :=
          (mul_le_mul_of_nonneg_right hnL hε.1).trans
            (by simpa only [mul_comm] using (le_div_iff₀ hL).mp hεL)
        have hx' : (n:ℝ)*ε ≤ d*κ/8 :=
          (mul_le_mul_of_nonneg_right hnL hε.1).trans
            (by simpa only [mul_comm] using (le_div_iff₀ hL).mp hεd)
        have hx : 2*A*((n:ℝ)*ε) ≤ d*κ*A/4 := by
          convert mul_le_mul_of_nonneg_left hx' (show 0 ≤ (2:ℝ)*A from mul_nonneg (by norm_num) hA.1) using 1
          ring
        exact damped_medium_word_integral_lower hC hCmax b endTime n (A,z) T hε.1 hquarter hA.1 hA.2
          hv hx (hnear n (Finset.mem_range.mp hn))
      _ = _ := by rw [Finset.sum_add_distrib]; rfl
  by_contra hbad
  have hupper := hsum.trans (add_le_add (le_of_not_gt hbad) hmass.le)
  norm_num at hupper
  exact (not_lt_of_ge hupper) href

theorem uniform_damped_perturbed_block_growth {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∀ Cmax : ℝ≥0, ∃ N : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ C : ℝ≥0, referenceClock ≤ C → C ≤ Cmax →
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ n < N, ∀ a : ParameterWord n, GoodReferenceWord n (A,z) a →
        WordNearby b endTime ε n (embedFlightState (A,z)) a) →
      (6 : ℝ≥0∞) < dampedMediumBlockMass C b endTime T (A,z) κ d N := by
  obtain ⟨A₀,hA₀,hdepth⟩ := uniform_damped_finite_block_growth hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT Cmax
  obtain ⟨N,hN⟩ := hdepth T hT Cmax
  obtain ⟨ε₀,hε₀,htransfer⟩ := damped_finite_history_block_transfer Cmax N T hκ hd
  refine ⟨N,ε₀,hε₀,?_⟩
  intro C hC hCmax ε hε A hA z b endTime hnear
  exact htransfer C hC hCmax ε hε A ⟨hA₀.le.trans hA.1,hA.2⟩ z (hN C hC hCmax A hA z) b endTime hnear

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Constant damping preserves an absolutely continuous supersolution -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.DampedSupersolution

theorem integral_bound {u g : ℝ → ℝ} {l t L : ℝ} (ht : 0 < t)
    (hu : ∀ a, 0 < a → a ≤ t → AbsolutelyContinuousOnInterval u a t)
    (hl : Tendsto u (𝓝[>] 0) (𝓝 l))
    (hui : IntervalIntegrable u volume 0 t) (hgi : IntervalIntegrable g volume 0 t)
    (hd : ∀ᵐ r, r ∈ Ioc 0 t → HasDerivAt u (deriv u r) r ∧ g r ≤ deriv u r) :
    Real.exp (-L * t) * l +
      (∫ r in 0..t, Real.exp (-L * (t-r)) * (g r + L * u r)) ≤ u t := by
  have hec : ContDiff ℝ 1 (fun r : ℝ => Real.exp (L * r)) := by fun_prop
  have hei : IntervalIntegrable (fun r => Real.exp (L*r) * (g r + L*u r)) volume 0 t :=
    (hgi.add (hui.const_mul L)).continuousOn_mul hec.continuous.continuousOn
  have htr : Tendsto (fun r => Real.exp (L*r) * u r) (𝓝[>] 0) (𝓝 l) := by
    have he := hec.continuous.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa using he.mul hl
  have hb := JetIntegralSupersolution.integral_from_right_trace ht
    (u := fun r => Real.exp (L*r) * u r)
    (fun a ha hat => hec.contDiffOn.absolutelyContinuousOnInterval.mul (hu a ha hat))
    htr hei (by
      filter_upwards [hd] with r hr hrt
      have he : HasDerivAt (fun r : ℝ => Real.exp (L*r)) (Real.exp (L*r)*L) r :=
        by simpa using ((hasDerivAt_id r).const_mul L).exp
      have hdprod : HasDerivAt (fun r => Real.exp (L*r) * u r)
          (Real.exp (L*r)*L*u r + Real.exp (L*r)*deriv u r) r :=
        he.mul (hr hrt).1
      rw [hdprod.deriv]
      nlinarith [mul_le_mul_of_nonneg_left (hr hrt).2 (Real.exp_nonneg (L*r))])
  have hm := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (-L*t))
  have he : Real.exp (-L*t) * Real.exp (L*t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hi : Real.exp (-L*t) *
      (∫ r in 0..t, Real.exp (L*r) * (g r + L*u r)) =
      ∫ r in 0..t, Real.exp (-L*(t-r)) * (g r + L*u r) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [mul_add, hi, ← mul_assoc, he, one_mul] at hm
  exact hm

end BoltzmannNonuniqueness.DampedSupersolution

end

end

section

/-! # Quantitative survival for positive characteristic equations -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

theorem survival_of_derivative_bound {a b : ℝ} (hab : a ≤ b)
    {f r E k : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hE : ContDiff ℝ 1 E) (hE' : ∀ t, HasDerivAt E (k t) t)
    (hr : ∀ᵐ t, t ∈ Icc a b → HasDerivAt f (r t) t)
    (hb : ∀ᵐ t, t ∈ Icc a b → -k t*f t ≤ r t) :
    Real.exp (E a-E b)*f a ≤ f b := by
  let W : ℝ → ℝ := fun t => Real.exp (E t)*f t
  have hExp : ContDiff ℝ 1 (fun t => Real.exp (E t)) := Real.contDiff_exp.comp hE
  have hW : AbsolutelyContinuousOnInterval W a b :=
    hExp.contDiffOn.absolutelyContinuousOnInterval.mul hf
  have hd : ∀ᵐ t, t ∈ Icc a b → 0 ≤ deriv W t := by
    filter_upwards [hr,hb] with t ht hb htmem
    have h := ((hE' t).exp).mul (ht htmem)
    change HasDerivAt W _ t at h
    rw [h.deriv]
    have hp := mul_le_mul_of_nonneg_left (hb htmem) (Real.exp_pos (E t)).le
    nlinarith only [hp]
  have hi : 0 ≤ ∫ t in a..b, deriv W t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    filter_upwards [ae_restrict_of_ae hd,ae_restrict_mem measurableSet_Icc] with t ht hm
    exact ht hm
  rw [hW.integral_deriv_eq_sub] at hi
  have hh : Real.exp (E a)*f a ≤ Real.exp (E b)*f b := sub_nonneg.mp hi
  have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-E b)).le
  have hleft : Real.exp (-E b)*(Real.exp (E a)*f a) = Real.exp (E a-E b)*f a := by
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  have hright : Real.exp (-E b)*(Real.exp (E b)*f b) = f b := by
    rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
  rwa [hleft,hright] at hh'

theorem damped_absolutelyContinuous {T L c : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T) :
    AbsolutelyContinuousOnInterval (damped L c g) 0 T := by
  have he : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-L*t)) := by fun_prop
  have hi : IntervalIntegrable (fun r => Real.exp (L*r)*g r) volume 0 T :=
    hg.continuousOn_mul (by fun_prop)
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 T := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  exact he.contDiffOn.absolutelyContinuousOnInterval.mul (hc.add hp)

theorem damped_derivative_ae {T L c : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T) :
    ∀ᵐ t, t ∈ uIcc (0:ℝ) T →
      HasDerivAt (damped L c g) (g t-L*damped L c g t) t := by
  have hi : IntervalIntegrable (fun r => Real.exp (L*r)*g r) volume 0 T :=
    hg.continuousOn_mul (by fun_prop)
  filter_upwards [hi.ae_hasDerivAt_integral] with t ht hm
  have hp := (ht hm 0 left_mem_uIcc).const_add c
  have he := ((hasDerivAt_id t).const_mul (-L)).exp
  have hd := he.mul hp
  have hexp : Real.exp (-L*t)*Real.exp (L*t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  convert hd using 1
  · rfl
  · dsimp only [damped]
    dsimp only [id_eq] at hexp ⊢
    nlinarith only [congrArg (fun x : ℝ => x*g t) hexp]

theorem damped_survival {T L c : ℝ} (hT : 0 ≤ T) {g E k : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T)
    (hE : ContDiff ℝ 1 E) (hE' : ∀ t, HasDerivAt E (k t) t)
    (hb : ∀ᵐ t, t ∈ Icc 0 T →
      (L-k t)*damped L c g t ≤ g t) :
    Real.exp (E 0-E T)*c ≤ damped L c g T := by
  have hr : ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt (damped L c g) (g t-L*damped L c g t) t := by
    simpa only [uIcc_of_le hT] using damped_derivative_ae hg
  have hb' : ∀ᵐ t, t ∈ Icc 0 T →
      -k t*damped L c g t ≤ g t-L*damped L c g t := by
    filter_upwards [hb] with t ht hm
    nlinarith only [ht hm]
  have h := survival_of_derivative_bound hT (damped_absolutelyContinuous hg) hE hE' hr hb'
  simpa only [damped,intervalIntegral.integral_same,add_zero,mul_zero,Real.exp_zero,one_mul] using h

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # The actual Fourier multiplier of a damped characteristic line -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem fourier_line_translation (f : FourierSpace → ℂ) (w k : FourierSpace) (s : ℝ) :
    𝓕 (fun x => f (x-s • w)) k = 𝐞 (-s*inner ℝ w k) • 𝓕 f k := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
    𝐞 (volume : Measure FourierSpace) (innerₗ FourierSpace) f ((-s) • w)) k
  change 𝓕 (fun x => f (x+(-s) • w)) k = 𝐞 (inner ℝ ((-s) • w) k) • 𝓕 f k at h
  simp only [real_inner_smul_left] at h
  simpa only [neg_smul,sub_eq_add_neg,neg_mul] using h

theorem damped_phase_character (a s : ℝ) (z : ℂ) :
    Real.exp (-s) • (𝐞 (-s*a) • z) = dampedCharacter (2*Real.pi*a) s*z := by
  change (Real.exp (-s) : ℂ) *
    (Complex.exp (↑(2*Real.pi*(-s*a)) * Complex.I) * z) =
    ((Real.exp (-s) : ℂ) * Complex.exp (-Complex.I * (↑(2*Real.pi*a) * ↑s))) * z
  have he : (↑(2*Real.pi*(-s*a)) : ℂ) * Complex.I =
      -Complex.I * (↑(2*Real.pi*a) * ↑s) := by push_cast; ring
  rw [he]
  exact (mul_assoc _ _ _).symm

theorem fourier_dampedLine {f : FourierSpace → ℂ} (hf : Integrable f) (w k : FourierSpace) :
    𝓕 (dampedLineResolvent f w) k =
      (1+Complex.I*(2*Real.pi*inner ℝ w k))⁻¹ * 𝓕 f k := by
  rw [fourier_dampedLine_integral hf]
  simp_rw [fourier_line_translation,damped_phase_character]
  rw [integral_mul_const,integral_dampedCharacter]
  push_cast
  rfl

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Smooth localization changes damping to the unit transport resolvent -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

/-- A smooth cutoff of a measurable-forcing mild solution has an explicit
unit-damped formula. This is the scalar part of the GLPS localization. -/
theorem localized_damped {T L c : ℝ} (hT : 0 ≤ T) {g χ χ' : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T)
    (hχ : ContinuousOn χ (Icc 0 T)) (hχ' : ContinuousOn χ' (Icc 0 T))
    (hdχ : ∀ t ∈ Icc 0 T, HasDerivAt χ (χ' t) t) :
    χ T*damped L c g T = Real.exp (-T)*χ 0*c +
      ∫ t in 0..T, Real.exp (-(T-t)) *
        (χ t*g t + (χ' t+(1-L)*χ t)*damped L c g t) := by
  let ψ : ℝ → ℝ := fun t => Real.exp t*χ t
  let ψ' : ℝ → ℝ := fun t => Real.exp t*(χ' t+χ t)
  have hψ : ContinuousOn ψ (Icc 0 T) := (by fun_prop : Continuous (Real.exp)).continuousOn.mul hχ
  have hψ' : ContinuousOn ψ' (Icc 0 T) := (by fun_prop : Continuous (Real.exp)).continuousOn.mul (hχ'.add hχ)
  have hdψ : ∀ t ∈ Icc 0 T, HasDerivAt ψ (ψ' t) t := by
    intro t ht
    convert (Real.hasDerivAt_exp t).mul (hdχ t ht) using 1
    dsimp [ψ,ψ']
    ring
  have H := damped_integration_by_parts hT hg hψ hψ' hdψ (L := L) (c := c)
  have he : Real.exp (-T)*Real.exp T = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  have hcalc : Real.exp (-T)*(∫ t in 0..T,
      ψ' t*damped L c g t+ψ t*(g t-L*damped L c g t)) =
      ∫ t in 0..T, Real.exp (-(T-t)) *
        (χ t*g t+(χ' t+(1-L)*χ t)*damped L c g t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [ψ,ψ']
    have hexp : Real.exp (-(T-t)) = Real.exp (-T)*Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  rw [H] at hcalc
  dsimp [ψ] at hcalc
  rw [Real.exp_zero,one_mul] at hcalc
  have hmul : Real.exp (-T)*(Real.exp T*χ T*damped L c g T) = χ T*damped L c g T := by
    calc
      _ = (Real.exp (-T)*Real.exp T)*χ T*damped L c g T := by ring
      _ = _ := by rw [he,one_mul]
  rw [mul_sub,hmul] at hcalc
  linarith

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Finite medium histories equal powers of the actual marked event kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedMediumWord_integral (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (p : PhysicalFlightState) :
    (∫⁻ a, dampedMediumWordDensity C b endTime n p a * F (mediumWordState b endTime n p a)
      ∂parameterWordMeasure T n) = ∫⁻ q, F q ∂((dampedMediumEventKernel C b endTime T)^n) p := by
  induction n generalizing p with
  | zero =>
    have hi : (1 : Kernel PhysicalFlightState PhysicalFlightState) = Kernel.id := rfl
    rw [pow_zero,hi,Kernel.id_apply,lintegral_dirac]
    change (∫⁻ _a : PUnit, 1*F p ∂Measure.dirac PUnit.unit) = F p
    rw [lintegral_const,Measure.dirac_apply_of_mem (mem_univ _),mul_one,one_mul]
  | succ n ih =>
    have hmap : Measurable (fun a : ParameterWord (n+1) => (p,a)) :=
      measurable_const.prodMk measurable_id
    have hd : Measurable (fun a : ParameterWord (n+1) => dampedMediumWordDensity C b endTime (n+1) p a) := by
      simpa only [Function.comp_def] using (dampedMediumWordDensity_measurable C b endTime (n+1)).comp hmap
    have hs : Measurable (fun a : ParameterWord (n+1) => mediumWordState b endTime (n+1) p a) := by
      simpa only [Function.comp_def] using (mediumWordState_measurable b endTime (n+1)).comp hmap
    have hm : Measurable (fun a : ParameterWord (n+1) =>
        dampedMediumWordDensity C b endTime (n+1) p a * F (mediumWordState b endTime (n+1) p a)) :=
      hd.mul (hF.comp hs)
    rw [parameterWordMeasure,lintegral_prod _ hm.aemeasurable]
    rw [show (dampedMediumEventKernel C b endTime T)^(n+1) =
        ((dampedMediumEventKernel C b endTime T)^n) ∘ₖ dampedMediumEventKernel C b endTime T by
      simpa only [pow_one] using Kernel.pow_add (dampedMediumEventKernel C b endTime T) n 1,
      Kernel.lintegral_comp _ _ _ hF,
      dampedMediumEventKernel_lintegral C b endTime T p (hF.lintegral_kernel (κ := (dampedMediumEventKernel C b endTime T)^n))]
    apply lintegral_congr
    intro a
    change (∫⁻ w, (dampedMediumParameterDensity C b endTime p a *
      dampedMediumWordDensity C b endTime n (mediumParameterState b endTime p a) w) *
      F (mediumWordState b endTime n (mediumParameterState b endTime p a) w)
        ∂parameterWordMeasure T n) = _
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ (dampedMediumParameterDensity_ne_top C b endTime p a),ih]

def dampedMediumFlightSeed (C : ℝ≥0) (f : V × V → ℝ≥0∞) (p : PhysicalFlightState) : ℝ≥0∞ :=
  clockSurvival C p.1*f (finishMediumFlight p)

theorem dampedMediumBlockMass_kernel (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ)
    (p : TimeFlightState) (κ d : ℝ) (N : ℕ) :
    dampedMediumBlockMass C b endTime T p κ d N =
      ∑ n ∈ Finset.range N, ∫⁻ q,
        dampedMediumFlightSeed C ((physicalBlockTarget p.2.1 p.1 κ d).indicator 1) q
          ∂((dampedMediumEventKernel C b endTime T)^n) (embedFlightState p) := by
  unfold dampedMediumBlockMass
  apply Finset.sum_congr rfl
  intro n _hn
  exact dampedMediumWord_integral C b endTime T
    ((show Measurable (fun p : PhysicalFlightState => clockSurvival C p.1) by unfold clockSurvival; fun_prop).mul
      ((measurable_const.indicator (physicalBlockTarget_measurable _ _ _ _)).comp finishMediumFlight_measurable))
      n (embedFlightState p)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The event kernel with all intermediate velocities in the physical box -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedBoundedEventKernel (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (dampedMediumEventKernel C b endTime T).restrict mediumVelocityBox_measurable

instance dampedBoundedEventKernel_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) :
    IsSFiniteKernel (dampedBoundedEventKernel C b endTime T) := by
  unfold dampedBoundedEventKernel
  infer_instance

theorem dampedBoundedEventKernel_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂dampedBoundedEventKernel C b endTime T p) =
      ∫⁻ a, dampedMediumParameterDensity C b endTime p a *
        (mediumVelocityBox.indicator 1 (mediumParameterState b endTime p a) *
          F (mediumParameterState b endTime p a)) ∂markedEventMeasure T := by
  rw [dampedBoundedEventKernel,Kernel.lintegral_restrict,
    ← lintegral_indicator mediumVelocityBox_measurable,
    dampedMediumEventKernel_lintegral C b endTime T p (hF.indicator mediumVelocityBox_measurable)]
  apply lintegral_congr
  intro a
  by_cases ha : mediumParameterState b endTime p a ∈ mediumVelocityBox
  · simp [ha]
  · simp [ha]

instance dampedBoundedEventKernel_pow_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ) :
    IsSFiniteKernel ((dampedBoundedEventKernel C b endTime T)^n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    rw [show (dampedBoundedEventKernel C b endTime T)^(n+1) =
        ((dampedBoundedEventKernel C b endTime T)^n) ∘ₖ dampedBoundedEventKernel C b endTime T by
      simpa only [pow_one] using Kernel.pow_add (dampedBoundedEventKernel C b endTime T) n 1]
    let _ := ih
    infer_instance

theorem dampedBoundedWord_integral (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (p : PhysicalFlightState) :
    (∫⁻ a, dampedBoundedWordDensity C b endTime n p a * F (mediumWordState b endTime n p a)
      ∂parameterWordMeasure T n) = ∫⁻ q, F q ∂((dampedBoundedEventKernel C b endTime T)^n) p := by
  induction n generalizing p with
  | zero =>
    change (∫⁻ _a : PUnit, 1*F p ∂Measure.dirac PUnit.unit) = ∫⁻ q, F q ∂Kernel.id p
    simp [Kernel.id_apply,lintegral_dirac' _ hF]
  | succ n ih =>
    have hmap : Measurable (fun a : ParameterWord (n+1) => (p,a)) :=
      measurable_const.prodMk measurable_id
    have hd : Measurable (fun a : ParameterWord (n+1) => dampedBoundedWordDensity C b endTime (n+1) p a) :=
      (dampedBoundedWordDensity_measurable C b endTime (n+1)).comp hmap
    have hs : Measurable (fun a : ParameterWord (n+1) => mediumWordState b endTime (n+1) p a) :=
      (mediumWordState_measurable b endTime (n+1)).comp hmap
    have hm : Measurable (fun a : ParameterWord (n+1) =>
        dampedBoundedWordDensity C b endTime (n+1) p a * F (mediumWordState b endTime (n+1) p a)) :=
      hd.mul (hF.comp hs)
    rw [parameterWordMeasure,lintegral_prod _ hm.aemeasurable]
    rw [show (dampedBoundedEventKernel C b endTime T)^(n+1) =
        ((dampedBoundedEventKernel C b endTime T)^n) ∘ₖ dampedBoundedEventKernel C b endTime T by
      simpa only [pow_one] using Kernel.pow_add (dampedBoundedEventKernel C b endTime T) n 1,
      Kernel.lintegral_comp _ _ _ hF,
      dampedBoundedEventKernel_lintegral C b endTime T p
        (hF.lintegral_kernel (κ := (dampedBoundedEventKernel C b endTime T)^n))]
    apply lintegral_congr
    intro a
    change (∫⁻ w, (dampedMediumParameterDensity C b endTime p a *
        (mediumVelocityBox.indicator 1 (mediumParameterState b endTime p a) *
          dampedBoundedWordDensity C b endTime n (mediumParameterState b endTime p a) w)) *
        F (mediumWordState b endTime n (mediumParameterState b endTime p a) w)
          ∂parameterWordMeasure T n) = _
    have hb : mediumVelocityBox.indicator (1 : PhysicalFlightState → ℝ≥0∞)
        (mediumParameterState b endTime p a) ≠ ⊤ := by
      by_cases ha : mediumParameterState b endTime p a ∈ mediumVelocityBox <;> simp [ha]
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ (dampedMediumParameterDensity_ne_top C b endTime p a),
      lintegral_const_mul' _ _ hb,ih]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Lower transfer of reference blocks with every velocity kept bounded -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedBoundedBlockIntegrand (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (p : TimeFlightState)
    (κ d : ℝ) (n : ℕ) (a : ParameterWord n) : ℝ≥0∞ :=
  let q := mediumWordState b endTime n (embedFlightState p) a
  dampedBoundedWordDensity C b endTime n (embedFlightState p) a *
    (clockSurvival C q.1 *
      (physicalBlockTarget p.2.1 p.1 κ d).indicator 1 (finishMediumFlight q))

def dampedBoundedBlockMass (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) (p : TimeFlightState)
    (κ d : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N,
    ∫⁻ a, dampedBoundedBlockIntegrand C b endTime p κ d n a ∂parameterWordMeasure T n

theorem damped_bounded_word_integrand_bound {C Cmax : ℝ≥0} (hC : referenceClock ≤ C)
    (hCmax : C ≤ Cmax) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (a : ParameterWord n) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hp : 0 ≤ p.1) (hv : (n:ℝ)*ε ≤ 1)
    (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (hnear : GoodReferenceWord n p a → WordNearby b endTime ε n (embedFlightState p) a) :
    dampedWordDensity C n p a * flightSeed C
        ((blockTarget p.2.1 p.1 κ d).indicator 1) (parameterWordState n p a) ≤
      dampedBoundedBlockIntegrand C b endTime p κ d n a+dampedHistoryPerturbationError Cmax n ε := by
  by_cases hr : dampedWordDensity C n p a = 0
  · rw [hr,zero_mul]
    exact bot_le
  have ha := goodReferenceWord_of_damped_density_ne_zero C n p a hr
  have he := dampedBoundedWordDensity_eq C b endTime n a (δ := 0)
    (by simpa using hv) (by simp [embedFlightState]) ha (hnear ha)
  unfold dampedBoundedBlockIntegrand
  rw [he]
  exact damped_medium_word_integrand_bound hC hCmax b endTime n p a hε hε1 hp hv hx hnear

theorem damped_bounded_word_integral_lower {C Cmax : ℝ≥0} (hC : referenceClock ≤ C)
    (hCmax : C ≤ Cmax) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (T : ℝ) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hp : 0 ≤ p.1) (hpT : p.1 ≤ T)
    (hv : (n:ℝ)*ε ≤ 1) (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (hnear : ∀ a, GoodReferenceWord n p a → WordNearby b endTime ε n (embedFlightState p) a) :
    eventHistory C (branchingAt C)
        (flightSeed C ((blockTarget p.2.1 p.1 κ d).indicator 1)) n p ≤
      (∫⁻ a, dampedBoundedBlockIntegrand C b endTime p κ d n a ∂parameterWordMeasure T n)+
        dampedHistoryPerturbationError Cmax n ε*(3*ENNReal.ofReal T)^n := by
  have hf : Measurable ((blockTarget p.2.1 p.1 κ d).indicator (1 : FlightState → ℝ≥0∞)) :=
    measurable_const.indicator (blockTarget_measurable _ _ _ _)
  rw [← dampedWord_integral C (flightSeed_measurable C hf) T n p ⟨hp,hpT⟩]
  calc
    _ ≤ ∫⁻ a, dampedBoundedBlockIntegrand C b endTime p κ d n a+dampedHistoryPerturbationError Cmax n ε
        ∂parameterWordMeasure T n :=
      lintegral_mono (fun a => damped_bounded_word_integrand_bound hC hCmax b endTime n p a
        hε hε1 hp hv hx (hnear a))
    _ = _ := by rw [lintegral_add_right _ measurable_const,lintegral_const,parameterWordMeasure_mass]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniformly positive finite branching blocks in a nearby measurable medium -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem damped_bounded_finite_history_block_transfer (Cmax : ℝ≥0) (N : ℕ) (T : ℝ) {κ d : ℝ}
    (hκ : 0 < κ) (hd : 0 < d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ C : ℝ≥0, referenceClock ≤ C → C ≤ Cmax →
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc 0 T, ∀ z : FlightState,
      (7 : ℝ≥0∞) < (∑ n ∈ Finset.range N, eventHistory C (branchingAt C)
        (flightSeed C ((blockTarget z.1 A κ d).indicator 1)) n (A,z)) →
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ n < N, ∀ a : ParameterWord n, GoodReferenceWord n (A,z) a →
        WordNearby b endTime ε n (embedFlightState (A,z)) a) →
      (6 : ℝ≥0∞) < dampedBoundedBlockMass C b endTime T (A,z) κ d N := by
  obtain ⟨r,hr,hrsmall⟩ := dampedFiniteHistoryError_small Cmax N T
  let L : ℝ := (N:ℝ)+1
  have hL : 0 < L := by dsimp [L]; positivity
  let ε₀ := min (1/4:ℝ) (min (1/L) (min ((d*κ/8)/L) r))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    simp only [lt_min_iff]
    exact ⟨by norm_num,one_div_pos.mpr hL,by positivity,hr⟩
  refine ⟨ε₀,hε₀,?_⟩
  intro C hC hCmax ε hε A hA z href b endTime hnear
  have hcut : ε ≤ min (1/4:ℝ) (min (1/L) (min ((d*κ/8)/L) r)) := hε.2
  have hquarter := hcut.trans (min_le_left _ _)
  have htail := hcut.trans (min_le_right _ _)
  have hεL := htail.trans (min_le_left _ _)
  have htail' := htail.trans (min_le_right _ _)
  have hεd := htail'.trans (min_le_left _ _)
  have hεr := htail'.trans (min_le_right _ _)
  have hmass := hrsmall ε ⟨hε.1,hεr⟩
  have hsum : (∑ n ∈ Finset.range N, eventHistory C (branchingAt C)
      (flightSeed C ((blockTarget z.1 A κ d).indicator 1)) n (A,z)) ≤
      dampedBoundedBlockMass C b endTime T (A,z) κ d N+dampedFiniteHistoryError Cmax N T ε := by
    calc
      _ ≤ ∑ n ∈ Finset.range N,
          ((∫⁻ a, dampedBoundedBlockIntegrand C b endTime (A,z) κ d n a ∂parameterWordMeasure T n)+
            dampedHistoryPerturbationError Cmax n ε*(3*ENNReal.ofReal T)^n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN := (Finset.mem_range.mp hn).le
        have hnL : (n:ℝ) ≤ L :=
          (Nat.cast_le.mpr hnN).trans (le_add_of_nonneg_right (by norm_num))
        have hv : (n:ℝ)*ε ≤ 1 :=
          (mul_le_mul_of_nonneg_right hnL hε.1).trans
            (by simpa only [mul_comm] using (le_div_iff₀ hL).mp hεL)
        have hx' : (n:ℝ)*ε ≤ d*κ/8 :=
          (mul_le_mul_of_nonneg_right hnL hε.1).trans
            (by simpa only [mul_comm] using (le_div_iff₀ hL).mp hεd)
        have hx : 2*A*((n:ℝ)*ε) ≤ d*κ*A/4 := by
          convert mul_le_mul_of_nonneg_left hx' (show 0 ≤ (2:ℝ)*A from mul_nonneg (by norm_num) hA.1) using 1
          ring
        exact damped_bounded_word_integral_lower hC hCmax b endTime n (A,z) T hε.1 hquarter hA.1 hA.2
          hv hx (hnear n (Finset.mem_range.mp hn))
      _ = _ := by rw [Finset.sum_add_distrib]; rfl
  by_contra hbad
  have hupper := hsum.trans (add_le_add (le_of_not_gt hbad) hmass.le)
  norm_num at hupper
  exact (not_lt_of_ge hupper) href

theorem uniform_damped_bounded_block_growth {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∀ Cmax : ℝ≥0, ∃ N : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ C : ℝ≥0, referenceClock ≤ C → C ≤ Cmax →
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ n < N, ∀ a : ParameterWord n, GoodReferenceWord n (A,z) a →
        WordNearby b endTime ε n (embedFlightState (A,z)) a) →
      (6 : ℝ≥0∞) < dampedBoundedBlockMass C b endTime T (A,z) κ d N := by
  obtain ⟨A₀,hA₀,hdepth⟩ := uniform_damped_finite_block_growth hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT Cmax
  obtain ⟨N,hN⟩ := hdepth T hT Cmax
  obtain ⟨ε₀,hε₀,htransfer⟩ := damped_bounded_finite_history_block_transfer Cmax N T hκ hd
  refine ⟨N,ε₀,hε₀,?_⟩
  intro C hC hCmax ε hε A hA z b endTime hnear
  exact htransfer C hC hCmax ε hε A ⟨hA₀.le.trans hA.1,hA.2⟩ z (hN C hC hCmax A hA z) b endTime hnear

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Endpoint measures for the bounded physical collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedMediumFlightSeed_measurable (C : ℝ≥0) {f : V × V → ℝ≥0∞}
    (hf : Measurable f) : Measurable (dampedMediumFlightSeed C f) :=
  (show Measurable (fun p : PhysicalFlightState => clockSurvival C p.1) by
    unfold clockSurvival; fun_prop).mul (hf.comp finishMediumFlight_measurable)

def dampedBoundedEndpointKernel (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ) :
    Kernel PhysicalFlightState (V × V) :=
  (Kernel.withDensity ((dampedBoundedEventKernel C b endTime T)^n)
    (fun _ p => clockSurvival C p.1)).map finishMediumFlight

instance dampedBoundedEndpointKernel_isSFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ) :
    IsSFiniteKernel (dampedBoundedEndpointKernel C b endTime T n) := by
  have hs : IsSFiniteKernel (Kernel.withDensity ((dampedBoundedEventKernel C b endTime T)^n)
      (fun _ p => clockSurvival C p.1)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro p q
    exact ENNReal.ofReal_ne_top
  unfold dampedBoundedEndpointKernel
  infer_instance

theorem dampedBoundedEndpointKernel_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ)
    (p : PhysicalFlightState) {F : V × V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂dampedBoundedEndpointKernel C b endTime T n p) =
      ∫⁻ q, dampedMediumFlightSeed C F q ∂((dampedBoundedEventKernel C b endTime T)^n) p := by
  have hc : Measurable (Function.uncurry (fun (_ : PhysicalFlightState) (q : PhysicalFlightState) =>
      clockSurvival C q.1)) := by unfold clockSurvival; fun_prop
  have hf : Measurable (fun q : PhysicalFlightState => F (finishMediumFlight q)) := by
    simpa only [Function.comp_def] using hF.comp finishMediumFlight_measurable
  rw [dampedBoundedEndpointKernel,Kernel.lintegral_map _ finishMediumFlight_measurable p hF,
    Kernel.lintegral_withDensity _ hc p hf]
  rfl

theorem dampedBoundedEndpointKernel_apply (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ)
    (p : PhysicalFlightState) {A : Set (V × V)} (hA : MeasurableSet A) :
    dampedBoundedEndpointKernel C b endTime T n p A =
      ∫⁻ q, dampedMediumFlightSeed C (A.indicator 1) q ∂((dampedBoundedEventKernel C b endTime T)^n) p := by
  have H := dampedBoundedEndpointKernel_lintegral C b endTime T n p
    (measurable_const.indicator hA : Measurable (A.indicator (1 : V × V → ℝ≥0∞)))
  change (∫⁻ y, A.indicator (1 : V × V → ℝ≥0∞) y ∂dampedBoundedEndpointKernel C b endTime T n p) = _ at H
  rw [lintegral_indicator_one hA] at H
  exact H

theorem dampedBoundedBlockMass_endpoints (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ)
    (p : TimeFlightState) (κ d : ℝ) (N : ℕ) :
    dampedBoundedBlockMass C b endTime T p κ d N =
      ∑ n ∈ Finset.range N, dampedBoundedEndpointKernel C b endTime T n (embedFlightState p)
        (physicalBlockTarget p.2.1 p.1 κ d) := by
  unfold dampedBoundedBlockMass
  apply Finset.sum_congr rfl
  intro n _hn
  rw [dampedBoundedEndpointKernel_apply C b endTime T n (embedFlightState p)
    (physicalBlockTarget_measurable _ _ _ _)]
  exact dampedBoundedWord_integral C b endTime T
    (dampedMediumFlightSeed_measurable C (measurable_const.indicator
      (physicalBlockTarget_measurable _ _ _ _))) n (embedFlightState p)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Changing a constant attenuation adds its difference as self-retention -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

theorem damped_change_rate {T L M c : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T) :
    damped L c g T = damped M c (fun t => g t+(M-L)*damped L c g t) T := by
  let ψ : ℝ → ℝ := fun t => Real.exp (M*t)
  let ψ' : ℝ → ℝ := fun t => M*Real.exp (M*t)
  have hψ : ContinuousOn ψ (Icc 0 T) := by unfold ψ; fun_prop
  have hψ' : ContinuousOn ψ' (Icc 0 T) := by unfold ψ'; fun_prop
  have hdψ : ∀ t ∈ Icc 0 T, HasDerivAt ψ (ψ' t) t := by
    intro t _ht
    simpa only [ψ,ψ',id_eq,mul_one,mul_comm] using ((hasDerivAt_id t).const_mul M).exp
  have H := damped_integration_by_parts hT hg hψ hψ' hdψ (L := L) (c := c)
  have he : Real.exp (-M*T)*Real.exp (M*T) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hcalc : Real.exp (-M*T)*(∫ t in 0..T,
      ψ' t*damped L c g t+ψ t*(g t-L*damped L c g t)) =
      ∫ t in 0..T, Real.exp (-M*(T-t))*(g t+(M-L)*damped L c g t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp [ψ,ψ']
    have hx : Real.exp (-M*(T-t)) = Real.exp (-M*T)*Real.exp (M*t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hx]
    ring
  rw [H] at hcalc
  dsimp [ψ] at hcalc
  rw [mul_zero,Real.exp_zero,one_mul,mul_sub] at hcalc
  have hcancel : Real.exp (-M*T)*(Real.exp (M*T)*damped L c g T) = damped L c g T := by
    rw [← mul_assoc,he,one_mul]
  rw [hcancel] at hcalc
  rw [damped_eq M]
  linarith

theorem changed_forcing_intervalIntegrable {T L M c : ℝ} (hT : 0 ≤ T)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 T) :
    IntervalIntegrable (fun t => g t+(M-L)*damped L c g t) volume 0 T := by
  apply hg.add
  apply IntervalIntegrable.const_mul
  exact ((damped_continuousOn hT L c hg).mono (by rw [uIcc_of_le hT])).intervalIntegrable

end BoltzmannNonuniqueness.TransportPrimitive

end

end

end OAI
