import OAI.NumberTheory.Jacobsthal.Estimates.MovingLocalReference

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceIntervalCutoff

attribute [local instance] Classical.propDecidable
open _root_.Finset _root_.Set _root_.MeasureTheory
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership
open ReferenceSourcePrimeSets ReferenceMertens ReferenceLocalResidual ReferenceHighIntervals ReferenceResidualErrors
open ReferenceBenchmarkDecay ReferenceDifferentiation
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def primeInterval (a b : ℝ) (closed : Bool) : Set ℝ :=
  {x | a<x ∧ capGuard closed b x}

noncomputable def intervalPrimes (w a b : ℝ) (closed : Bool) : Finset ℕ :=
  (highPrimes w b closed).filter (fun p => a<primeExponent w p)

noncomputable def rebase (z : Node) (a : ℝ) : Node :=
  {z with ratio := z.gap/a,cutoff := a,closed := true}

noncomputable def intervalResidual (w : ℝ) (z : Node) (a : ℝ) : ℝ :=
  referenceProduct w a true*(parentBenchmark z.side (z.gap/a)-1)-
    referenceProduct w z.cutoff z.closed*(parentBenchmark z.side z.ratio-1)-
    ∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      (benchmark z.side.flip (childRatio w z.gap p)-1)

theorem primeInterval_measurable (a b : ℝ) (closed : Bool) : MeasurableSet (primeInterval a b closed) := by
  cases closed <;> simp only [primeInterval,capGuard,Bool.false_eq_true,ite_false,ite_true] <;> measurability

theorem primeInterval_orderConnected (a b : ℝ) (closed : Bool) : (primeInterval a b closed).OrdConnected := by
  cases closed
  · exact ordConnected_Ioo
  · exact ordConnected_Ioc

theorem primeInterval_subset (a b : ℝ) (closed : Bool) : primeInterval a b closed ⊆ Icc a b := by
  intro x hx
  refine ⟨hx.1.le,?_⟩
  cases closed
  · exact hx.2.le
  · exact hx.2

theorem primeInterval_integral {a b : ℝ} (hab : a ≤ b) (closed : Bool) (F : ℝ → ℝ) :
    (∫ x in primeInterval a b closed,F x)=∫ x in a..b,F x := by
  cases closed
  · change (∫ x in Ioo a b,F x)=_
    rw [← integral_Ioc_eq_integral_Ioo,intervalIntegral.integral_of_le hab]
  · exact (intervalIntegral.integral_of_le hab).symm

theorem intervalPrimes_eq_filter {w a : ℝ} (hw : 1 < w) (ha : 2 ≤ a) (b : ℝ) (closed : Bool) :
    intervalPrimes w a b closed=(Nat.primesLE ⌊w^b⌋₊).filter (fun p => primeExponent w p ∈ primeInterval a b closed) := by
  rw [intervalPrimes,highPrimes_eq_filter hw,Finset.filter_filter]
  apply Finset.filter_congr
  intro p _hp
  simp only [highInterval,primeInterval,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨_h2,hcap⟩,haP⟩
    exact ⟨haP,hcap⟩
  · rintro ⟨haP,hcap⟩
    exact ⟨⟨ha.trans_lt haP,hcap⟩,haP⟩

theorem intervalPrime_sum {w a : ℝ} (hw : 1 < w) (ha : 2 ≤ a) (b : ℝ) (closed : Bool) (F : ℕ → ℝ) :
    (∑ p ∈ intervalPrimes w a b closed,F p)=
      ∑ p ∈ Nat.primesLE ⌊w^b⌋₊,if primeExponent w p ∈ primeInterval a b closed then F p else 0 := by
  rw [intervalPrimes_eq_filter hw ha,Finset.sum_filter]

theorem lowerHigh_subset {w a b : ℝ} (hw : 1 < w) (hab : a < b) (closed : Bool) :
    highPrimes w a true ⊆ highPrimes w b closed := by
  intro p hp
  obtain ⟨hpP,h2,ha⟩ := (highPrimes_membership hw a true p).mp hp
  have ha' : primeExponent w p ≤ a := ha
  apply (highPrimes_membership hw b closed p).mpr
  refine ⟨hpP,h2,?_⟩
  cases closed
  · exact ha'.trans_lt hab
  · exact ha'.trans hab.le

theorem highPrimes_split {w a b : ℝ} (hw : 1 < w) (hab : a < b) (closed : Bool) :
    highPrimes w b closed=highPrimes w a true ∪ intervalPrimes w a b closed := by
  ext p
  constructor
  · intro hp
    by_cases hx : a<primeExponent w p
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp,hx⟩))
    · obtain ⟨hpP,h2,_hcap⟩ := (highPrimes_membership hw b closed p).mp hp
      exact Finset.mem_union.mpr (Or.inl ((highPrimes_membership hw a true p).mpr ⟨hpP,h2,le_of_not_gt hx⟩))
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact lowerHigh_subset hw hab closed hp
    · exact (Finset.mem_filter.mp hp).1

theorem highPrimes_split_disjoint {w a b : ℝ} (hw : 1 < w) (closed : Bool) :
    Disjoint (highPrimes w a true) (intervalPrimes w a b closed) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hlow : primeExponent w p ≤ a := ((highPrimes_membership hw a true p).mp hp).2.2
  have hhigh := (Finset.mem_filter.mp hq).2
  exact (not_lt_of_ge hlow) hhigh

theorem highPrime_sum_split {w a b : ℝ} (hw : 1 < w) (hab : a < b) (closed : Bool) (F : ℕ → ℝ) :
    (∑ p ∈ highPrimes w b closed,F p)=
      (∑ p ∈ highPrimes w a true,F p)+(∑ p ∈ intervalPrimes w a b closed,F p) := by
  rw [highPrimes_split hw hab,Finset.sum_union (highPrimes_split_disjoint hw closed)]

theorem residual_split {w : ℝ} (hw : 1 < w) (z : Node) {a : ℝ} (hab : a < z.cutoff) :
    sourceResidual w z=sourceResidual w (rebase z a)+intervalResidual w z a := by
  unfold sourceResidual intervalResidual
  simp only [rebase]
  rw [highPrime_sum_split hw hab z.closed]
  ring

theorem rebase_invariants {z : Node} (hs : Valid z.side z.ratio) (hr : 0 < z.gap) (hz : Consistent z)
    {a : ℝ} (ha : 0 < a) (hab : a ≤ z.cutoff) :
    Valid (rebase z a).side (rebase z a).ratio ∧ Consistent (rebase z a) := by
  have hb : 0 < z.cutoff := ha.trans_le hab
  have hrat := ratio_eq_gap_div_cutoff hs hz hb
  have hdiv := div_le_div_of_nonneg_left hr.le ha hab
  rw [← hrat] at hdiv
  constructor
  · change Valid z.side (z.gap/a)
    cases hi : z.side <;> simp only [hi,Valid] at hs ⊢ <;> linarith
  · change a=z.gap/(z.gap/a)
    field_simp

end NumberTheoryLean.ReferenceIntervalCutoff

end

section

namespace NumberTheoryLean.ReferenceIntervalErrors

open _root_.Finset _root_.Set _root_.MeasureTheory
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceBenchmarkDecay ReferenceDifferentiation ReferenceCancellation ReferenceWeightDomination
open ReferenceMertens ReferenceResidualErrors ReferenceIntervalCutoff
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def lowerProductError (w : ℝ) (z : Node) (a : ℝ) : ℝ :=
  (referenceProduct w a true-normalization w/a)*(parentBenchmark z.side (z.gap/a)-1)

noncomputable def intervalPrimeError (w : ℝ) (z : Node) (a : ℝ) : ℝ :=
  ∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹*
    (referenceProduct w (primeExponent w p) false-normalization w/primeExponent w p)*
    (benchmark z.side.flip (childRatio w z.gap p)-1)

noncomputable def intervalQuadratureError (w : ℝ) (z : Node) (a : ℝ) : ℝ :=
  (∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹*
    (benchmark z.side.flip (childRatio w z.gap p)-1)/primeExponent w p)-
  ∫ x in primeInterval a z.cutoff z.closed,(benchmark z.side.flip (z.gap/x-1)-1)/x^2

theorem continuous_interval_cancellation (i : Side) {r a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hs : ParentDomain i (r/b)) :
    (parentBenchmark i (r/a)-1)/a-(parentBenchmark i (r/b)-1)/b-
      (∫ x in a..b,(benchmark i.flip (r/x-1)-1)/x^2)=0 := by
  have hb : 2 ≤ b := ha.trans hab
  have hi : IntervalIntegrable (fun x => (benchmark i.flip (r/x-1)-1)/x^2) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro x hx
    exact (prospective_integrand_continuousAt i (by linarith [hx.1])
      (parent_domain_interval i hb hs ⟨ha.trans hx.1,hx.2⟩)).continuousWithinAt
  have hd : ∀ x ∈ uIcc a b,HasDerivAt (fun t => (parentBenchmark i (r/t)-1)/t)
      (-(benchmark i.flip (r/x-1)-1)/x^2) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact reference_derivative i (by linarith [hx.1]) (parent_domain_interval i hb hs ⟨ha.trans hx.1,hx.2⟩)
  have hin : IntervalIntegrable (fun x => -(benchmark i.flip (r/x-1)-1)/x^2) volume a b := by
    convert! hi.neg using 1
    funext x
    exact neg_div _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hin
  simp_rw [neg_div] at h
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem normalized_interval_zero (w : ℝ) {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    {a : ℝ} (ha : 2 ≤ a) (hab : a ≤ z.cutoff) :
    (normalization w/a)*(parentBenchmark z.side (z.gap/a)-1)-
      (normalization w/z.cutoff)*(parentBenchmark z.side z.ratio-1)-
      normalization w*(∫ x in primeInterval a z.cutoff z.closed,(benchmark z.side.flip (z.gap/x-1)-1)/x^2)=0 := by
  have hr := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hd : ParentDomain z.side (z.gap/z.cutoff) := by rw [← hr]; exact valid_parent_domain hs
  have hc := continuous_interval_cancellation z.side ha hab hd
  rw [← hr] at hc
  rw [primeInterval_integral hab]
  have hm := congrArg (fun t : ℝ => normalization w*t) hc
  convert! hm using 1 <;> ring

theorem interval_error_identity (w : ℝ) {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    {a : ℝ} (ha : 2 ≤ a) (hab : a ≤ z.cutoff) :
    intervalResidual w z a=lowerProductError w z a-parentProductError w z-intervalPrimeError w z a-
      normalization w*intervalQuadratureError w z a := by
  have hc := normalized_interval_zero w hs hz ha hab
  have hp : (∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
      (benchmark z.side.flip (childRatio w z.gap p)-1))=
    intervalPrimeError w z a+normalization w*(∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹*
      (benchmark z.side.flip (childRatio w z.gap p)-1)/primeExponent w p) := by
    rw [intervalPrimeError,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  unfold intervalResidual lowerProductError parentProductError intervalQuadratureError
  rw [hp]
  nlinarith

end NumberTheoryLean.ReferenceIntervalErrors

end

section

namespace NumberTheoryLean.ReferenceIntervalProductBounds

open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceMertens ReferenceSourcePrimeSets ReferenceBenchmarkDecay ReferenceDifferentiation
open ReferenceResidualErrors ReferenceProductErrorBounds ReferenceIntervalCutoff ReferenceIntervalErrors ReferenceParentMonotonicity
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem finite_interval_product_bounds {c C w : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hw : 1 < w)
    (hP : ∀ t : ℝ,2 ≤ t → ∀ closed : Bool,
      |referenceProduct w t closed-normalization w/t| ≤ (C/t)*primeError c w t)
    {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z) {a : ℝ} (ha : 2 ≤ a) (hab : a ≤ z.cutoff) :
    |lowerProductError w z a| ≤ 2*C*weight z.side z.ratio*primeError c w a ∧
    |parentProductError w z| ≤ 2*C*weight z.side z.ratio*primeError c w a ∧
    |intervalPrimeError w z a| ≤ (2*C*weight z.side z.ratio*primeError c w a)*
      (∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹) := by
  have hφ := weight_pos hs
  have hE := primeError_pos c w a
  have hr := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hs' : Valid z.side (z.gap/z.cutoff) := by rwa [← hr]
  have hD := interval_deviations_bound z.side ha hab hs' ⟨hab,le_rfl⟩
  rw [← hr] at hD
  have hparent : |parentBenchmark z.side z.ratio-1| ≤ 4*weight z.side z.ratio := by
    linarith [abs_nonneg (parentBenchmark z.side (z.gap/a)-1),abs_nonneg (benchmark z.side.flip (z.ratio-1)-1)]
  have hlower : |parentBenchmark z.side (z.gap/a)-1| ≤ 4*weight z.side z.ratio := by
    linarith [abs_nonneg (parentBenchmark z.side z.ratio-1),abs_nonneg (benchmark z.side.flip (z.ratio-1)-1)]
  have hscale : ∀ t : ℝ,a ≤ t → ∀ closed : Bool,
      |referenceProduct w t closed-normalization w/t| ≤ (C/2)*primeError c w a := by
    intro t ht closed
    apply (hP t (ha.trans ht) closed).trans
    exact mul_le_mul (div_le_div_of_nonneg_left hC (by norm_num) (ha.trans ht))
      (primeError_antitone hc hw ht) (primeError_pos _ _ _).le (by positivity)
  constructor
  · unfold lowerProductError
    rw [abs_mul]
    have h := mul_le_mul (hscale a le_rfl true) hlower (abs_nonneg _) (by positivity)
    convert! h using 1
    ring
  constructor
  · unfold parentProductError
    rw [abs_mul]
    have h := mul_le_mul (hscale z.cutoff hab z.closed) hparent (abs_nonneg _) (by positivity)
    convert! h using 1
    ring
  · unfold intervalPrimeError
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpH := (Finset.mem_filter.mp hp).1
    have hxa : a ≤ primeExponent w p := (Finset.mem_filter.mp hp).2.le
    obtain ⟨_hprime,_hxp,hcap⟩ := (highPrimes_membership hw z.cutoff z.closed p).mp hpH
    have hxb : primeExponent w p ≤ z.cutoff := by
      cases hcl : z.closed with
      | false => have h : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
                 exact h.le
      | true => simpa [capGuard,hcl] using hcap
    have hchild0 := interval_deviations_bound z.side ha hab hs' ⟨hxa,hxb⟩
    rw [← hr] at hchild0
    have hchild : |benchmark z.side.flip (childRatio w z.gap p)-1| ≤ 4*weight z.side z.ratio := by
      unfold childRatio
      linarith [abs_nonneg (parentBenchmark z.side z.ratio-1),abs_nonneg (parentBenchmark z.side (z.gap/a)-1)]
    rw [abs_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
    have hleft := mul_le_mul_of_nonneg_left (hscale (primeExponent w p) hxa false)
      (inv_nonneg.mpr (Nat.cast_nonneg p))
    have h := mul_le_mul hleft hchild (abs_nonneg _) (by positivity)
    convert! h using 1
    ring

end NumberTheoryLean.ReferenceIntervalProductBounds

end

section

namespace NumberTheoryLean.ReferenceIntervalQuadrature

open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceProductErrorBounds ReferenceResidualErrors ReferenceIntervalCutoff ReferenceIntervalErrors
open ReferenceWeightedQuadrature

theorem actual_interval_quadrature : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ z : Node,Valid z.side z.ratio → Consistent z →
      ∀ a : ℝ,2 ≤ a → a ≤ z.cutoff →
      |intervalQuadratureError w z a| ≤ (C*weight z.side z.ratio/2)*primeError c w a := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := source_weighted_quadrature
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw z hs hz a ha hab
  have hw1 : 1 < w := hw₀.trans_le hw
  have hr := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hs' : Valid z.side (z.gap/z.cutoff) := by rwa [← hr]
  have hh := h w hw a z.cutoff z.cutoff z.gap ha hab le_rfl z.side hs'
    (primeInterval a z.cutoff z.closed) (primeInterval_orderConnected _ _ _) (primeInterval_subset _ _ _)
  rw [← hr] at hh
  have hφ := weight_pos hs
  have hl : C*weight z.side z.ratio/a ≤ C*weight z.side z.ratio/2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) ha
  unfold intervalQuadratureError
  rw [intervalPrime_sum hw1 ha]
  apply le_trans (by simpa only [childRatio] using hh)
  exact mul_le_mul_of_nonneg_right hl (primeError_pos _ _ _).le

end NumberTheoryLean.ReferenceIntervalQuadrature

end

section

namespace NumberTheoryLean.ReferenceIntervalBound

open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership
open ReferenceSourcePrimeSets ReferenceMertens ReferenceProductErrors ReferenceLocalResidual ReferenceHighIntervals
open ReferenceResidualErrors ReferenceProductErrorBounds ReferenceIntervalCutoff ReferenceIntervalErrors
open ReferenceIntervalProductBounds ReferenceIntervalQuadrature

theorem interval_abs_triangle (w : ℝ) {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    {a : ℝ} (ha : 2 ≤ a) (hab : a ≤ z.cutoff) :
    |intervalResidual w z a| ≤ |lowerProductError w z a|+|parentProductError w z|+
      |intervalPrimeError w z a|+|normalization w*intervalQuadratureError w z a| := by
  rw [interval_error_identity w hs hz ha hab]
  have h1 := abs_sub (lowerProductError w z a-parentProductError w z-intervalPrimeError w z a)
    (normalization w*intervalQuadratureError w z a)
  have h2 := abs_sub (lowerProductError w z a-parentProductError w z) (intervalPrimeError w z a)
  have h3 := abs_sub (lowerProductError w z a) (parentProductError w z)
  linarith

theorem actual_interval_residual_bound : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ z : Node,Valid z.side z.ratio → Consistent z →
      ∀ a : ℝ,2 ≤ a → a ≤ z.cutoff →
      |intervalResidual w z a| ≤ C*weight z.side z.ratio*(1+Real.log z.cutoff)*primeError c w a := by
  obtain ⟨cP,CP,wP,hcP,hCP,hwP,hP⟩ := reference_product_absolute
  obtain ⟨cQ,CQ,wQ,hcQ,hCQ,_hwQ,hQ⟩ := actual_interval_quadrature
  obtain ⟨CH,wH,hCH,_hwH,hH⟩ := highPrime_mass_bound
  let c := min cP cQ
  let C := 4*CP+2*CP*CH+CQ
  have hc : 0 < c := lt_min hcP hcQ
  refine ⟨c,C,max wP (max wQ wH),hc,by dsimp [C]; positivity,hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw z hs hz a ha hab
  have hwp : wP ≤ w := (le_max_left _ _).trans hw
  have hwq : wQ ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwh : wH ≤ w := ((le_max_right _ _).trans (le_max_right _ _)).trans hw
  have hw1 : 1 < w := hwP.trans_le hwp
  obtain ⟨_hNlo,hNhi,hProd⟩ := hP w hwp
  have hP' : ∀ t : ℝ,2 ≤ t → ∀ closed : Bool,
      |referenceProduct w t closed-normalization w/t| ≤ (CP/t)*primeError c w t := by
    intro t ht closed
    exact (hProd t ht closed).trans (mul_le_mul_of_nonneg_left
      (exp_error_mono_rate (t:=t*Real.log w) (min_le_left cP cQ)) (by positivity))
  obtain ⟨hLow,hPar,hPrime⟩ := finite_interval_product_bounds hc.le hCP.le hw1 hP' hs hz ha hab
  have hφ := weight_pos hs
  have hE := primeError_pos c w a
  have hQ' : |intervalQuadratureError w z a| ≤ (CQ*weight z.side z.ratio/2)*primeError c w a := by
    exact (hQ w hwq z hs hz a ha hab).trans (mul_le_mul_of_nonneg_left
      (exp_error_mono_rate (t:=a*Real.log w) (min_le_right cP cQ)) (by positivity))
  have hN : |normalization w| ≤ 2 := by rw [abs_of_pos (normalization_pos hw1)]; exact hNhi
  have hNQ : |normalization w*intervalQuadratureError w z a| ≤ CQ*weight z.side z.ratio*primeError c w a := by
    rw [abs_mul]
    have hh := mul_le_mul hN hQ' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    convert! hh using 1
    ring
  have hMass : (∑ p ∈ intervalPrimes w a z.cutoff z.closed,(p:ℝ)⁻¹) ≤ CH*(1+Real.log z.cutoff) := by
    apply le_trans _ (hH w hwh z.cutoff (ha.trans hab) z.closed)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p _ _ => by positivity)
  have hPrime' : |intervalPrimeError w z a| ≤
      (2*CP*weight z.side z.ratio*primeError c w a)*(CH*(1+Real.log z.cutoff)) :=
    hPrime.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have htri := interval_abs_triangle w hs hz ha hab
  have hL : 1 ≤ 1+Real.log z.cutoff := by
    have hh := Real.log_nonneg (show 1 ≤ z.cutoff by linarith)
    linarith
  have hpay : (4*CP+CQ)*weight z.side z.ratio*primeError c w a ≤
      (4*CP+CQ)*weight z.side z.ratio*primeError c w a*(1+Real.log z.cutoff) :=
    le_mul_of_one_le_right (by positivity) hL
  calc
    _ ≤ (4*CP+CQ)*weight z.side z.ratio*primeError c w a+
      (2*CP*weight z.side z.ratio*primeError c w a)*(CH*(1+Real.log z.cutoff)) := by
        nlinarith only [htri,hLow,hPar,hPrime',hNQ]
    _ ≤ (4*CP+CQ)*weight z.side z.ratio*primeError c w a*(1+Real.log z.cutoff)+
      (2*CP*weight z.side z.ratio*primeError c w a)*(CH*(1+Real.log z.cutoff)) := add_le_add_left hpay _
    _ = _ := by dsimp [C]; ring

theorem source_residual_split_bound : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ z : Node,Valid z.side z.ratio → Consistent z →
      ∀ a : ℝ,2 ≤ a → a < z.cutoff →
      |sourceResidual w z| ≤ |sourceResidual w (rebase z a)|+
        C*weight z.side z.ratio*(1+Real.log z.cutoff)*primeError c w a := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := actual_interval_residual_bound
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw z hs hz a ha hab
  rw [residual_split (hw₀.trans_le hw) z hab]
  exact (abs_add_le _ _).trans (add_le_add_right (h w hw z hs hz a ha hab.le) _)

end NumberTheoryLean.ReferenceIntervalBound

end

end Erdos970

end OAI
