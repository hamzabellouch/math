import OAI.NumberTheory.Jacobsthal.Partitions.ReferenceHighIntervals

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.WeightDistantDecay

open FinitePathGeometry DerivativeWeights WeightDickmanComparison TwoStepDensityBounds
open Dickman DickmanDecay DickmanFiniteDecay

theorem sided_rho_bounds : ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ i : Side,∀ s : ℝ,2 ≤ s →
    c*rho (s-2) ≤ weight i s ∧ weight i s ≤ C*rho (s-2) := by
  obtain ⟨c,C,hc,hC,h⟩ := weights_dickman_bounds
  refine ⟨c,C,hc,hC,?_⟩
  intro i s hs
  cases i with
  | even => exact (h s hs).1
  | odd => exact (h s hs).2

theorem compact_weight_lower : ∃ m : ℝ,0 < m ∧ ∀ i s,Valid i s → s ≤ 4 → m ≤ weight i s := by
  let m := min (weight .even 4) (weight .odd 4)
  have he : 0 < weight .even 4 := weight_pos (valid_of_three_le .even (by norm_num))
  have ho : 0 < weight .odd 4 := weight_pos (valid_of_three_le .odd (by norm_num))
  refine ⟨m,lt_min he ho,?_⟩
  intro i s hs hs4
  have hm : m ≤ weight i 4 := by cases i; exact min_le_left _ _; exact min_le_right _ _
  exact hm.trans (weight_antitone hs (valid_of_three_le i (by norm_num)) hs4)

theorem rho_one_rate {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    rho b ≤ rho a*Real.exp (-(b-a)) := by
  simpa only [one_mul,neg_mul] using
    rho_exponential_comparison 2 1 a b le_rfl (fun t ht => hazard_ge_one ht) ha hab

theorem relative_weight_decay : ∃ C : ℝ,0 < C ∧ ∀ i j : Side,∀ s t : ℝ,
    Valid i s → s+4 ≤ t → weight j t ≤ C*weight i s*Real.exp (-(t-s)/2) := by
  obtain ⟨c₀,C₀,hc₀,hC₀,hρ⟩ := sided_rho_bounds
  obtain ⟨m,hm,hmLower⟩ := compact_weight_lower
  let CL := C₀/c₀
  let CS := C₀*Real.exp 4/m
  have hCL : 0 < CL := div_pos hC₀ hc₀
  have hCS : 0 < CS := div_pos (mul_pos hC₀ (Real.exp_pos _)) hm
  refine ⟨max CL CS,hCL.trans_le (le_max_left _ _),?_⟩
  intro i j s t hs hst
  have hs0 := valid_pos hs
  have ht4 : 4 ≤ t := by linarith
  have ht2 : 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hwt := (hρ j t ht2).2
  have hφ := weight_pos hs
  by_cases hs4 : 4 ≤ s
  · have hcomp := rho_one_rate (a:=s-2) (b:=t-2) (by linarith) (by linarith)
    have hlow := (hρ i s (by linarith)).1
    have hdiv : rho (s-2) ≤ weight i s/c₀ := (le_div_iff₀ hc₀).mpr (by nlinarith)
    have he : Real.exp (-((t-2)-(s-2))) ≤ Real.exp (-(t-s)/2) := Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ C₀*rho (t-2) := hwt
      _ ≤ C₀*(rho (s-2)*Real.exp (-((t-2)-(s-2)))) := mul_le_mul_of_nonneg_left hcomp hC₀.le
      _ ≤ C₀*((weight i s/c₀)*Real.exp (-(t-s)/2)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul hdiv he (Real.exp_pos _).le (by positivity)) hC₀.le
      _ = CL*weight i s*Real.exp (-(t-s)/2) := by dsimp [CL]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left CL CS) hφ.le) (Real.exp_pos _).le
  · have hs4' : s ≤ 4 := le_of_lt (lt_of_not_ge hs4)
    have hmin := hmLower i s hs hs4'
    have hcomp := rho_one_rate (a:=2) (b:=t-2) le_rfl (by linarith)
    have hbound : rho (t-2) ≤ Real.exp 4*Real.exp (-(t-s)/2) := by
      calc
        _ ≤ rho 2*Real.exp (-((t-2)-2)) := hcomp
        _ ≤ Real.exp (-((t-2)-2)) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (rho_le_one 2) (Real.exp_pos _).le
        _ ≤ _ := by rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
    have hcoeff : C₀*Real.exp 4 ≤ CS*weight i s := by
      calc
        _ = CS*m := by dsimp [CS]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hmin hCS.le
    calc
      _ ≤ C₀*rho (t-2) := hwt
      _ ≤ C₀*(Real.exp 4*Real.exp (-(t-s)/2)) := mul_le_mul_of_nonneg_left hbound hC₀.le
      _ ≤ CS*weight i s*Real.exp (-(t-s)/2) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right CL CS) hφ.le) (Real.exp_pos _).le

theorem weight_exponential_majorant (rate : ℝ) : ∃ C T : ℝ,0 < C ∧ 4 ≤ T ∧
    ∀ i : Side,∀ t : ℝ,T ≤ t → weight i t ≤ C*Real.exp (-rate*t) := by
  obtain ⟨_c,C₀,_hc,hC₀,hρ⟩ := sided_rho_bounds
  obtain ⟨A,hA,T,hT,h⟩ := rho_exponential_majorant rate
  refine ⟨C₀*A*Real.exp (2*rate),T+2,by positivity,by linarith,?_⟩
  intro i t ht
  have hr := h (t-2) (by linarith)
  calc
    _ ≤ C₀*rho (t-2) := (hρ i t (by linarith)).2
    _ ≤ C₀*(A*Real.exp (-rate*(t-2))) := mul_le_mul_of_nonneg_left hr hC₀.le
    _ = _ := by rw [show -rate*(t-2)=2*rate+(-rate*t) by ring,Real.exp_add]; ring

end NumberTheoryLean.WeightDistantDecay



namespace NumberTheoryLean.ReferenceResidualErrors

open _root_.Finset _root_.MeasureTheory
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry ActualBoundaryDomain
open ReferenceBenchmarkDecay ReferenceDifferentiation ReferenceCancellation ReferenceWeightDomination
open ReferenceSourcePrimeSets ReferenceMertens ReferenceLocalResidual ReferenceHighIntervals
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem ratio_eq_gap_div_cutoff {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hb : 0 < z.cutoff) : z.ratio=z.gap/z.cutoff := by
  have he := (eq_div_iff (ne_of_gt (valid_pos hs))).mp hz
  apply (eq_div_iff (ne_of_gt hb)).mpr
  nlinarith

theorem boundary_parent_eq (i : Side) {r : ℝ} (hr : BoundaryDomain i r) :
    parentBenchmark i (r/2)=benchmark i (r/2) := by
  cases i with
  | even => exact parent_even_eq_ordinary (by change 4 ≤ r at hr; linarith)
  | odd => rfl

noncomputable def boundaryProductError (w : ℝ) (z : Node) : ℝ :=
  (referenceProduct w 2 true-normalization w/2)*(benchmark z.side (z.gap/2)-1)

noncomputable def parentProductError (w : ℝ) (z : Node) : ℝ :=
  (referenceProduct w z.cutoff z.closed-normalization w/z.cutoff)*(parentBenchmark z.side z.ratio-1)

noncomputable def primeProductError (w : ℝ) (z : Node) : ℝ :=
  ∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*
    (referenceProduct w (primeExponent w p) false-normalization w/primeExponent w p)*
    (benchmark z.side.flip (childRatio w z.gap p)-1)

noncomputable def quadratureError (w : ℝ) (z : Node) : ℝ :=
  (∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*
    (benchmark z.side.flip (childRatio w z.gap p)-1)/primeExponent w p)-
  ∫ x in highInterval z.cutoff z.closed,(benchmark z.side.flip (z.gap/x-1)-1)/x^2

theorem actual_continuous_zero (w : ℝ) {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hb : 2 ≤ z.cutoff) (hdom : BoundaryDomain z.side z.gap) :
    (normalization w/2)*(benchmark z.side (z.gap/2)-1)-
      (normalization w/z.cutoff)*(parentBenchmark z.side z.ratio-1)-
      normalization w*(∫ x in highInterval z.cutoff z.closed,(benchmark z.side.flip (z.gap/x-1)-1)/x^2)=0 := by
  have hr := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hd : ParentDomain z.side (z.gap/z.cutoff) := by rw [← hr]; exact valid_parent_domain hs
  have hc := continuous_reference_cancellation z.side hb hd
  rw [boundary_parent_eq z.side hdom,← hr] at hc
  rw [highInterval_integral hb]
  have hm := congrArg (fun t : ℝ => normalization w*t) hc
  convert! hm using 1 <;> ring

theorem residual_error_identity (w : ℝ) {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hb : 2 ≤ z.cutoff) (hdom : BoundaryDomain z.side z.gap) :
    sourceResidual w z=boundaryProductError w z-parentProductError w z-primeProductError w z-
      normalization w*quadratureError w z := by
  have hc := actual_continuous_zero w hs hz hb hdom
  have hp : (∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false*
        (benchmark z.side.flip (childRatio w z.gap p)-1))=
      primeProductError w z+normalization w*(∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹*
        (benchmark z.side.flip (childRatio w z.gap p)-1)/primeExponent w p) := by
    rw [primeProductError,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  unfold sourceResidual boundaryProductError parentProductError quadratureError
  rw [hp]
  nlinarith

end NumberTheoryLean.ReferenceResidualErrors



namespace NumberTheoryLean.ReferenceProductErrorBounds

open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceMertens ReferenceSourcePrimeSets ReferenceBenchmarkDecay ReferenceDifferentiation
open ReferenceWeightDomination ReferenceResidualErrors
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def primeError (c w t : ℝ) : ℝ := Real.exp (-c*Real.sqrt (t*Real.log w))

theorem primeError_pos (c w t : ℝ) : 0 < primeError c w t := Real.exp_pos _

theorem primeError_antitone {c w t s : ℝ} (hc : 0 ≤ c) (hw : 1 < w) (hts : t ≤ s) :
    primeError c w s ≤ primeError c w t := by
  apply Real.exp_le_exp.mpr
  have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hts (Real.log_pos hw).le)
  nlinarith

theorem divided_error_bound {c C w t : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hw : 1 < w) (ht : 2 ≤ t) :
    (C/t)*primeError c w t ≤ (C/2)*primeError c w 2 := by
  apply mul_le_mul (div_le_div_of_nonneg_left hC (by norm_num : (0:ℝ)<2) ht)
    (primeError_antitone hc hw ht) (primeError_pos _ _ _).le (by positivity)

theorem finite_product_error_bounds {c C w : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hw : 1 < w)
    (hP : ∀ t : ℝ,2 ≤ t → ∀ closed : Bool,
      |referenceProduct w t closed-normalization w/t| ≤ (C/t)*primeError c w t)
    {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z) (hb : 2 ≤ z.cutoff) :
    |boundaryProductError w z| ≤ 2*C*weight z.side z.ratio*primeError c w 2 ∧
    |parentProductError w z| ≤ 2*C*weight z.side z.ratio*primeError c w 2 ∧
    |primeProductError w z| ≤ (2*C*weight z.side z.ratio*primeError c w 2)*
      (∑ p ∈ highPrimes w z.cutoff z.closed,(p:ℝ)⁻¹) := by
  have hφ := weight_pos hs
  have hE := primeError_pos c w 2
  have hr := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hs' : Valid z.side (z.gap/z.cutoff) := by rwa [← hr]
  have hD := residual_deviations_bound z.side hb hs' ⟨hb,le_rfl⟩
  rw [← hr] at hD
  have hparent : |parentBenchmark z.side z.ratio-1| ≤ 4*weight z.side z.ratio := by
    linarith [abs_nonneg (benchmark z.side (z.gap/2)-1),abs_nonneg (benchmark z.side.flip (z.ratio-1)-1)]
  have hboundary : |benchmark z.side (z.gap/2)-1| ≤ 4*weight z.side z.ratio := by
    linarith [abs_nonneg (parentBenchmark z.side z.ratio-1),abs_nonneg (benchmark z.side.flip (z.ratio-1)-1)]
  have hscale : ∀ t : ℝ,2 ≤ t → ∀ closed : Bool,
      |referenceProduct w t closed-normalization w/t| ≤ (C/2)*primeError c w 2 := by
    intro t ht closed
    exact (hP t ht closed).trans (divided_error_bound hc hC hw ht)
  constructor
  · unfold boundaryProductError
    rw [abs_mul]
    have h := mul_le_mul (hscale 2 le_rfl true) hboundary (abs_nonneg _) (by positivity)
    convert! h using 1
    ring
  constructor
  · unfold parentProductError
    rw [abs_mul]
    have h := mul_le_mul (hscale z.cutoff hb z.closed) hparent (abs_nonneg _) (by positivity)
    convert! h using 1
    ring
  · unfold primeProductError
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨_hprime,hxp,hcap⟩ := (highPrimes_membership hw z.cutoff z.closed p).mp hp
    have hxb : primeExponent w p ≤ z.cutoff := by
      cases hcl : z.closed with
      | false => have h : primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
                 exact h.le
      | true => simpa [capGuard,hcl] using hcap
    have hchild0 := residual_deviations_bound z.side hb hs' ⟨hxp.le,hxb⟩
    rw [← hr] at hchild0
    have hchild : |benchmark z.side.flip (childRatio w z.gap p)-1| ≤ 4*weight z.side z.ratio := by
      unfold childRatio
      linarith [abs_nonneg (parentBenchmark z.side z.ratio-1),abs_nonneg (benchmark z.side (z.gap/2)-1)]
    rw [abs_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
    have hleft := mul_le_mul_of_nonneg_left (hscale (primeExponent w p) hxp.le false)
      (inv_nonneg.mpr (Nat.cast_nonneg p))
    have h := mul_le_mul hleft hchild (abs_nonneg _) (by positivity)
    convert! h using 1
    ring

end NumberTheoryLean.ReferenceProductErrorBounds



namespace NumberTheoryLean.GlobalResidualScale

open ReferenceProductErrorBounds

noncomputable def powerDecay (M B : ℝ) : ℝ := Real.exp (-M*Real.log B)

theorem powerDecay_pos (M B : ℝ) : 0 < powerDecay M B := Real.exp_pos _

theorem primeError_le_one {c : ℝ} (hc : 0 ≤ c) (w t : ℝ) : primeError c w t ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (Real.sqrt_nonneg _))

theorem powerDecay_nat {B : ℝ} (hB : 0 < B) (n : ℕ) : powerDecay n B=(B^n)⁻¹ := by
  rw [powerDecay,neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hB]

theorem linear_log_cutoff_saving {c d M : ℝ} (hc : 0 < c) (hd : 0 < d) (hM : 0 < M) :
    ∃ K : ℝ,1 ≤ K ∧ ∀ B w : ℝ,1 ≤ B → 1 < w → Real.log B ≤ d*Real.log w →
      primeError c w (K*Real.log B) ≤ powerDecay M B := by
  let q := M/c
  let K := 1+d*q^2
  have hq : 0 < q := div_pos hM hc
  have hK : 1 ≤ K := by dsimp [K]; exact le_add_of_nonneg_right (mul_nonneg hd.le (sq_nonneg q))
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨K,hK,?_⟩
  intro B w hB hw hcomp
  have hL : 0 ≤ Real.log B := Real.log_nonneg hB
  have hW : 0 ≤ Real.log w := (Real.log_pos hw).le
  have hm := mul_le_mul_of_nonneg_left hcomp (mul_nonneg (sq_nonneg q) hL)
  have hsquare : (q*Real.log B)^2 ≤ (K*Real.log B)*Real.log w := by
    dsimp only [K]
    nlinarith only [hm,mul_nonneg hL hW]
  have harg : 0 ≤ (K*Real.log B)*Real.log w := by positivity
  have hsqrt : q*Real.log B ≤ Real.sqrt ((K*Real.log B)*Real.log w) := by
    nlinarith only [hsquare,Real.sq_sqrt harg,Real.sqrt_nonneg ((K*Real.log B)*Real.log w),mul_nonneg hq.le hL]
  have hcq : c*q=M := by dsimp [q]; field_simp
  have hpay : M*Real.log B ≤ c*Real.sqrt ((K*Real.log B)*Real.log w) := by
    calc
      _ = c*(q*Real.log B) := by rw [← mul_assoc,hcq]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt hc.le
  change Real.exp (-c*Real.sqrt ((K*Real.log B)*Real.log w)) ≤ Real.exp (-M*Real.log B)
  exact Real.exp_le_exp.mpr (by linarith)

theorem rebased_ratio_separation {K M L s b : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hLK : K ≤ L) (hLM : 4*M+10 ≤ L) (hs : (1/2:ℝ) ≤ s) (hb : L^4 < b) :
    s+4 ≤ (b*s)/(K*L) ∧ 2*M*L ≤ (b*s)/(K*L)-s := by
  have hL : 1 ≤ L := hK.trans hLK
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have ha : 0 < K*L := mul_pos hK0 hL0
  have hcoef : (K*L)*L^2 ≤ b := by
    have hh := mul_le_mul_of_nonneg_right hLK (pow_nonneg hL0.le 3)
    nlinarith
  have hratio : L^2 ≤ b/(K*L) := (le_div_iff₀ ha).mpr (by nlinarith)
  have ht : s*L^2 ≤ (b*s)/(K*L) := by
    have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ s by linarith)
    convert! hh using 1
    ring
  have hdiff : (L^2-1)/2 ≤ (b*s)/(K*L)-s := by
    have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ L^2-1 by nlinarith)
    nlinarith
  have hpoly : 2*M*L ≤ (L^2-1)/2 ∧ 4 ≤ (L^2-1)/2 := by
    have hh := mul_nonneg hL0.le (show 0 ≤ L-(4*M+10) by linarith)
    constructor <;> nlinarith
  exact ⟨by linarith [hpoly.2],hpoly.1.trans hdiff⟩

theorem gap_over_linear_cutoff {K L r b : ℝ} (hK : 0 < K) (hL : 0 ≤ L) (hb : 0 < b)
    (hbK : b ≤ K*L) (hr : L^2/2 ≤ r) : L/(2*K) ≤ r/b := by
  apply (le_div_iff₀ hb).mpr
  have hm := mul_le_mul_of_nonneg_left hbK (div_nonneg hL (by positivity : 0 ≤ 2*K))
  have he : L/(2*K)*(K*L)=L^2/2 := by field_simp
  rw [he] at hm
  exact hm.trans hr

end NumberTheoryLean.GlobalResidualScale



namespace NumberTheoryLean.ReferenceLogScale

open _root_.Filter
open scoped Topology
open ReferenceProductErrorBounds ExponentialMesh

theorem primeError_two_eq (c w : ℝ) :
    primeError c w 2=Real.exp (-(c*Real.sqrt 2)*Real.sqrt (Real.log w)) := by
  unfold primeError
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem log_power_primeError_tendsto (C : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun w : ℝ => C*(Real.log w)^n*primeError c w 2) atTop (𝓝 0) := by
  have h := log_power_exp_tendsto C n (mul_pos hc (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  simpa only [primeError_two_eq] using h

theorem primeError_two_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun w : ℝ => primeError c w 2) atTop (𝓝 0) := by
  simpa only [pow_zero,one_mul] using log_power_primeError_tendsto 1 0 hc

end NumberTheoryLean.ReferenceLogScale



namespace NumberTheoryLean.ReferenceResidualQuadrature

open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry
open ReferenceMertens ReferenceResidualErrors ReferenceProductErrorBounds ReferenceHighIntervals
open ReferenceWeightedQuadrature

theorem actual_quadrature_error : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ z : Node,Valid z.side z.ratio → Consistent z → 2 ≤ z.cutoff →
      |quadratureError w z| ≤ (C*weight z.side z.ratio/2)*primeError c w 2 := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := source_weighted_quadrature
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw z hs hz hb
  have hw1 : 1 < w := hw₀.trans_le hw
  have hr := ratio_eq_gap_div_cutoff hs hz (by linarith)
  have hs' : Valid z.side (z.gap/z.cutoff) := by rwa [← hr]
  have hh := h w hw 2 z.cutoff z.cutoff z.gap le_rfl hb le_rfl z.side hs'
    (highInterval z.cutoff z.closed) (highInterval_orderConnected _ _) (highInterval_subset _ _)
  rw [← hr] at hh
  unfold quadratureError
  rw [highPrime_sum hw1]
  simpa only [childRatio,primeError] using hh

end NumberTheoryLean.ReferenceResidualQuadrature



namespace NumberTheoryLean.WeightPowerBounds

open FinitePathGeometry WeightDistantDecay GlobalResidualScale

theorem relative_weight_power : ∃ C : ℝ,0 < C ∧ ∀ M B : ℝ,∀ i j : Side,∀ s t : ℝ,
    Valid i s → s+4 ≤ t → 2*M*Real.log B ≤ t-s →
      weight j t ≤ C*weight i s*powerDecay M B := by
  obtain ⟨C,hC,h⟩ := relative_weight_decay
  refine ⟨C,hC,?_⟩
  intro M B i j s t hs hst hgap
  apply (h i j s t hs hst).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (weight_pos hs).le)
  change Real.exp (-(t-s)/2) ≤ Real.exp (-M*Real.log B)
  exact Real.exp_le_exp.mpr (by linarith)

theorem weight_power_at_ratio {K M : ℝ} (hK : 0 < K) (hM : 0 < M) :
    ∃ C T : ℝ,0 < C ∧ 0 < T ∧ ∀ B : ℝ,T ≤ Real.log B → ∀ i : Side,∀ t : ℝ,
      Real.log B/(2*K) ≤ t → weight i t ≤ C*powerDecay M B := by
  obtain ⟨C,T,hC,hT,h⟩ := weight_exponential_majorant (2*K*M)
  refine ⟨C,2*K*T,hC,mul_pos (by positivity) (by linarith),?_⟩
  intro B hB i t ht
  have hTt : T ≤ t := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2*K)).mp ht
    nlinarith
  have hpay : M*Real.log B ≤ (2*K*M)*t := by
    have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ (by positivity : 0 < 2*K)).mp ht) hM.le
    nlinarith only [hh]
  apply (h i t hTt).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  change Real.exp (-(2*K*M)*t) ≤ Real.exp (-M*Real.log B)
  exact Real.exp_le_exp.mpr (by linarith)

end NumberTheoryLean.WeightPowerBounds



namespace NumberTheoryLean.ReferenceProductLower

open _root_.Filter
open scoped Topology
open ReferenceProductsBasics ReferenceMertens ReferenceProductErrors ReferenceProductErrorBounds ReferenceLogScale

theorem reference_product_lower : ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w →
    ∀ b : ℝ,2 ≤ b → ∀ closed : Bool,1/(4*b) ≤ referenceProduct w b closed := by
  obtain ⟨c,C,wP,hc,hC,hwP,hP⟩ := reference_product_strong
  have hdec : Tendsto (fun w => C*primeError c w 2) atTop (𝓝 0) := by
    simpa only [mul_zero] using (primeError_two_tendsto hc).const_mul C
  obtain ⟨wE,hwE⟩ := eventually_atTop.mp (hdec.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2)))
  obtain ⟨wN,hwN⟩ := eventually_atTop.mp normalization_eventually_bounded
  refine ⟨max wP (max wE wN),hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw b hb closed
  have hwp : wP ≤ w := (le_max_left _ _).trans hw
  have hwe : wE ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwn : wN ≤ w := ((le_max_right _ _).trans (le_max_right _ _)).trans hw
  have hw1 : 1 < w := hwP.trans_le hwp
  have hb0 : 0 < b := by linarith
  have hD : 0 < normalization w/b := div_pos (normalization_pos hw1) hb0
  have herr : |referenceProduct w b closed/(normalization w/b)-1| ≤ 1/2 := by
    apply (hP w hwp b hb closed).trans
    apply le_trans (mul_le_mul_of_nonneg_left (primeError_antitone hc.le hw1 hb) hC.le)
    exact hwE w hwe
  have hratio : (1/2:ℝ) ≤ referenceProduct w b closed/(normalization w/b) := by
    have hlow := (abs_le.mp herr).1
    linarith
  have hm := (le_div_iff₀ hD).mp hratio
  have hn := (hwN w hwn).1
  calc
    1/(4*b) = ((1/2:ℝ)/b)/2 := by ring
    _ ≤ (normalization w/b)/2 :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hn hb0.le) (by norm_num)
    _ ≤ referenceProduct w b closed := by linarith

end NumberTheoryLean.ReferenceProductLower



namespace NumberTheoryLean.ReferenceResidualPointwise

open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualBoundaryDomain
open ReferenceSourcePrimeSets ReferenceMertens ReferenceProductErrors ReferenceLocalResidual
open ReferenceResidualErrors ReferenceProductErrorBounds ReferenceResidualQuadrature ReferenceHighIntervals

theorem residual_abs_triangle (w : ℝ) {z : Node} (hs : Valid z.side z.ratio) (hz : Consistent z)
    (hb : 2 ≤ z.cutoff) (hdom : BoundaryDomain z.side z.gap) :
    |sourceResidual w z| ≤ |boundaryProductError w z|+|parentProductError w z|+
      |primeProductError w z|+|normalization w*quadratureError w z| := by
  rw [residual_error_identity w hs hz hb hdom]
  have h1 := abs_sub (boundaryProductError w z-parentProductError w z-primeProductError w z)
    (normalization w*quadratureError w z)
  have h2 := abs_sub (boundaryProductError w z-parentProductError w z) (primeProductError w z)
  have h3 := abs_sub (boundaryProductError w z) (parentProductError w z)
  linarith

theorem source_residual_pointwise : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ z : Node,Valid z.side z.ratio → Consistent z → 2 ≤ z.cutoff →
      BoundaryDomain z.side z.gap →
      |sourceResidual w z| ≤ C*weight z.side z.ratio*(1+Real.log z.cutoff)*primeError c w 2 := by
  obtain ⟨cP,CP,wP,hcP,hCP,hwP,hP⟩ := reference_product_absolute
  obtain ⟨cQ,CQ,wQ,hcQ,hCQ,hwQ,hQ⟩ := actual_quadrature_error
  obtain ⟨CH,wH,hCH,_hwH,hH⟩ := highPrime_mass_bound
  let c := min cP cQ
  let C := 4*CP+2*CP*CH+CQ
  have hc : 0 < c := lt_min hcP hcQ
  refine ⟨c,C,max wP (max wQ wH),hc,by dsimp [C]; positivity,
    hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw z hs hz hb hdom
  have hwp : wP ≤ w := (le_max_left _ _).trans hw
  have hwq : wQ ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwh : wH ≤ w := ((le_max_right _ _).trans (le_max_right _ _)).trans hw
  have hw1 : 1 < w := hwP.trans_le hwp
  obtain ⟨_hNlo,hNhi,hProd⟩ := hP w hwp
  have hP' : ∀ t : ℝ,2 ≤ t → ∀ closed : Bool,
      |referenceProduct w t closed-normalization w/t| ≤ (CP/t)*primeError c w t := by
    intro t ht closed
    have he := exp_error_mono_rate (t:=t*Real.log w) (min_le_left cP cQ)
    exact (hProd t ht closed).trans (mul_le_mul_of_nonneg_left he (div_nonneg hCP.le (by linarith)))
  obtain ⟨hB,hPar,hPrime⟩ := finite_product_error_bounds hc.le hCP.le hw1 hP' hs hz hb
  have hφ := weight_pos hs
  have hQ' : |quadratureError w z| ≤ (CQ*weight z.side z.ratio/2)*primeError c w 2 := by
    have he := exp_error_mono_rate (t:=2*Real.log w) (min_le_right cP cQ)
    exact (hQ w hwq z hs hz hb).trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hN : |normalization w| ≤ 2 := by rw [abs_of_pos (normalization_pos hw1)]; exact hNhi
  have hNQ : |normalization w*quadratureError w z| ≤ CQ*weight z.side z.ratio*primeError c w 2 := by
    rw [abs_mul]
    have hh := mul_le_mul hN hQ' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    convert! hh using 1
    ring
  have hMass := hH w hwh z.cutoff hb z.closed
  have hE := primeError_pos c w 2
  have hPrime' : |primeProductError w z| ≤
      (2*CP*weight z.side z.ratio*primeError c w 2)*(CH*(1+Real.log z.cutoff)) :=
    hPrime.trans (mul_le_mul_of_nonneg_left hMass (by positivity))
  have htri := residual_abs_triangle w hs hz hb hdom
  have hL : 1 ≤ 1+Real.log z.cutoff := by have hh := Real.log_nonneg (show 1 ≤ z.cutoff by linarith); linarith
  have hpay : (4*CP+CQ)*weight z.side z.ratio*primeError c w 2 ≤
      (4*CP+CQ)*weight z.side z.ratio*primeError c w 2*(1+Real.log z.cutoff) :=
    le_mul_of_one_le_right (by positivity) hL
  calc
    _ ≤ (4*CP+CQ)*weight z.side z.ratio*primeError c w 2+
      (2*CP*weight z.side z.ratio*primeError c w 2)*(CH*(1+Real.log z.cutoff)) := by
        nlinarith only [htri,hB,hPar,hPrime',hNQ]
    _ ≤ (4*CP+CQ)*weight z.side z.ratio*primeError c w 2*(1+Real.log z.cutoff)+
      (2*CP*weight z.side z.ratio*primeError c w 2)*(CH*(1+Real.log z.cutoff)) :=
        add_le_add_left hpay _
    _ = _ := by dsimp [C]; ring

end NumberTheoryLean.ReferenceResidualPointwise



namespace NumberTheoryLean.ReferenceResidualSum

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry ActualPrimeHigh ActualBoundaryDomain
open SourceNodeCoordinates ReferenceSourceDecomposition ReferenceResidualPointwise ReferenceProductErrorBounds
open ReferenceLocalResidual TwoStepDensityBounds
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

noncomputable def residualAbsoluteSum (w : ℝ) (start : Node) : ℝ :=
  ∑ ps ∈ uncappedPrefixes w 2 start,prefixWeight ps*|sourceResidual w (terminal w start ps)|

theorem uniform_weight_bound : ∃ W : ℝ,0 < W ∧ ∀ i s,Valid i s → weight i s ≤ W := by
  let W := max (weight .even (baseRatio .even)) (weight .odd (baseRatio .odd))
  refine ⟨W,(weight_pos (baseRatio_valid .even)).trans_le (le_max_left _ _),?_⟩
  intro i s hs
  have h := weight_antitone (baseRatio_valid i) hs (baseRatio_le hs)
  cases i with
  | even => exact h.trans (le_max_left _ _)
  | odd => exact h.trans (le_max_right _ _)

theorem uncapped_cutoff_le {w : ℝ} {z : Node} {ps : List ℕ} (hp : uncappedAllowed w 2 z ps) :
    (terminal w z ps).cutoff ≤ z.cutoff := by
  induction ps generalizing z with
  | nil => exact le_rfl
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    have hcap := (Finset.mem_filter.mp hc).2.2.1
    have hx : ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p ≤ z.cutoff := by
      cases hcl : z.closed with
      | false => have h : ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p < z.cutoff := by simpa [capGuard,hcl] using hcap
                 exact h.le
      | true => simpa [capGuard,hcl] using hcap
    exact (ih (z:=step w z p) ht).trans hx

theorem summed_source_residual_bound : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ B : ℝ,4 ≤ B → ∀ start : Node,
      start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff=B →
      residualAbsoluteSum w start ≤ C*B*(1+Real.log B)*primeError c w 2 := by
  obtain ⟨c,CP,wP,hc,hCP,hwP,hP⟩ := source_residual_pointwise
  obtain ⟨M,wM,hM,_hwM,hMass⟩ := total_prime_prefix_mass
  obtain ⟨W,hW,hWeight⟩ := uniform_weight_bound
  refine ⟨c,CP*W*M,max wP wM,hc,by positivity,hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw B hB start hi h199 h23 hcons hcut
  have hwp : wP ≤ w := (le_max_left _ _).trans hw
  have hwm : wM ≤ w := (le_max_right _ _).trans hw
  have hBpos : 0 < B := by linarith
  obtain ⟨hs,hr,_hgap,_hsize⟩ := source_node_bounds hBpos start hi h199 h23 hcons hcut
  have hcap0 : 2 < start.cutoff := by rw [hcut]; linarith
  have hE := primeError_pos c w 2
  have hL : 0 ≤ 1+Real.log B := by have h := Real.log_nonneg (show 1 ≤ B by linarith); linarith
  have hpoint : ∀ ps ∈ uncappedPrefixes w 2 start,
      |sourceResidual w (terminal w start ps)| ≤ CP*W*(1+Real.log B)*primeError c w 2 := by
    intro ps hp
    have hpA : uncappedAllowed w 2 start ps := (Finset.mem_filter.mp hp).2
    obtain ⟨U,_hU,hpU⟩ := (uncapped_iff_exists_ceiling w 2 start ps).mp hpA
    have hvs := terminal_valid hs hpU
    have hcs := terminal_consistent (by norm_num : (0:ℝ) ≤ 2) hr hs hcons hpU
    have hdom := source_boundary_domain hB le_rfl start hi h199 h23 hcons hcut hpA
    have hlow := uncapped_cutoff_gt_two hcap0 hpA
    have hupp : (terminal w start ps).cutoff ≤ B := by simpa only [hcut] using uncapped_cutoff_le hpA
    have hwt := hWeight _ _ hvs
    have hlog := Real.log_le_log (by linarith : 0 < (terminal w start ps).cutoff) hupp
    have hLt : 0 ≤ 1+Real.log (terminal w start ps).cutoff := by
      have hh := Real.log_nonneg (show 1 ≤ (terminal w start ps).cutoff by linarith)
      linarith
    calc
      _ ≤ CP*weight (terminal w start ps).side (terminal w start ps).ratio*
          (1+Real.log (terminal w start ps).cutoff)*primeError c w 2 := hP w hwp _ hvs hcs hlow.le hdom
      _ ≤ _ := by gcongr
  have htotal : (∑ ps ∈ uncappedPrefixes w 2 start,prefixWeight ps) ≤ M*B := by
    calc
      _ ≤ ∑ ps ∈ decreasingPrefixes (primesBetween (w^(2:ℝ)) (w^start.cutoff)),prefixWeight ps :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun ps _ _ => prefixWeight_nonneg ps)
      _ ≤ M*B := by
        rw [hcut]
        have hh := hMass w hwm 2 B (by norm_num) (by linarith)
        nlinarith [mul_pos hM hBpos]
  calc
    _ ≤ ∑ ps ∈ uncappedPrefixes w 2 start,prefixWeight ps*(CP*W*(1+Real.log B)*primeError c w 2) :=
      Finset.sum_le_sum (fun ps hp => mul_le_mul_of_nonneg_left (hpoint ps hp) (prefixWeight_nonneg ps))
    _ = (∑ ps ∈ uncappedPrefixes w 2 start,prefixWeight ps)*(CP*W*(1+Real.log B)*primeError c w 2) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (M*B)*(CP*W*(1+Real.log B)*primeError c w 2) := mul_le_mul_of_nonneg_right htotal (by positivity)
    _ = _ := by ring

theorem signed_residual_le_absolute (w : ℝ) (start : Node) :
    |residualCorrection w start| ≤ residualAbsoluteSum w start := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro ps _hp
  simp only [abs_mul,abs_of_nonneg (prefixWeight_nonneg ps),abs_pow,abs_neg,abs_one,one_pow,one_mul]
  exact le_rfl

end NumberTheoryLean.ReferenceResidualSum



namespace NumberTheoryLean.ReferenceRelativeError

open FinitePathGeometry PrimeHistories PrimeBinMembership SourceNodeCoordinates
open ReferenceMertens ReferenceProductsBasics ReferenceProductLower ReferenceDifferentiation
open ReferenceLocalResidual ReferenceSourceDecomposition ReferenceResidualSum ReferenceProductErrorBounds
open UniformBoundaryCorrection

theorem source_relative_reference_error (d : ℝ) (hd : 0 < d) :
    ∃ c A C B₀ w₀ : ℝ,0 < c ∧ 0 < A ∧ 0 < C ∧ 0 < B₀ ∧ 1 < w₀ ∧
      ∀ w B : ℝ,w₀ ≤ w → B₀ ≤ B → Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |sourceReference w start/referenceProduct w B start.closed-parentBenchmark .even start.ratio| ≤
          A/B+C*B^2*(1+Real.log B)*primeError c w 2 := by
  obtain ⟨AB,BB,wB,hAB,hBB,hwB,hBoundary⟩ := uniform_boundary_correction_div 2 d le_rfl hd
  obtain ⟨c,CR,wR,hc,hCR,_hwR,hResidual⟩ := summed_source_residual_bound
  obtain ⟨wV,_hwV,hV⟩ := reference_product_lower
  refine ⟨c,4*AB,4*CR,max BB 4,max wB (max wR wV),hc,by positivity,by positivity,
    hBB.trans_le (le_max_left _ _),hwB.trans_le (le_max_left _ _),?_⟩
  intro w B hw hB hcomp start hi h199 h23 hcons hcut
  have hwB' : wB ≤ w := (le_max_left _ _).trans hw
  have hwR' : wR ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwV' : wV ≤ w := ((le_max_right _ _).trans (le_max_right _ _)).trans hw
  have hBB' : BB ≤ B := (le_max_left _ _).trans hB
  have hB4 : 4 ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := by linarith
  have hw1 : 1 < w := hwB.trans_le hwB'
  obtain ⟨hs,hr,_hsize1,_hsize2⟩ := source_node_bounds hBpos start hi h199 h23 hcons hcut
  have hbnd := hBoundary B w hBB' hwB' hcomp start hi h199 h23 hcons hcut
  have hres := (signed_residual_le_absolute w start).trans (hResidual w hwR' B hB4 start hi h199 h23 hcons hcut)
  have hdecomp := actual_reference_decomposition hw1 hs hr hcons (by rw [hcut]; linarith)
  have hab : |sourceReference w start-nodeBenchmark w start| ≤
      AB/B^2+CR*B*(1+Real.log B)*primeError c w 2 := by
    rw [hdecomp]
    exact (abs_add_le _ _).trans (add_le_add hbnd hres)
  have hlow := hV w hwV' B (by linarith) start.closed
  have hVpos : 0 < referenceProduct w B start.closed := availableProduct_pos _ _ _
  have heq : sourceReference w start/referenceProduct w B start.closed-parentBenchmark .even start.ratio=
      (sourceReference w start-nodeBenchmark w start)/referenceProduct w B start.closed := by
    unfold nodeBenchmark
    rw [hi,hcut]
    field_simp
  have hL : 0 ≤ 1+Real.log B := by have h := Real.log_nonneg (show 1 ≤ B by linarith); linarith
  have hE := primeError_pos c w 2
  rw [heq,abs_div,abs_of_pos hVpos]
  calc
    _ ≤ (AB/B^2+CR*B*(1+Real.log B)*primeError c w 2)/referenceProduct w B start.closed :=
      div_le_div_of_nonneg_right hab hVpos.le
    _ ≤ (AB/B^2+CR*B*(1+Real.log B)*primeError c w 2)/(1/(4*B)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlow
    _ = _ := by field_simp

end NumberTheoryLean.ReferenceRelativeError



namespace NumberTheoryLean.MovingLocalReference

open _root_.Filter Asymptotics
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership ReferenceMertens ReferenceDifferentiation
open ReferenceSourceDecomposition ReferenceProductErrorBounds ReferenceLogScale ReferenceRelativeError

theorem log_square_le_base {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ w : ℝ in atTop,K*(Real.log w)^2 ≤ w := by
  have h : (fun w : ℝ => K*(Real.log w)^2)=o[atTop](fun w => w) := by
    simpa only [Real.rpow_ofNat,Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s:=1) (by norm_num)).const_mul_left K
  filter_upwards [h.bound (by norm_num : (0:ℝ)<1),eventually_ge_atTop (0:ℝ)] with w hw hw0
  simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hK (sq_nonneg _)),abs_of_nonneg hw0,one_mul] using hw

theorem moving_local_reference (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ w B : ℝ,w₀ ≤ w → B₀ ≤ B →
      B ≤ K*(Real.log w)^2 → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |sourceReference w start/referenceProduct w B start.closed-parentBenchmark .even start.ratio| ≤ ε := by
  obtain ⟨c,A,C,BR,wR,hc,hA,hC,hBR,hwR,hR⟩ := source_relative_reference_error 1 (by norm_num)
  obtain ⟨wS,hwS⟩ := eventually_atTop.mp (log_square_le_base hK.le)
  have hdec := log_power_primeError_tendsto (2*C*K^2) 5 hc
  obtain ⟨wE,hwE⟩ := eventually_atTop.mp
    (hdec.eventually (eventually_le_nhds (show (0:ℝ)<ε/2 by linarith)))
  let B₀ := max BR (2*A/ε)
  let w₀ := max wR (max wS (max wE (Real.exp 1)))
  refine ⟨B₀,w₀,hBR.trans_le (le_max_left _ _),hwR.trans_le (le_max_left _ _),?_⟩
  intro w B hw hB hscale start hi h199 h23 hcons hcut
  have hwR' : wR ≤ w := (le_max_left _ _).trans hw
  have hwS' : wS ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw
  have hwE' : wE ≤ w := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hw
  have hwExp : Real.exp 1 ≤ w := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hw
  have hBR' : BR ≤ B := (le_max_left _ _).trans hB
  have hBl : 2*A/ε ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := hBR.trans_le hBR'
  have hlogw : 1 ≤ Real.log w := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hwExp
  have hBw : B ≤ w := hscale.trans (hwS w hwS')
  have hlogs : Real.log B ≤ Real.log w := Real.log_le_log hBpos hBw
  have hcomp : Real.log B ≤ (1:ℝ)*Real.log w := by simpa only [one_mul] using hlogs
  have herr := hR w B hwR' hBR' hcomp start hi h199 h23 hcons hcut
  have hsmall : A/B ≤ ε/2 := by
    apply (div_le_iff₀ hBpos).mpr
    have hh := (div_le_iff₀ hε).mp hBl
    nlinarith
  have hBsq : B^2 ≤ K^2*(Real.log w)^4 := by nlinarith [mul_self_le_mul_self hBpos.le hscale]
  have hL : 1+Real.log B ≤ 2*Real.log w := by linarith
  have hLogPos : 0 ≤ Real.log w := by linarith
  have hE := primeError_pos c w 2
  have hpoly : C*B^2*(1+Real.log B)*primeError c w 2 ≤ 2*C*K^2*(Real.log w)^5*primeError c w 2 := by
    have hh : B^2*(1+Real.log B) ≤ (K^2*(Real.log w)^4)*(2*Real.log w) := by
      calc
        _ ≤ B^2*(2*Real.log w) := mul_le_mul_of_nonneg_left hL (sq_nonneg B)
        _ ≤ _ := mul_le_mul_of_nonneg_right hBsq (by positivity)
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC.le) hE.le
    convert! hm using 1 <;> ring
  have htail := hwE w hwE'
  linarith

end NumberTheoryLean.MovingLocalReference


end Erdos970

end OAI
