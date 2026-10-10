import OAI.Probability.TraceReconstruction.InitialOracle
import OAI.Probability.TraceReconstruction.Amplification

namespace OAI

/-!
# InitialRates

Initial geometric parameters, moment depths, error and overlap rates, and production of the base induction pair.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N q ω w : ℕ → ℝ} {J u m : ℕ → ℕ}

/-- Exact power of the sharp initial rank prefactor; all channel losses are
 subpower at the source's smallest scale. -/
theorem initialPrefactor_rate (hN : Tendsto N atTop atTop)
    {α β : ℝ} (hu : PowerRate N (fun t=>(u t:ℝ)) α)
    (hm : PowerRate N (fun t=>(m t:ℝ)) β) (hq : PowerRate N q 0) (r d : ℕ) :
    PowerRate N (fun t=>initialPrefactorCap (u t) (m t) r d (q t))
      (α/2-β*((d:ℝ)+(r:ℝ)/2)) := by
  have hd : PowerRate N (fun t=>initialDifferenceCap d (q t)) 0 := by
    have H := ((PowerRate.const hN (by positivity : (0:ℝ)<8*((d:ℝ)+1))).div (hq.pow 2)).sqrt.const_mul hN (by norm_num : (0:ℝ)<2)
    simpa only [initialDifferenceCap,zero_mul,zero_sub,neg_zero,zero_div] using H
  have hnum := (((hu.mul hm).const_mul hN (by norm_num : (0:ℝ)<144)).mul_const hN
    (by positivity : (0:ℝ)<(2:ℝ)^(2*r))).mul (hd.pow (2*d+r+2))
  have hden := ((hm.div_const hN (by norm_num : (0:ℝ)<4)).pow d).mul
    (((hu.mul hm).div_const hN (by positivity : (0:ℝ)<2*(r+1:ℝ))).sqrt)
  have H := hnum.div (hden.mul ((hm.div_const hN (by norm_num : (0:ℝ)<4)).sqrt.pow (r+1)))
  convert H using 1
  · ext t; simp only [initialPrefactorCap,Nat.cast_mul]
  · push_cast; ring

theorem periodCentral_rate (hN : Tendsto N atTop atTop) {α : ℝ}
    (hu : PowerRate N (fun t=>(u t:ℝ)) α) {r : ℕ} (hr : 0<r) :
    PowerRate N (fun t=>periodCentralSumConstant (u t) r) (α*((r:ℝ)-3)/2) := by
  have H := ((hu.div_const hN (by positivity : (0:ℝ)<3*(r+1:ℝ))).inv hN).const_mul hN
    (by positivity : (0:ℝ)<((r+1:ℕ):ℝ)^2)
  have H' := H.mul (((hu.const_mul hN (by norm_num : (0:ℝ)<2)).sqrt.const_mul hN
    (by norm_num : (0:ℝ)<2)).pow (r-1))
  convert H' using 1
  · ext t; simp only [periodCentralSumConstant,Nat.cast_mul,Nat.cast_ofNat]
  · rw [Nat.cast_sub (by omega : 1≤r)]; norm_num; ring

theorem periodBounded_rate (hN : Tendsto N atTop atTop) {α : ℝ}
    (hu : PowerRate N (fun t=>(u t:ℝ)) α) {r : ℕ} (hr : 2≤r) (M : ℕ) :
    PowerRate N (fun t=>periodBoundedSumConstant (u t) r M) (α*((r:ℝ)-4)/2) := by
  have H := (((hu.div_const hN (by positivity : (0:ℝ)<3*(r+1:ℝ))).inv hN).const_mul hN
    (by positivity : (0:ℝ)<((r+1:ℕ):ℝ)^2)).mul_const hN (by positivity : (0:ℝ)<(M:ℝ)+1)
  have H' := H.mul (((hu.const_mul hN (by norm_num : (0:ℝ)<2)).sqrt.const_mul hN
    (by norm_num : (0:ℝ)<2)).pow (r-2))
  convert H' using 1
  · ext t; simp only [periodBoundedSumConstant,Nat.cast_mul,Nat.cast_ofNat]
  · rw [Nat.cast_sub hr]; norm_num; ring

theorem hiddenSigned_rate (hN : Tendsto N atTop atTop) {γ : ℝ} (hγ : 0<γ)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) γ) (hω : PowerRate N ω 0) (s : ℕ) :
    PowerRate N (fun t=>hiddenSignedL2Bound (J t) s (ω t)) (-γ*((s:ℝ)+1/2)) := by
  have hden := (hJ.mul (hω.pow 2)).add_const hN (by simpa using hγ) (by norm_num : (0:ℝ)≤2)
  have hroot := ((PowerRate.const hN (by positivity : (0:ℝ)<4*((s:ℝ)+1))).div hden).sqrt
  have hp := ((hroot.const_mul hN (by norm_num : (0:ℝ)<2)).pow s).pow 2
  have H := (hp.const_mul hN (by positivity : (0:ℝ)<((2:ℝ)^(s*s))^2)).mul hroot
  convert H using 1
  · rfl
  · push_cast; ring

theorem hiddenUnsigned_rate (hN : Tendsto N atTop atTop) {γ : ℝ} (hγ : 0<γ)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) γ) (hω : PowerRate N ω 0) (s : ℕ) :
    PowerRate N (fun t=>hiddenUnsignedL2Bound (J t) s (ω t)) (-γ/2) := by
  have hden := (hJ.mul (hω.pow 2)).add_const hN (by simpa using hγ) (by norm_num : (0:ℝ)≤2)
  have H := (((PowerRate.const hN (by norm_num : (0:ℝ)<4)).div hden).sqrt).const_mul hN
    (by positivity : (0:ℝ)<((2:ℝ)^s)^2)
  convert H using 1
  · rfl
  · ring

/-- The two eliminated large gaps are quantitatively visible in this exponent. -/
theorem initial_central_rate (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    {r : ℕ} (hr : 0<r) (d : ℕ) :
    PowerRate N (fun t=>initialPrefactorCap (u t) (m t) r d (q t)*periodCentralSumConstant (u t) r)
      (-123/250-(62/125)*(d:ℝ)-(1/500)*(r:ℝ)) := by
  convert (initialPrefactor_rate hN hu hm hq r d).mul (periodCentral_rate hN hu hr) using 1; ring

theorem initial_bounded_rate (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    {r : ℕ} (hr : 2≤r) (d M : ℕ) :
    PowerRate N (fun t=>initialPrefactorCap (u t) (m t) r d (q t)*periodBoundedSumConstant (u t) r M)
      (-369/500-(62/125)*(d:ℝ)-(1/500)*(r:ℝ)) := by
  convert (initialPrefactor_rate hN hu hm hq r d).mul (periodBounded_rate hN hu hr M) using 1; ring

/-- Fixed low degrees already beat the signed and pure source score exponents. -/
theorem initial_signed_pattern_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0)
    {r : ℕ} (hr : 0<r) (k : Fin r→GapDifference) (hk : Odd (firstDifferenceCount k)) :
    PowerUpper N (fun t=>initialSignedPatternCap (J t) (u t) (m t) r 300 (q t) (ω t) k) (-223/100) := by
  by_cases hlin : ∃a,k=linearPattern a
  · have H := (initial_central_rate hN hu hm hq hr 1).mul
      (hiddenSigned_rate hN (by norm_num) hJ hω 300)
    have hb : -123/250-(62/125)*(1:ℝ)-(1/500)*(r:ℝ)+(-(1/125)*((300:ℝ)+1/2)) ≤ -223/100 := by
      have hh : (0:ℝ)≤r := Nat.cast_nonneg r
      linarith
    simpa only [initialSignedPatternCap,ite_eq_left hlin] using (H.upper hN).mono (by simpa using hb)
  · have hd : 3≤∑h,(k h).order := odd_nonlinear_order k hk hlin
    obtain ⟨a,b,hab,_,_⟩ := odd_pattern_pair k hk hlin
    have hr2 : 2≤r := by have := a.isLt; have := b.isLt; have := hab; omega
    have H := (initial_bounded_rate hN hu hm hq hr2 (∑h,(k h).order) (2*(2^300))).mul
      (hiddenUnsigned_rate hN (by norm_num) hJ hω 300)
    have hb : -369/500-(62/125)*(∑h,(k h).order:ℕ)-(1/500)*(r:ℝ)+(-(1/125)/2) ≤ -223/100 := by
      have hd' : (3:ℝ)≤(∑h,(k h).order:ℕ) := by exact_mod_cast hd
      have hr' : (2:ℝ)≤r := by exact_mod_cast hr2
      linarith
    simpa only [initialSignedPatternCap,ite_eq_right hlin] using (H.upper hN).mono (by simpa using hb)

theorem initial_pure_pattern_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0)
    {r : ℕ} (hr : 0<r) (k : Fin r→GapDifference) (hk : k≠unchangedPattern r) :
    PowerUpper N (fun t=>initialPurePatternCap (J t) (u t) (m t) r 300 (q t) (ω t) k) (-37/25) := by
  by_cases hlin : ∃a,k=linearPattern a
  · have H := (initial_central_rate hN hu hm hq hr 1).mul
      (hiddenSigned_rate hN (by norm_num) hJ hω 300)
    have hb : -123/250-(62/125)*(1:ℝ)-(1/500)*(r:ℝ)+(-(1/125)*((300:ℝ)+1/2)) ≤ -37/25 := by
      have hh : (0:ℝ)≤r := Nat.cast_nonneg r
      linarith
    simpa only [initialPurePatternCap,ite_eq_left hlin] using (H.upper hN).mono (by simpa using hb)
  · have hd := (nonconstant_pattern_linear_or_order_two k hk).resolve_left hlin
    have H := (initial_central_rate hN hu hm hq hr (∑h,(k h).order)).mul
      (hiddenUnsigned_rate hN (by norm_num) hJ hω 300)
    have hb : -123/250-(62/125)*(∑h,(k h).order:ℕ)-(1/500)*(r:ℝ)+(-(1/125)/2) ≤ -37/25 := by
      have hd' : (2:ℝ)≤(∑h,(k h).order:ℕ) := by exact_mod_cast hd
      have hr' : (0:ℝ)≤r := Nat.cast_nonneg r
      linarith
    simpa only [initialPurePatternCap,ite_eq_right hlin] using (H.upper hN).mono (by simpa using hb)

theorem increasingTuple_card_le (u r : ℕ) : Fintype.card (IncreasingTuple u r) ≤ u^r := by
  simpa only [Fintype.card_fun,Fintype.card_fin] using
    Fintype.card_subtype_le (fun v : Fin r→Fin u => StrictMono v)

theorem initialRankTail_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (r : ℕ) (a : ℝ) :
    PowerUpper N (fun t=>initialRankTailCap (u t) (m t) r) a := by
  have hcard : PowerUpper N (fun t=>(Fintype.card (IncreasingTuple (u t) r):ℝ)) ((123/250)*(r:ℝ)) := by
    apply (hu.pow r).upper hN |>.of_abs_le
    exact Eventually.of_forall fun t=>by
      rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (by positivity)]
      exact_mod_cast increasingTuple_card_le (u t) r
  have hpoly := hcard.mul hN (((hu.mul hm).sqrt.const_mul hN
    (by positivity : (0:ℝ)<48*((r+1:ℕ):ℝ))).upper hN)
  have hexpr : PowerRate N (fun t=>(m t:ℝ)/(1024*(u t:ℝ))) (1/250) := by
    convert hm.div (hu.const_mul hN (by norm_num : (0:ℝ)<1024)) using 1; norm_num
  have hexp := hexpr.exp_neg_upper hN (by norm_num) (a/2-((123/250)*(r:ℝ)+(123/250+62/125)/2))
  have H := ((PowerRate.const hN (by norm_num : (0:ℝ)<2)).upper hN).mul hN
    ((hpoly.mul hN hexp).pow hN 2)
  convert H using 1
  · ext t
    simp only [initialRankTailCap,Nat.cast_mul,neg_div]
    ring
  · push_cast; ring

theorem initialMomentRatio_rate (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hw : PowerRate N w 0) :
    PowerRate N (fun t=>initialMomentRatio (u t) (m t) (q t) (w t)) (-1/500) := by
  have H := ((hw.pow 2).mul ((PowerRate.const hN
    (by positivity [rankSchurConstant_pos] : (0:ℝ)<3*rankSchurConstant)).div hq)).mul (hu.div hm).sqrt
  convert H using 1
  · rfl
  · norm_num

theorem initial_fixed_high_tail_rate (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hw : PowerRate N w 0) :
    PowerRate N (fun t=>4*(initialMomentRatio (u t) (m t) (q t) (w t))^3000/
      (1-initialMomentRatio (u t) (m t) (q t) (w t))) (-6) := by
  have hρ := initialMomentRatio_rate hN hu hm hq hw
  have hz := (hρ.upper hN).tendsto_zero hN (by norm_num)
  have hden : PowerRate N (fun t=>1-initialMomentRatio (u t) (m t) (q t) (w t)) 0 := by
    apply PowerRate.of_tendsto hN (by norm_num : (0:ℝ)<1)
    simpa using tendsto_const_nhds.sub hz
  convert ((hρ.pow 3000).const_mul hN (by norm_num : (0:ℝ)<4)).div hden using 1
  norm_num

theorem initialSignedDegree_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0) (r : ℕ) :
    PowerUpper N (fun t=>initialSignedDegreeCap (J t) (u t) (m t) r 300 (q t) (ω t)) (-223/100) := by
  by_cases hr : r=0
  · simpa only [initialSignedDegreeCap,ite_eq_left hr] using PowerUpper.zero hN (-223/100)
  have hs : PowerUpper N (fun t=>∑k : Fin r→GapDifference,
      if Odd (firstDifferenceCount k) then initialSignedPatternCap (J t) (u t) (m t) r 300 (q t) (ω t) k else 0) (-223/100) := by
    apply PowerUpper.sum hN Finset.univ
    intro k _
    by_cases hk : Odd (firstDifferenceCount k)
    · simpa only [ite_eq_left hk] using initial_signed_pattern_upper hN hu hm hq hJ hω (by omega) k hk
    · simpa only [ite_eq_right hk] using PowerUpper.zero hN (-223/100)
  have hc : (0:ℝ)<8*(Fintype.card (Fin r→GapDifference):ℝ) := by
    have hp : 0<Fintype.card (Fin r→GapDifference) := Fintype.card_pos_iff.mpr ⟨fun _=>.unchanged⟩
    positivity
  have H := (((PowerRate.const hN hc).upper hN).mul hN hs)
  simp only [zero_add] at H
  simpa only [initialSignedDegreeCap,ite_eq_right hr] using H.add hN (initialRankTail_upper hN hu hm r (-223/100))

theorem initialPureDegree_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0) (r : ℕ) :
    PowerUpper N (fun t=>initialPureDegreeCap (J t) (u t) (m t) r 300 (q t) (ω t)) (-37/25) := by
  by_cases hr : r=0
  · simpa only [initialPureDegreeCap,ite_eq_left hr] using PowerUpper.zero hN (-37/25)
  have hs : PowerUpper N (fun t=>∑k : Fin r→GapDifference,
      if k=unchangedPattern r then 0 else initialPurePatternCap (J t) (u t) (m t) r 300 (q t) (ω t) k) (-37/25) := by
    apply PowerUpper.sum hN Finset.univ
    intro k _
    by_cases hk : k=unchangedPattern r
    · simpa only [ite_eq_left hk] using PowerUpper.zero hN (-37/25)
    · simpa only [ite_eq_right hk] using initial_pure_pattern_upper hN hu hm hq hJ hω (by omega) k hk
  have hc : (0:ℝ)<2*(Fintype.card (Fin r→GapDifference):ℝ) := by
    have hp : 0<Fintype.card (Fin r→GapDifference) := Fintype.card_pos_iff.mpr ⟨fun _=>.unchanged⟩
    positivity
  have H := (((PowerRate.const hN hc).upper hN).mul hN hs)
  simp only [zero_add] at H
  simpa only [initialPureDegreeCap,ite_eq_right hr] using H.add hN (initialRankTail_upper hN hu hm r (-37/25))

theorem initialSignedCap_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0) (hw : PowerRate N w 0) :
    PowerUpper N (fun t=>initialSignedCap (J t) (u t) (m t) 3000 300 (q t) (ω t) (w t)) (-223/100) := by
  have hs : PowerUpper N (fun t=>∑r∈Finset.range 3000,(w t)^(2*r)*
      initialSignedDegreeCap (J t) (u t) (m t) r 300 (q t) (ω t)) (-223/100) := by
    apply PowerUpper.sum hN (Finset.range 3000)
    intro r _
    simpa only [zero_mul,zero_add] using ((hw.pow (2*r)).upper hN).mul hN (initialSignedDegree_upper hN hu hm hq hJ hω r)
  exact hs.add hN ((initial_fixed_high_tail_rate hN hu hm hq hw).upper hN |>.mono (by norm_num))

theorem initialPureCap_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0) (hw : PowerRate N w 0) :
    PowerUpper N (fun t=>initialPureCap (J t) (u t) (m t) 3000 300 (q t) (ω t) (w t)) (-37/25) := by
  have hs : PowerUpper N (fun t=>∑r∈Finset.range 3000,(w t)^(2*r)*
      initialPureDegreeCap (J t) (u t) (m t) r 300 (q t) (ω t)) (-37/25) := by
    apply PowerUpper.sum hN (Finset.range 3000)
    intro r _
    simpa only [zero_mul,zero_add] using ((hw.pow (2*r)).upper hN).mul hN (initialPureDegree_upper hN hu hm hq hJ hω r)
  exact hs.add hN ((initial_fixed_high_tail_rate hN hu hm hq hw).upper hN |>.mono (by norm_num))

/-- Actual scalar budgets, not assumed coefficient bounds: all report- and
 count-independent caps are strictly below the source clipping allowances. -/
theorem initial_score_caps_eventually (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0) (hw : PowerRate N w 0) :
    ∀ᶠt in atTop,
      64*initialSignedCap (J t) (u t) (m t) 3000 300 (q t) (ω t) (w t) ≤ (N t)^(-11/5:ℝ) ∧
      64*initialPureCap (J t) (u t) (m t) 3000 300 (q t) (ω t) (w t) ≤ (N t)^(-7/5:ℝ) := by
  have hc := (PowerRate.const hN (by norm_num : (0:ℝ)<64)).upper hN
  have hs := hc.mul hN (initialSignedCap_upper hN hu hm hq hJ hω hw)
  have hp := hc.mul hN (initialPureCap_upper hN hu hm hq hJ hω hw)
  filter_upwards [hs (-11/5) (by norm_num),hp (-7/5) (by norm_num)] with t hs hp
  exact ⟨(le_abs_self _).trans hs,(le_abs_self _).trans hp⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N f g : ℕ→ℝ} {α β : ℝ}

theorem PowerRate.sub_lower (hN : Tendsto N atTop atTop)
    (hf : PowerRate N f α) (hg : PowerRate N g β) (hβα : β<α) :
    PowerRate N (fun t=>f t-g t) α := by
  have hz := ((hg.div hf).upper hN).tendsto_zero hN (sub_neg.mpr hβα)
  apply hf.of_ratio hN (by norm_num : (0:ℝ)<1)
  have H : Tendsto (fun t=>1-g t/f t) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hz
  apply H.congr'
  filter_upwards [hf.1] with t ht
  field_simp [ht.ne']

theorem PowerRate.nat_sub_lower (hN : Tendsto N atTop atTop) {f g : ℕ→ℕ}
    (hf : PowerRate N (fun t=>(f t:ℝ)) α)
    (hg : PowerRate N (fun t=>(g t:ℝ)) β) (hβα : β<α) :
    PowerRate N (fun t=>(f t-g t:ℕ)) α := by
  have H := hf.sub_lower hN hg hβα
  apply H.congr
  filter_upwards [H.1] with t ht
  have hg : g t≤f t := by exact_mod_cast (sub_pos.mp ht).le
  rw [Nat.cast_sub hg]

/-- Literal integer choices of the initial-pair construction, including the outer floors. -/
def sourceInitialM (N : ℝ) : ℕ := ⌊N^(62/125:ℝ)⌋₊
def sourceInitialK (N : ℝ) : ℕ := ⌊N^(123/250:ℝ)⌋₊
def sourceInitialPeriodSize (N : ℝ) : ℕ := 2*sourceInitialM N-1
def sourceInitialCapacity (N : ℝ) : ℕ := ⌊N/(sourceInitialPeriodSize N:ℝ)⌋₊
def sourceInitialJ (q N : ℝ) : ℕ :=
  ⌊((sourceInitialCapacity N:ℝ)-sourceInitialK N)/
    (2*(initialSideCount q (sourceInitialM N):ℝ)+1)⌋₊
def sourceInitialP (q N : ℝ) : ℕ :=
  sourceInitialJ q N*(2*initialSideCount q (sourceInitialM N)+1)+sourceInitialK N
/-- One-based manuscript anchors translated once to zero-based list indices. -/
def sourceInitialAnchor (q N : ℝ) : ℤ := ((sourceInitialP q N/2:ℕ):ℤ)-1

theorem sourceInitialM_rate (hN : Tendsto N atTop atTop) :
    PowerRate N (fun t=>(sourceInitialM (N t):ℝ)) (62/125) := by
  have H := ((PowerRate.base hN).rpow (62/125)).nat_floor hN (by norm_num)
  simpa only [sourceInitialM,one_mul] using H

theorem sourceInitialK_rate (hN : Tendsto N atTop atTop) :
    PowerRate N (fun t=>(sourceInitialK (N t):ℝ)) (123/250) := by
  have H := ((PowerRate.base hN).rpow (123/250)).nat_floor hN (by norm_num)
  simpa only [sourceInitialK,one_mul] using H

theorem sourceInitialPeriodSize_rate (hN : Tendsto N atTop atTop) :
    PowerRate N (fun t=>(sourceInitialPeriodSize (N t):ℝ)) (62/125) := by
  have hh : PowerRate N (fun t=>(2*sourceInitialM (N t):ℕ)) (62/125) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (sourceInitialM_rate hN).const_mul hN (by norm_num : (0:ℝ)<2)
  exact hh.nat_sub_lower hN (PowerRate.const hN (by norm_num : (0:ℝ)<(1:ℕ))) (by norm_num)

theorem sourceInitialCapacity_rate (hN : Tendsto N atTop atTop) :
    PowerRate N (fun t=>(sourceInitialCapacity (N t):ℝ)) (63/125) := by
  have H := ((PowerRate.base hN).div (sourceInitialPeriodSize_rate hN)).nat_floor hN (by norm_num)
  convert H using 1
  · rfl
  · norm_num

theorem sourceInitialSide_rate (hN : Tendsto N atTop atTop) {q : ℕ→ℝ}
    (hq : PowerRate N q 0) :
    PowerRate N (fun t=>(initialSideCount (q t) (sourceInitialM (N t)):ℝ)) (62/125) := by
  have H := (hq.mul (sourceInitialM_rate hN)).nat_floor hN (by norm_num)
  simpa only [initialSideCount,zero_add] using H

theorem sourceInitialJ_rate (hN : Tendsto N atTop atTop) {q : ℕ→ℝ}
    (hq : PowerRate N q 0) :
    PowerRate N (fun t=>(sourceInitialJ (q t) (N t):ℝ)) (1/125) := by
  have hn := (sourceInitialCapacity_rate hN).sub_lower hN (sourceInitialK_rate hN) (by norm_num)
  have hd := ((sourceInitialSide_rate hN hq).const_mul hN (by norm_num : (0:ℝ)<2)).add_const hN
    (by norm_num) (by norm_num : (0:ℝ)≤1)
  have H := (hn.div hd).nat_floor hN (by norm_num)
  convert H using 1
  · rfl
  · norm_num

theorem initialOverlap_rate (hN : Tendsto N atTop atTop) {q : ℕ→ℝ}
    (_hq : ∀t,0<q t)
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0)) :
    PowerRate N (fun t=>initialOverlapLower (q t)) 0 := by
  refine ⟨Eventually.of_forall (fun t=>initialOverlapLower_pos _),?_⟩
  have H := (hΛ.const_mul (-(32+3*primitivePeriodConstant))).sub
    ((Real.tendsto_log_atTop.comp hN).const_div_atTop (Real.log 1536))
  simp only [mul_zero,sub_zero] at H
  apply H.congr'
  filter_upwards [] with t
  rw [initialOverlapLower,Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp]
  simp only [zpow_neg,zpow_ofNat,Function.comp_apply]
  ring

theorem deletion_rate_zero (hN : Tendsto N atTop atTop) {q : ℕ→ℝ}
    (hq : ∀t,q t∈Set.Ioc 0 1)
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0)) :
    PowerRate N q 0 := by
  refine ⟨Eventually.of_forall (fun t=>(hq t).1),?_⟩
  apply squeeze_zero_norm' _ hΛ
  filter_upwards [hN.eventually_gt_atTop 1] with t hNt
  have hp := (hq t).1
  have hle := (hq t).2
  have hqinv : 1≤(q t)⁻¹ := (one_le_inv₀ hp).mpr hle
  have hlog : |Real.log (q t)| ≤ (q t)^(-3:ℤ) := by
    rw [abs_of_nonpos (Real.log_nonpos hp.le hle),←Real.log_inv, zpow_neg,zpow_ofNat]
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
    have hcube : (q t)⁻¹ ≤ ((q t)⁻¹)^3 := by nlinarith [sq_nonneg ((q t)⁻¹-1)]
    rw [←inv_pow]
    linarith
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (Real.log_pos hNt)]
  exact div_le_div_of_nonneg_right hlog (Real.log_pos hNt).le

/-- Mechanical realization of the base scalar score budgets from the actual
 integer choices and the unchanged known channel. -/
theorem source_initial_score_caps {q w : ℕ→ℝ} (hN : Tendsto N atTop atTop)
    (hq : ∀t,q t∈Set.Ioc 0 1)
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0))
    (hw : PowerRate N w 0) :
    ∀ᶠt in atTop,
      64*initialSignedCap (sourceInitialJ (q t) (N t)) (sourceInitialK (N t))
        (sourceInitialM (N t)) 3000 300 (q t) (initialOverlapLower (q t)) (w t) ≤ (N t)^(-11/5:ℝ) ∧
      64*initialPureCap (sourceInitialJ (q t) (N t)) (sourceInitialK (N t))
        (sourceInitialM (N t)) 3000 300 (q t) (initialOverlapLower (q t)) (w t) ≤ (N t)^(-7/5:ℝ) := by
  exact initial_score_caps_eventually hN (sourceInitialK_rate hN) (sourceInitialM_rate hN)
    (deletion_rate_zero hN hq hΛ) (sourceInitialJ_rate hN (deletion_rate_zero hN hq hΛ))
    (initialOverlap_rate hN (fun t=>(hq t).1) hΛ) hw

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- The manuscript's one-based middle defect, translated to a list index. -/
def sourceInitialOffset (m : ℕ) (hm : 4 ≤ m) : Fin m :=
  ⟨m/2-1,by omega⟩

theorem sourceInitialOffset_interior (m : ℕ) (hm : 4 ≤ m) :
    1 ≤ (sourceInitialOffset m hm).val ∧ (sourceInitialOffset m hm).val+1 < m := by
  simp only [sourceInitialOffset]; omega

theorem sourceInitialOffset_middle (m : ℕ) (hm : 4 ≤ m) :
    |((sourceInitialOffset m hm).val:ℝ)-(m:ℝ)/2| ≤ 2 := by
  have h1 : 2*(m/2) ≤ m := Nat.mul_div_le m 2
  have h2 : m<2*(m/2+1) := by omega
  have h3 : 1 ≤ m/2 := by omega
  simp only [sourceInitialOffset,Nat.cast_sub h3,Nat.cast_one]
  rw [abs_le]
  have hh1 : (2:ℝ)*(m/2:ℕ) ≤ m := by exact_mod_cast h1
  have hh2 : (m:ℝ)<2*((m/2:ℕ)+1) := by exact_mod_cast h2
  constructor <;> linarith

theorem sourceInitialOffset_safe (u m : ℕ) (hm : 4 ≤ m) :
    SafeTaggedTuple (periodSlot (u:=u) (fun _=>sourceInitialOffset m hm)) := by
  have hi := sourceInitialOffset_interior m hm
  exact constant_period_safe _ hi.1 hi.2 (by omega) id strictMono_id

/-- A literal arithmetic margin implies every base window placement condition. -/
theorem initial_anchor_geometry (J K t s : ℕ) (hK : 12*(J+2^s+1) ≤ K) :
    let a : ℤ := (((J*(2*t+1)+K)/2:ℕ):ℤ)-1
    (J*t+J:ℕ) ≤ a ∧ a+(2^s:ℕ) ≤ (J*t+K:ℕ) ∧
    (K:ℝ)/3 ≤ 2*((a-(J*t:ℕ):ℤ)-J)+1 ∧
    (K:ℝ)/3 ≤ 2*K-(2*((a-(J*t:ℕ):ℤ)+(2:ℝ)^s)+1) := by
  have he : (J*(2*t+1)+K)/2=J*t+(J+K)/2 := by
    rw [show J*(2*t+1)+K=2*(J*t)+(J+K) by ring,Nat.mul_add_div (by norm_num)]
  have hlo : 2*((J+K)/2) ≤ J+K := Nat.mul_div_le _ 2
  have hhi : J+K<2*((J+K)/2+1) := by omega
  have hK1 : 12*(J+1) ≤ K := by nlinarith [Nat.zero_le (2^s)]
  dsimp only
  rw [he]
  have hi1 : J+1 ≤ (J+K)/2 := by omega
  have hi2 : (J+K)/2+(2^s:ℕ) ≤ K+1 := by omega
  constructor
  · apply (le_sub_iff_add_le).mpr
    exact_mod_cast (show J*t+J+1 ≤ J*t+(J+K)/2 from by omega)
  constructor
  · push_cast only [Nat.cast_add]
    omega
  have hl : (2:ℝ)*((J+K)/2:ℕ) ≤ J+K := by exact_mod_cast hlo
  have hh : (J:ℝ)+K<2*(((J+K)/2:ℕ)+1) := by exact_mod_cast hhi
  have hk : (12:ℝ)*((J:ℝ)+(2:ℝ)^s+1) ≤ K := by exact_mod_cast hK
  simp only [Nat.cast_add,Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_one,Int.cast_mul,Nat.cast_mul]
  constructor <;> nlinarith [show (0:ℝ) ≤ (2:ℝ)^s by positivity]

theorem prouhetSeries_coeff_zero (s : ℕ) : (prouhetSeries s).coeff 0=1 := by
  induction s with
  | zero => simp [prouhetSeries]
  | succ s ih =>
    have hp : (0:ℤ)<(2^s:ℕ) := by positivity
    rw [prouhetSeries_succ_coeff,ih,(prouhetSeries_coeff_spec s).1 _ (Or.inl (by omega)),sub_zero]

/-- Literal source initial words really are different, not only their formal templates. -/
theorem motifPeriodWord_ne {m : ℕ} (off : Fin m) (hi : 1 ≤ off.val ∧ off.val+1 < m)
    (u s : ℕ) (a : ℤ) (ha : 0 ≤ a) (hau : a<u) :
    motifPeriodWord off hi u s a (-1) ≠ motifPeriodWord off hi u s a 1 := by
  intro he
  have H := periodString_injective m u he
  have hj : a.toNat<u := by omega
  have h := congrArg (fun f=>((f ⟨a.toNat,hj⟩):Fin m).val) H
  have ha' : (a.toNat:ℤ)=a := Int.toNat_of_nonneg ha
  simp only [motifOffset,ha',sub_self,prouhetSeries_coeff_zero] at h
  have hpos : (0:ℤ)<(2^s:ℕ) := by positivity
  norm_num [motifIndicator,hpos,motifShift] at h

/-- Floors in the initial construction waste no more than one long slot. -/
theorem initial_period_count_bounds {N : ℝ} {m K t : ℕ}
    (hL : 0<2*m-1) (hN : 0 ≤ N) (hK : (K:ℝ) ≤ ⌊N/(2*m-1:ℕ)⌋₊) :
    let F : ℕ := ⌊N/(2*m-1:ℕ)⌋₊
    let J : ℕ := ⌊((F:ℝ)-K)/(2*t+1:ℕ)⌋₊
    let P : ℕ := J*(2*t+1)+K
    (P:ℝ)*(2*m-1:ℕ) ≤ N ∧ N<((P:ℝ)+(2*t+1:ℕ)+1)*(2*m-1:ℕ) := by
  dsimp only
  set F : ℕ := ⌊N/(2*m-1:ℕ)⌋₊
  set J : ℕ := ⌊((F:ℝ)-K)/(2*t+1:ℕ)⌋₊
  have hd : (0:ℝ)<(2*t+1:ℕ) := by positivity
  have hl : (0:ℝ)<(2*m-1:ℕ) := by exact_mod_cast hL
  have hjlo := Nat.floor_le (div_nonneg (sub_nonneg.mpr hK) hd.le)
  have hjhi := Nat.lt_floor_add_one (((F:ℝ)-K)/(2*t+1:ℕ))
  change (J:ℝ) ≤ _ at hjlo
  change _<(J:ℝ)+1 at hjhi
  have hflo := Nat.floor_le (div_nonneg hN hl.le)
  have hfhi := Nat.lt_floor_add_one (N/(2*m-1:ℕ))
  change (F:ℝ) ≤ _ at hflo
  change _<(F:ℝ)+1 at hfhi
  have hp : (J:ℝ)*(2*t+1:ℕ)+K ≤ F := by
    have H := (le_div_iff₀ hd).mp hjlo
    linarith
  have hp' : (F:ℝ)<(J:ℝ)*(2*t+1:ℕ)+K+(2*t+1:ℕ) := by
    have H := (div_lt_iff₀ hd).mp hjhi
    nlinarith
  constructor
  · push_cast
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      (mul_le_mul_of_nonneg_right hp hl.le).trans ((le_div_iff₀ hl).mp hflo)
  · have H := (div_lt_iff₀ hl).mp hfhi
    push_cast at hp' ⊢
    nlinarith

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- Source moment order is twice this integer. -/
def sourceHalfMoment (B D : ℕ) (n : ℝ) (i : ℕ) : ℕ :=
  ⌈(10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)*Real.log n/
    Real.log (sourceTargetScale B D n i)⌉₊

theorem sourceEpsilon_le_one (B D : ℕ) : sourceEpsilon B D ≤ 1 := by
  unfold sourceEpsilon
  apply (div_le_one (by positivity)).mpr
  have H : (1:ℝ) ≤ 2^(4*B+100) := one_le_pow₀ (by norm_num)
  nlinarith [show (0:ℝ) ≤ D by positivity]

theorem sourceTargetScale_tendsto (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n Λ H : ℕ→ℝ} (i : ℕ→ℕ) (hn : Tendsto n atTop atTop) (hH : Tendsto H atTop atTop)
    (hΛ : ∀t,1 ≤ Λ t) (hrel : ∀t,Real.log (n t)=Λ t*H t) :
    Tendsto (fun t=>sourceTargetScale B (sourceDepth B ζ (H t)) (n t) (i t)) atTop atTop := by
  have hlog : Tendsto (fun t=>Real.log (sourceTargetScale B (sourceDepth B ζ (H t)) (n t) (i t))) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (((tendsto_rpow_atTop hζ.1).comp hH).atTop_div_const (by norm_num : (0:ℝ)<2))
    filter_upwards [hH.eventually_ge_atTop 1,hn.eventually_gt_atTop 1] with t ht hnt
    have hl := sourceTargetScale_log_lower B ζ (H t) (n t) (i t) hB hζ.2.le ht hnt
    have he : Real.log (n t)/(2*(H t)^(1-ζ))=Λ t*(H t)^ζ/2 := by
      rw [hrel t,Real.rpow_sub (by linarith : 0<H t),Real.rpow_one]
      have hp : (H t)^ζ ≠ 0 := (Real.rpow_pos_of_pos (by linarith : 0<H t) _).ne'
      field_simp
    rw [he] at hl
    exact (by nlinarith [hΛ t,Real.rpow_nonneg (by linarith : 0 ≤ H t) ζ] : (H t)^ζ/2 ≤ Λ t*(H t)^ζ/2).trans hl
  apply tendsto_atTop_mono' atTop _ hlog
  filter_upwards [hn.eventually_gt_atTop 1] with t ht
  exact Real.log_le_self (Real.rpow_nonneg (by linarith : 0 ≤ n t) _)

theorem source_uniform_log_absorption (B h : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n Λ H : ℕ→ℝ} (i : ℕ→ℕ) (hn : Tendsto n atTop atTop) (hH : Tendsto H atTop atTop)
    (hΛ : ∀t,1 ≤ Λ t) (hrel : ∀t,Real.log (n t)=Λ t*H t) :
    Tendsto (fun t=>((sourceDepth B ζ (H t):ℝ)+1)^h*Λ t/
      Real.log (sourceTargetScale B (sourceDepth B ζ (H t)) (n t) (i t))) atTop (𝓝 0) := by
  have hh := source_uniform_absorption B h ζ hB hζ i hn hH (fun t=>lt_of_lt_of_le (by norm_num) (hΛ t)) hrel
  apply squeeze_zero' _ _ hh
  · filter_upwards [(sourceTargetScale_tendsto B ζ hB hζ i hn hH hΛ hrel).eventually_gt_atTop 1] with t ht
    exact div_nonneg (mul_nonneg (by positivity) (by linarith [hΛ t])) (Real.log_pos ht).le
  · filter_upwards [(sourceTargetScale_tendsto B ζ hB hζ i hn hH hΛ hrel).eventually_gt_atTop 1] with t ht
    apply div_le_div_of_nonneg_left (by positivity [hΛ t])
      (mul_pos (sourceEpsilon_pos _ _) (Real.log_pos ht))
    exact mul_le_of_le_one_left (Real.log_pos ht).le (sourceEpsilon_le_one _ _)

theorem totalScoreExponent_bounds (B D : ℕ) (hB : 2 ≤ B) :
    11/5 ≤ totalScoreExponent B D ∧ totalScoreExponent B D ≤ 3+(D:ℝ)*B := by
  have hdim (i : ℕ) : (2:ℝ) ≤ (if i<warmupBlocks B then (2:ℕ) else B) ∧
      (((if i<warmupBlocks B then (2:ℕ) else B):ℕ):ℝ) ≤ B := by
    split_ifs <;> norm_cast
  have hlo : 0 ≤ ∑i∈Finset.range D,blockGain (if i<warmupBlocks B then 2 else B) := by
    apply Finset.sum_nonneg
    intro i _
    unfold blockGain
    linarith [(hdim i).1]
  have hhi : (∑i∈Finset.range D,blockGain (if i<warmupBlocks B then 2 else B)) ≤ (D:ℝ)*B := by
    calc
      _ ≤ ∑_i∈Finset.range D,(B:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        unfold blockGain
        linarith [(hdim i).1,(hdim i).2]
      _ = _ := by simp
  unfold totalScoreExponent
  constructor <;> linarith

theorem sourceHalfMoment_bounds (B D i : ℕ) {n : ℝ} (hB : 2 ≤ B) (hn : 1<n) :
    1 ≤ sourceHalfMoment B D n i ∧
    (sourceHalfMoment B D n i:ℝ) ≤
      ((10^8:ℝ)*2^(10*B)*((B:ℝ)+4)*2+1)*((D:ℝ)+1)*2^(B*D) := by
  have hp := sourceScaleProduct_lower B D i hB
  have hp0 : 0<sourceScaleProduct B D i := lt_of_lt_of_le (by positivity) hp
  have he : (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)*Real.log n/
      Real.log (sourceTargetScale B D n i)=
      (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)/sourceScaleProduct B D i := by
    rw [sourceTargetScale,Real.log_rpow (by linarith : 0<n)]
    field_simp [(Real.log_pos hn).ne']
  have hd := totalScoreExponent_bounds B D hB
  have hA : 0<(10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1) := by positivity [hd.1]
  unfold sourceHalfMoment
  rw [he]
  constructor
  · exact Nat.one_le_ceil_iff.mpr (div_pos hA hp0)
  have hc := Nat.ceil_lt_add_one (div_nonneg hA.le hp0.le)
  have hb := div_le_div_of_nonneg_left hA.le (by positivity) hp
  have he' : (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)/(1/(2*2^(B*D)))=
      (10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)*2*2^(B*D) := by field_simp
  rw [he'] at hb
  have hdd : totalScoreExponent B D+B+1 ≤ ((B:ℝ)+4)*((D:ℝ)+1) := by nlinarith [hd.2]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdd (by positivity : (0:ℝ) ≤ 10^8*2^(10*B)))
    (by positivity : (0:ℝ) ≤ 2*2^(B*D))
  have hp1 : (1:ℝ) ≤ 2^(B*D) := one_le_pow₀ (by norm_num)
  nlinarith [show (0:ℝ) ≤ D by positivity]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N f g : ℕ→ℝ} {α β : ℝ}

theorem PowerRate.eventually_lt (hN : Tendsto N atTop atTop)
    (hf : PowerRate N f α) (hg : PowerRate N g β) (hab : α<β) :
    ∀ᶠt in atTop, f t<g t := by
  have hz := ((hf.div hg).upper hN).tendsto_zero hN (sub_neg.mpr hab)
  filter_upwards [hz.eventually_lt_const (by norm_num : (0:ℝ)<1),hg.1] with t ht hp
  exact (div_lt_one hp).mp ht

theorem PowerRate.log_base (hN : Tendsto N atTop atTop) :
    PowerRate N (fun t=>Real.log (N t)) 0 := by
  refine ⟨(hN.eventually_gt_atTop 1).mono (fun _ ht=>Real.log_pos ht),?_⟩
  convert
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
      (Real.tendsto_log_atTop.comp hN) using 1
  ext t
  simp only [Function.comp_apply,Real.rpow_one]

/-- Only arithmetic predicates on the literal source integers. -/
structure SourceInitialGeometry (q N : ℝ) : Prop where
  m_large : 128 ≤ sourceInitialM N
  K_pos : 0 < sourceInitialK N
  K_le_m : sourceInitialK N ≤ sourceInitialM N
  seed : 16 ≤ q^3*(sourceInitialM N:ℝ)
  count : 8 ≤ ((sourceInitialK N*sourceInitialM N:ℕ):ℝ)*q^2
  anchor_margin : 12*(sourceInitialJ q N+2^300+1) ≤ sourceInitialK N
  smoothing_margin : ((2*(2^300):ℕ):ℝ) < (sourceInitialK N:ℝ)/(3*(3000+1:ℝ))
  length_lower : N/2 ≤ (sourceInitialP q N:ℝ)*(sourceInitialPeriodSize N:ℝ)
  length_upper : (sourceInitialP q N:ℝ)*(sourceInitialPeriodSize N:ℝ) ≤ N

/-- All floor, seed, count, placement and length restrictions are automatic
 in the actual joint regime; no change of the deletion rate at the base scale. -/
theorem source_initial_geometry {q : ℕ→ℝ} (hN : Tendsto N atTop atTop)
    (hq : ∀t,q t∈Set.Ioc 0 1)
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0)) :
    ∀ᶠt in atTop,SourceInitialGeometry (q t) (N t) := by
  have hm := sourceInitialM_rate hN
  have hK := sourceInitialK_rate hN
  have hqrate := deletion_rate_zero hN hq hΛ
  have hJ := sourceInitialJ_rate hN hqrate
  have hL := sourceInitialPeriodSize_rate hN
  have hF := sourceInitialCapacity_rate hN
  have ht := sourceInitialSide_rate hN hqrate
  have hm128 := (hm.tendsto_atTop hN (by norm_num)).eventually_ge_atTop 128
  have hKm := hK.eventually_lt hN hm (by norm_num)
  have hKF := hK.eventually_lt hN hF (by norm_num)
  have hseed := ((hqrate.pow 3).mul hm).tendsto_atTop hN (by norm_num)
  have hcount := ((hK.mul hm).mul (hqrate.pow 2)).tendsto_atTop hN (by norm_num)
  have hanchor := ((hJ.add_const hN (by norm_num) (by positivity : (0:ℝ)≤2^300+1)).const_mul
    hN (by norm_num : (0:ℝ)<12)).eventually_lt hN hK (by norm_num)
  have hsm := (hK.tendsto_atTop hN (by norm_num)).eventually_gt_atTop ((2*(2^300):ℝ)*(3*3001))
  have hloss : PowerRate N (fun t=>(2*(initialSideCount (q t) (sourceInitialM (N t)):ℝ)+2)*
      (sourceInitialPeriodSize (N t):ℝ)) (124/125) := by
    convert ((ht.const_mul hN (by norm_num : (0:ℝ)<2)).add_const hN
      (by norm_num) (by norm_num : (0:ℝ)≤2)).mul hL using 1
    norm_num
  have hloss' := hloss.eventually_lt hN ((PowerRate.base hN).div_const hN (by norm_num : (0:ℝ)<2)) (by norm_num)
  filter_upwards [hN.eventually_gt_atTop 0,hm128,hK.1,hKm,hKF,
    hseed.eventually_ge_atTop 16,hcount.eventually_ge_atTop 8,hanchor,hsm,hloss'] with t hNt hm128 hKpos hKm hKF hs hc ha hsm hloss
  have hmn : 128 ≤ sourceInitialM (N t) := by exact_mod_cast hm128
  have hKn : 0 < sourceInitialK (N t) := by exact_mod_cast hKpos
  have hLpos : 0 < sourceInitialPeriodSize (N t) := by unfold sourceInitialPeriodSize; omega
  have hcnt := initial_period_count_bounds (m:=sourceInitialM (N t))
    (K:=sourceInitialK (N t)) (t:=initialSideCount (q t) (sourceInitialM (N t)))
    (N:=N t) hLpos hNt.le hKF.le
  have hcnt' : (sourceInitialP (q t) (N t):ℝ)*(sourceInitialPeriodSize (N t):ℝ) ≤ N t ∧
      N t<((sourceInitialP (q t) (N t):ℝ)+(2*initialSideCount (q t) (sourceInitialM (N t))+1:ℕ)+1)*
        (sourceInitialPeriodSize (N t):ℝ) := by
    simpa only [sourceInitialP,sourceInitialJ,sourceInitialCapacity,sourceInitialPeriodSize,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hcnt
  refine ⟨hmn,hKn,?_,hs,?_,?_,?_,?_,hcnt'.1⟩
  · exact_mod_cast hKm.le
  · simpa only [Nat.cast_mul] using hc
  · apply (Nat.cast_le (α:=ℝ)).mp
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    simpa only [add_assoc] using ha.le
  · apply (lt_div_iff₀ (by norm_num : (0:ℝ)<3*(3000+1))).mpr
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,show (3000+1:ℝ)=3001 by norm_num] using hsm
  · have H := hcnt'.2
    push_cast at H
    nlinarith only [H,hloss]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- The exact varying even moment order is subpower at EVERY working scale. -/
theorem sourceHalfMoment_rate (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B) (hζ : ζ∈Set.Ioo 0 1)
    {n Λ H : ℕ→ℝ} (i : ℕ→ℕ) (hn : Tendsto n atTop atTop) (hH : Tendsto H atTop atTop)
    (hΛ : ∀t,1 ≤ Λ t) (hrel : ∀t,Real.log (n t)=Λ t*H t) :
    PowerRate (fun t=>sourceTargetScale B (sourceDepth B ζ (H t)) (n t) (i t))
      (fun t=>(sourceHalfMoment B (sourceDepth B ζ (H t)) (n t) (i t):ℝ)) 0 := by
  let C : ℝ := ((10^8:ℝ)*2^(10*B)*((B:ℝ)+4)*2+1)
  let A : ℝ := C+1+(B:ℝ)*Real.log 2
  have hC : 0<C := by dsimp [C]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  have hscale := sourceTargetScale_tendsto B ζ hB hζ i hn hH hΛ hrel
  have hlim := (source_uniform_log_absorption B 1 ζ hB hζ i hn hH hΛ hrel).const_mul A
  simp only [pow_one,mul_zero] at hlim
  refine ⟨?_,?_⟩
  · filter_upwards [hn.eventually_gt_atTop 1] with t ht
    have hk := (sourceHalfMoment_bounds B (sourceDepth B ζ (H t)) (i t) hB ht).1
    exact_mod_cast (show 0<sourceHalfMoment B (sourceDepth B ζ (H t)) (n t) (i t) by omega)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hn.eventually_gt_atTop 1,hscale.eventually_gt_atTop 1] with t ht hs
    have hk := (sourceHalfMoment_bounds B (sourceDepth B ζ (H t)) (i t) hB ht).1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hk)) (Real.log_pos hs).le
  · filter_upwards [hn.eventually_gt_atTop 1,hscale.eventually_gt_atTop 1] with t ht hs
    let D := sourceDepth B ζ (H t)
    let k := sourceHalfMoment B D (n t) (i t)
    have hk := sourceHalfMoment_bounds B D (i t) hB ht
    have hkpos : 0<(k:ℝ) := by exact_mod_cast (show 0<k by dsimp [k]; omega)
    have hlog := Real.log_le_log hkpos hk.2
    change Real.log (k:ℝ) ≤ Real.log (C*((D:ℝ)+1)*2^(B*D)) at hlog
    rw [Real.log_mul (mul_pos hC (by positivity)).ne' (by positivity),
      Real.log_mul hC.ne' (by positivity),Real.log_pow] at hlog
    have hD : Real.log ((D:ℝ)+1) ≤ D := by
      simpa using Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<(D:ℝ)+1)
    have hc := Real.log_le_sub_one_of_pos hC
    have hb : 0 ≤ (B:ℝ)*Real.log 2 := by positivity
    have hd : 0 ≤ (D:ℝ) := Nat.cast_nonneg _
    have hl : Real.log (k:ℝ) ≤ A*((D:ℝ)+1) := by
      dsimp [A]
      push_cast at hlog
      nlinarith
    have hl' : Real.log (k:ℝ) ≤ A*((D:ℝ)+1)*Λ t :=
      hl.trans (le_mul_of_one_le_right (by positivity) (hΛ t))
    have HH := div_le_div_of_nonneg_right hl' (Real.log_pos hs).le
    simpa only [mul_div_assoc,mul_assoc] using HH

/-- Actual primitive-score weight at the base scale. -/
def sourceInitialWeight (q : ℝ) (k : ℕ) : ℝ := (6*(2*k:ℕ):ℝ)*(2/q)

theorem sourceInitialWeight_rate {N q : ℕ→ℝ} {k : ℕ→ℕ}
    (hN : Tendsto N atTop atTop) (hq : PowerRate N q 0)
    (hk : PowerRate N (fun t=>(k t:ℝ)) 0) :
    PowerRate N (fun t=>sourceInitialWeight (q t) (k t)) 0 := by
  have H := (hk.const_mul hN (by norm_num : (0:ℝ)<24)).div hq
  convert H using 1
  · ext t
    simp only [sourceInitialWeight,Nat.cast_mul,Nat.cast_ofNat]
    ring
  · norm_num

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N q w : ℕ→ℝ} {k : ℕ→ℕ}

def initialClipFactor (N q w : ℝ) : ℝ :=
  4*(initialMomentRatio (sourceInitialK N) (sourceInitialM N) q w/
    (1-initialMomentRatio (sourceInitialK N) (sourceInitialM N) q w))

theorem initialClipFactor_rate (hN : Tendsto N atTop atTop)
    (hq : PowerRate N q 0) (hw : PowerRate N w 0) :
    PowerRate N (fun t=>initialClipFactor (N t) (q t) (w t)) (-1/500) := by
  have hρ := initialMomentRatio_rate hN (sourceInitialK_rate hN) (sourceInitialM_rate hN) hq hw
  have hden := (PowerRate.const hN (by norm_num : (0:ℝ)<1)).sub_lower hN hρ (by norm_num)
  simpa only [initialClipFactor,sub_zero] using (hρ.div hden).const_mul hN (by norm_num : (0:ℝ)<4)

/-- The source moment is genuinely used in clipping: the exponent is linear
 in that moment, not a fixed negative power of the intermediate length. -/
theorem initial_clip_exp_bound (hN : Tendsto N atTop atTop)
    (hq : PowerRate N q 0) (hw : PowerRate N w 0) (hk : ∀ᶠt in atTop,1 ≤ k t) :
    ∀ᶠt in atTop,
      Real.sqrt (6*(initialClipFactor (N t) (q t) (w t))^(k t)) ≤
        Real.exp (-(k t:ℝ)*Real.log (N t)/2000) := by
  have hfac := initialClipFactor_rate hN hq hw
  have hu := hfac.upper hN (-3/2000) (by norm_num)
  filter_upwards [hk,hfac.1,hu,hN.eventually_gt_atTop 1,
    (Real.tendsto_log_atTop.comp hN).eventually_ge_atTop (2000*Real.log 6)] with t hk hp hu hn hlog
  rw [abs_of_pos hp] at hu
  have hh := Real.log_le_log hp hu
  rw [Real.log_rpow (by linarith : 0<N t)] at hh
  have hk' : (1:ℝ) ≤ k t := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ k t)
  have hl : 0 ≤ Real.log (N t) := (Real.log_pos hn).le
  have hg : Real.log 6 ≤ (k t:ℝ)*Real.log (N t)/2000 := by
    change 2000*Real.log 6 ≤ Real.log (N t) at hlog
    nlinarith [mul_nonneg (sub_nonneg.mpr hk') hl]
  have hexp : Real.sqrt (6*initialClipFactor (N t) (q t) (w t)^(k t)) =
      Real.exp ((Real.log 6+(k t:ℝ)*Real.log (initialClipFactor (N t) (q t) (w t)))/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by positivity),Real.log_mul (by norm_num) (pow_pos hp _).ne',Real.log_pow]
    congr 1
    ring
  rw [hexp]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The fixed metadata tails also beat the varying moment times log-scale.
 Their exponents have orders .988 and .008 respectively, while k log N
 has order zero. -/
theorem initial_metadata_exp_bound (hN : Tendsto N atTop atTop)
    (hq : PowerRate N q 0) (hω : PowerRate N (fun t=>initialOverlapLower (q t)) 0)
    (hk : PowerRate N (fun t=>(k t:ℝ)) 0) :
    ∀ᶠt in atTop,
      2*Real.exp (-((sourceInitialK (N t)*sourceInitialM (N t):ℕ):ℝ)*(q t)^4/64)+
        Real.exp (-(sourceInitialJ (q t) (N t):ℝ)*(initialOverlapLower (q t))^4/16) ≤
        3*Real.exp (-(k t:ℝ)*Real.log (N t)) := by
  have hlow : PowerRate N (fun t=>(k t:ℝ)*Real.log (N t)) 0 := by
    simpa using hk.mul (PowerRate.log_base hN)
  have hfirst := (((sourceInitialK_rate hN).mul (sourceInitialM_rate hN)).mul
    (hq.pow 4)).div_const hN (by norm_num : (0:ℝ)<64)
  have hsecond := ((sourceInitialJ_rate hN hq).mul (hω.pow 4)).div_const hN (by norm_num : (0:ℝ)<16)
  filter_upwards [hlow.eventually_lt hN hfirst (by norm_num),hlow.eventually_lt hN hsecond (by norm_num)] with t h1 h2
  have he1 := Real.exp_le_exp.mpr (neg_le_neg h1.le)
  have he2 := Real.exp_le_exp.mpr (neg_le_neg h2.le)
  push_cast
  simp only [neg_div,neg_mul] at he1 he2 ⊢
  linarith

/-- A completely quantitative sufficient moment inequality for the actual
 initial error. This is later discharged by the literal ceiling r_0/2. -/
theorem initial_error_eventually {n A : ℕ→ℝ} (hN : Tendsto N atTop atTop)
    (hn : Tendsto n atTop atTop) (hA : ∀ᶠt in atTop,1 ≤ A t)
    (hq : ∀t,q t∈Set.Ioc 0 1)
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0))
    (hk : PowerRate N (fun t=>(k t:ℝ)) 0) (hk1 : ∀ᶠt in atTop,1 ≤ k t)
    (hmoment : ∀ᶠt in atTop, 10^6*A t*Real.log (n t) ≤ (k t:ℝ)*Real.log (N t)) :
    ∀ᶠt in atTop,
      initialErrorCap (sourceInitialJ (q t) (N t)) (sourceInitialK (N t))
        (sourceInitialM (N t)) (k t) (q t) (initialOverlapLower (q t))
        (sourceInitialWeight (q t) (k t)) ≤ (n t)^(-100*A t) := by
  have hqrate := deletion_rate_zero hN hq hΛ
  have hω := initialOverlap_rate hN (fun t=>(hq t).1) hΛ
  have hw := sourceInitialWeight_rate hN hqrate hk
  have hclip := initial_clip_exp_bound hN hqrate hw hk1
  have hmeta := initial_metadata_exp_bound hN hqrate hω hk
  filter_upwards [hclip,hmeta,hmoment,hA,hn.eventually_gt_atTop 1,
    (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop (Real.log 4)] with t hc hm hmom hA hn hlog
  have hAn : 0 ≤ A t*Real.log (n t) := mul_nonneg (by linarith) (Real.log_pos hn).le
  have he1 : Real.exp (-(k t:ℝ)*Real.log (N t)/2000) ≤ Real.exp (-500*(A t*Real.log (n t))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he2 : Real.exp (-(k t:ℝ)*Real.log (N t)) ≤ Real.exp (-500*(A t*Real.log (n t))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have herr : initialErrorCap (sourceInitialJ (q t) (N t)) (sourceInitialK (N t))
      (sourceInitialM (N t)) (k t) (q t) (initialOverlapLower (q t))
      (sourceInitialWeight (q t) (k t)) ≤ 4*Real.exp (-500*(A t*Real.log (n t))) := by
    unfold initialErrorCap
    change Real.sqrt (6*initialClipFactor (N t) (q t) (sourceInitialWeight (q t) (k t))^(k t))+_ ≤ _
    nlinarith only [hc,hm,he1,he2]
  apply herr.trans
  rw [Real.rpow_def_of_pos (by linarith : 0<n t)]
  calc
    4*Real.exp (-500*(A t*Real.log (n t))) =
        Real.exp (Real.log 4-500*(A t*Real.log (n t))) := by
      rw [Real.exp_sub,Real.exp_log (by norm_num)]
      rw [show -500*(A t*Real.log (n t)) = -(500*(A t*Real.log (n t))) by ring, Real.exp_neg]
      rfl
    _ ≤ Real.exp (Real.log (n t)*(-100*A t)) := by
      apply Real.exp_le_exp.mpr
      have hAL : Real.log 4 ≤ A t*Real.log (n t) := hlog.trans (le_mul_of_one_le_left (Real.log_pos hn).le hA)
      nlinarith

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N f g : ℕ→ℝ} {α β : ℝ}

theorem PowerRate.add_lower (hN : Tendsto N atTop atTop)
    (hf : PowerRate N f α) (hg : PowerRate N g β) (hβα : β<α) :
    PowerRate N (fun t=>f t+g t) α := by
  have hz := ((hg.div hf).upper hN).tendsto_zero hN (sub_neg.mpr hβα)
  apply hf.of_ratio hN (by norm_num : (0:ℝ)<1)
  have H : Tendsto (fun t=>1+g t/f t) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hz
  apply H.congr'
  filter_upwards [hf.1] with t ht
  field_simp [ht.ne']

theorem PowerRate.nat_ceil (hN : Tendsto N atTop atTop) (hf : PowerRate N f α)
    (ha : 0<α) : PowerRate N (fun t=>(⌈f t⌉₊:ℝ)) α := by
  exact hf.of_ratio hN (by norm_num : (0:ℝ)<1)
    (tendsto_nat_ceil_div_atTop.comp (hf.tendsto_atTop hN ha))

def sourceOverlapConstant (q : ℝ) : ℝ := (2:ℝ)^40/(q*initialOverlapLower q)
def sourceInitialCount (q N : ℝ) : ℕ :=
  ⌈sourceOverlapConstant q*(initialSideCount q (sourceInitialM N):ℝ)*(sourceInitialP q N:ℝ)⌉₊

theorem sourceInitialP_rate {q : ℕ→ℝ} (hN : Tendsto N atTop atTop)
    (hq : PowerRate N q 0) :
    PowerRate N (fun t=>(sourceInitialP (q t) (N t):ℝ)) (63/125) := by
  have hj := sourceInitialJ_rate hN hq
  have ht := ((sourceInitialSide_rate hN hq).const_mul hN (by norm_num : (0:ℝ)<2)).add_const hN
    (by norm_num) (by norm_num : (0:ℝ)≤1)
  have H := (hj.mul ht).add_lower hN (sourceInitialK_rate hN) (by norm_num)
  convert H using 1
  · ext t
    simp only [sourceInitialP,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  · norm_num

theorem sourceOverlapConstant_rate {q : ℕ→ℝ} (hN : Tendsto N atTop atTop)
    (hq : PowerRate N q 0) (hω : PowerRate N (fun t=>initialOverlapLower (q t)) 0) :
    PowerRate N (fun t=>sourceOverlapConstant (q t)) 0 := by
  simpa only [sourceOverlapConstant,add_zero,sub_zero] using
    (PowerRate.const hN (by positivity : (0:ℝ)<(2:ℝ)^40)).div (hq.mul hω)

theorem sourceInitialCount_rate {q : ℕ→ℝ} (hN : Tendsto N atTop atTop)
    (hq : PowerRate N q 0) (hω : PowerRate N (fun t=>initialOverlapLower (q t)) 0) :
    PowerRate N (fun t=>(sourceInitialCount (q t) (N t):ℝ)) 1 := by
  have H := (((sourceOverlapConstant_rate hN hq hω).mul (sourceInitialSide_rate hN hq)).mul
    (sourceInitialP_rate hN hq)).nat_ceil hN (by norm_num)
  convert H using 1
  · rfl
  · norm_num

theorem sourceOverlapConstant_pos {q : ℝ} (hq : 0<q) : 0<sourceOverlapConstant q := by
  unfold sourceOverlapConstant
  positivity [initialOverlapLower_pos q]

theorem sourceOverlapConstant_large {q : ℝ} (hq : q∈Set.Ioc 0 (1/2:ℝ)) :
    1073741824 ≤ initialOverlapLower q*sourceOverlapConstant q := by
  have hω := initialOverlapLower_pos q
  have he : initialOverlapLower q*sourceOverlapConstant q=(2:ℝ)^40/q := by
    unfold sourceOverlapConstant
    field_simp
  rw [he]
  apply (le_div_iff₀ hq.1).mpr
  nlinarith [hq.2]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

def sourceInitialWord (q N : ℝ) (τ : ℝ) : List Bool :=
  if hm : 4 ≤ sourceInitialM N then
    motifPeriodWord (sourceInitialOffset (sourceInitialM N) hm)
      (sourceInitialOffset_interior _ hm) (sourceInitialP q N) 300 (sourceInitialAnchor q N) τ
  else []

def sourceInitialPure (q N : ℝ) : List Bool :=
  pureAtomRun (initialPeriod (sourceInitialM N) (sourceInitialM N/2-1)) (sourceInitialP q N)

def sourceInitialError (q N : ℝ) (k : ℕ) : ℝ :=
  initialErrorCap (sourceInitialJ q N) (sourceInitialK N) (sourceInitialM N) k q
    (initialOverlapLower q) (sourceInitialWeight q k)

theorem sourceInitialWord_length {q N : ℝ} (hm : 4 ≤ sourceInitialM N) (τ : ℝ) :
    (sourceInitialWord q N τ).length=sourceInitialP q N*sourceInitialPeriodSize N := by
  rw [sourceInitialWord,dite_eq_left hm,motifPeriodWord_length]
  rfl

theorem sourceInitialWord_different {q N : ℝ} (H : SourceInitialGeometry q N) :
    sourceInitialWord q N (-1) ≠ sourceInitialWord q N 1 := by
  have hm : 4 ≤ sourceInitialM N := (by norm_num : 4 ≤ 128).trans H.m_large
  have ha := initial_anchor_geometry (sourceInitialJ q N) (sourceInitialK N)
    (initialSideCount q (sourceInitialM N)) 300 H.anchor_margin
  have hap : (0:ℤ) ≤ sourceInitialAnchor q N := (Int.natCast_nonneg _).trans ha.1
  have hau : sourceInitialAnchor q N<(sourceInitialP q N:ℤ) := by
    have h1 := ha.2.1
    have he : (sourceInitialJ q N*initialSideCount q (sourceInitialM N)+sourceInitialK N:ℕ) ≤ sourceInitialP q N := by
      unfold sourceInitialP
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      omega
    have hp : (0:ℤ)<(2^300:ℕ) := by positivity
    have hh : ((sourceInitialJ q N*initialSideCount q (sourceInitialM N)+sourceInitialK N:ℕ):ℤ) ≤ sourceInitialP q N := Int.ofNat_le.mpr he
    exact (lt_add_of_pos_right (sourceInitialAnchor q N) hp).trans_le (h1.trans hh)
  simp only [sourceInitialWord,dite_eq_left hm]
  exact motifPeriodWord_ne _ _ _ _ _ hap hau

/-- The actual initial proof, with no oracle or coefficient-bound hypothesis.
 The only moment restriction is the quantitative source ceiling inequality. -/
theorem source_initial_oracles_eventually {N q n A : ℕ→ℝ} {k : ℕ→ℕ}
    (hN : Tendsto N atTop atTop) (hn : Tendsto n atTop atTop)
    (hA : ∀ᶠt in atTop,1 ≤ A t) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0))
    (hk : PowerRate N (fun t=>(k t:ℝ)) 0) (hk1 : ∀ᶠt in atTop,1 ≤ k t)
    (hmoment : ∀ᶠt in atTop,10^6*A t*Real.log (n t) ≤ (k t:ℝ)*Real.log (N t)) :
    ∀ᶠt in atTop,
      SourceInitialGeometry (q t) (N t) ∧
      sourceInitialError (q t) (N t) (k t) ≤ (n t)^(-100*A t) ∧
      Nonempty (OracleTracePair (q t) (sourceInitialWord (q t) (N t) (-1))
        (sourceInitialWord (q t) (N t) 1) (k t) (sourceInitialError (q t) (N t) (k t)) ((N t)^(-11/5:ℝ))) ∧
      Nonempty (OracleTracePair (q t) (sourceInitialPure (q t) (N t))
        (sourceInitialWord (q t) (N t) 1) (k t) (sourceInitialError (q t) (N t) (k t)) ((N t)^(-7/5:ℝ))) := by
  have hq' (t) : q t ∈ Set.Ioc 0 1 := ⟨(hq t).1,by linarith [(hq t).2]⟩
  have hqr := deletion_rate_zero hN hq' hΛ
  have hw := sourceInitialWeight_rate hN hqr hk
  have herr := initial_error_eventually hN hn hA hq' hΛ hk hk1 hmoment
  have hgeo := source_initial_geometry hN hq' hΛ
  have hcap := source_initial_score_caps hN hq' hΛ hw
  have hρ := (initialMomentRatio_rate hN (sourceInitialK_rate hN) (sourceInitialM_rate hN) hqr hw).upper hN |>.tendsto_zero hN (by norm_num)
  have hsmall := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<100)).comp hn).eventually_le_const (by norm_num : (0:ℝ)<1/2)
  filter_upwards [hgeo,hcap,herr,hk1,hA,hn.eventually_gt_atTop 1,hN.eventually_gt_atTop 0,
    hρ.eventually_le_const (by norm_num : (0:ℝ)<1/2),hsmall] with t hg hcap he hk1 ha hnt hNt hρ hsmall
  have hm : 4 ≤ sourceInitialM (N t) := (by norm_num : 4 ≤ 128).trans hg.m_large
  let off := sourceInitialOffset (sourceInitialM (N t)) hm
  have hi := sourceInitialOffset_interior _ hm
  have hanchor := initial_anchor_geometry (sourceInitialJ (q t) (N t)) (sourceInitialK (N t))
    (initialSideCount (q t) (sourceInitialM (N t))) 300 hg.anchor_margin
  change _ ≤ sourceInitialAnchor (q t) (N t) ∧ sourceInitialAnchor (q t) (N t)+(2^300:ℕ) ≤ _ ∧ _ at hanchor
  have he' : sourceInitialError (q t) (N t) (k t) ≤ 1/2 := by
    exact he.trans ((Real.rpow_le_rpow_of_exponent_le hnt.le (by linarith : -100*A t ≤ -100)).trans hsmall)
  have hc : Real.sqrt (6*(4*(initialMomentRatio (sourceInitialK (N t)) (sourceInitialM (N t)) (q t)
      (sourceInitialWeight (q t) (k t))/(1-initialMomentRatio (sourceInitialK (N t))
      (sourceInitialM (N t)) (q t) (sourceInitialWeight (q t) (k t)))))^(k t)) ≤ 1/2 := by
    have ht : 0 ≤ 2*Real.exp (-((sourceInitialK (N t)*sourceInitialM (N t):ℕ):ℝ)*(q t)^4/64)+
      Real.exp (-(sourceInitialJ (q t) (N t):ℝ)*(initialOverlapLower (q t))^4/16) := by positivity
    unfold sourceInitialError initialErrorCap at he'
    linarith only [he',ht]
  have HH := actual_initial_oracles hg.K_pos hg.m_large hg.K_le_m (by norm_num : 0<3000)
    off hi (sourceInitialOffset_middle _ hm) (sourceInitialOffset_safe _ _ hm)
    (sourceInitialAnchor (q t) (N t)) 300 (k t) hk1 (hq t) hg.seed hg.count
    hanchor.1 hanchor.2.1 hanchor.2.2.1 hanchor.2.2.2 hg.smoothing_margin
    (rfl : sourceInitialWeight (q t) (k t)=_) hρ hc
    (Real.rpow_nonneg hNt.le _) (Real.rpow_nonneg hNt.le _) hcap.1 hcap.2
  refine ⟨hg,he,?_,?_⟩
  · simpa only [sourceInitialWord,dite_eq_left hm,sourceInitialP,sourceInitialError,off] using HH.1
  · simpa only [sourceInitialWord,dite_eq_left hm,sourceInitialP,sourceInitialError,sourceInitialPure,
      off,sourceInitialOffset] using HH.2

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- Literal count instantiation; the harmless ceiling is included. -/
theorem sourceInitialCount_bounds {q N : ℝ} (hq : q ∈ Set.Ioc 0 (1/2:ℝ))
    (H : SourceInitialGeometry q N) :
    sourceInitialP q N*sourceInitialPeriodSize N  ≤  sourceInitialCount q N ∧
    (sourceInitialCount q N:ℝ)  ≤  (sourceOverlapConstant q)^2*
      ((sourceInitialP q N*sourceInitialPeriodSize N:ℕ):ℝ) := by
  let C := sourceOverlapConstant q
  let m := sourceInitialM N
  let t := initialSideCount q m
  let P := sourceInitialP q N
  let ell := sourceInitialPeriodSize N
  have hC : 0<C := sourceOverlapConstant_pos hq.1
  have hm : 32 ≤ m := (by norm_num : 32 ≤ 128).trans H.m_large
  have ht := initialSideCount_bounds hq hm H.seed
  have hω := initialOverlapLower_lt_eighth hq.1
  have hω0 := initialOverlapLower_pos q
  have hCq : 4  ≤  C*q := by
    have he : C*q=(2:ℝ)^40/initialOverlapLower q := by dsimp [C,sourceOverlapConstant]; field_simp [hq.1.ne']
    rw [he]
    exact (le_div_iff₀ hω0).mpr (by nlinarith)
  have hC2 : 2  ≤  C := by nlinarith [hq.2]
  have hell : (ell:ℝ)=2*(m:ℝ)-1 := by
    dsimp [ell,sourceInitialPeriodSize,m]
    rw [Nat.cast_sub (by omega),Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  have hell1 : (1:ℝ) ≤ ell := by
    rw [hell]
    have hml : (32:ℝ) ≤ m := by exact_mod_cast hm
    linarith only [hml]
  have hPm : 1 ≤ P := by dsimp [P,sourceInitialP]; have := H.K_pos; omega
  have hP : (1:ℝ) ≤ P := by exact_mod_cast hPm
  have hPt : 0 ≤ (P:ℝ) := Nat.cast_nonneg _
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hlower : (ell:ℝ) ≤ C*(t:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left ht.1 hC.le
    have hh' := mul_le_mul_of_nonneg_right hCq hm0
    rw [hell]
    dsimp [t] at *
    nlinarith only [hh,hh']
  have hct : 0 ≤ C*(t:ℝ)*(P:ℝ) := by positivity
  have hceil : C*(t:ℝ)*(P:ℝ) ≤ (sourceInitialCount q N:ℝ) := Nat.le_ceil _
  have hu : (sourceInitialCount q N:ℝ)<C*(t:ℝ)*(P:ℝ)+1 := Nat.ceil_lt_add_one hct
  constructor
  · apply (Nat.cast_le (α:=ℝ)).mp
    simp only [Nat.cast_mul]
    simpa only [mul_comm (ell:ℝ) (P:ℝ)] using (mul_le_mul_of_nonneg_right hlower hPt).trans hceil
  · have htell : (t:ℝ) ≤ ell := by
      have hh := mul_le_mul_of_nonneg_right hq.2 hm0
      rw [hell]
      have hml : (32:ℝ) ≤ m := by exact_mod_cast hm
      linarith [ht.2.1]
    have he1 : (1:ℝ) ≤ (P:ℝ)*ell := one_le_mul_of_one_le_of_one_le hP hell1
    have hu' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htell hC.le) hPt
    have hc : C+1 ≤ C^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hPt (zero_le_one.trans hell1))
    change _  ≤  C^2*((P*ell:ℕ):ℝ)
    rw [Nat.cast_mul]
    nlinarith only [hu,hu',he1,hh]

/-- Genuine overlap stability for complete traces of powers. -/
theorem OracleTracePair.transfer_power_overlap {q E V p : ℝ} {x y : List Bool} {k F : ℕ}
    (C : OracleTracePair q x y k E V) (hq : q ∈ Set.Icc 0 1) (hk : 1 ≤ k)
    (hov : p ≤ listTraceOverlap q hq (pureAtomRun y F) (pureAtomRun y (F+1))) :
    p-(Real.sqrt ((F:ℝ)*V)+2*(F:ℝ)*E)-
      (Real.sqrt (((F+1:ℕ):ℝ)*V)+2*((F+1:ℕ):ℝ)*E)  ≤ 
      listTraceOverlap q hq (pureAtomRun x F) (pureAtomRun x (F+1)) := by
  let a := pureAtomRun y F
  let b := pureAtomRun y (F+1)
  let u := pureAtomRun x F
  let v := pureAtomRun x (F+1)
  let M := max (max a.length b.length) (max u.length v.length)
  have ha : a.length ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hb : b.length ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hu : u.length ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hv : v.length ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have H₁ := C.power_tv hq hk F M hu ha
  have H₂ := C.power_tv hq hk (F+1) M hv hb
  rw [listTraceOverlap_ambient hq _ _ M ha hb,FiniteLaw.overlap_eq_one_sub_tv] at hov
  rw [listTraceOverlap_ambient hq _ _ M hu hv,FiniteLaw.overlap_eq_one_sub_tv]
  have HH := (FiniteLaw.tv_triangle (listTraceLaw q hq u M hu) (listTraceLaw q hq a M ha)
    (listTraceLaw q hq v M hv)).trans
    (add_le_add le_rfl (FiniteLaw.tv_triangle (listTraceLaw q hq a M ha)
      (listTraceLaw q hq b M hb) (listTraceLaw q hq v M hv)))
  rw [FiniteLaw.tv_symm (listTraceLaw q hq b M hb) (listTraceLaw q hq v M hv)] at HH
  linarith only [HH,H₁,H₂,hov]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem powerTransferBudget_mono {V W E : ℝ} {F G : ℕ} (hE : 0 ≤ E)
    (hV : 0 ≤ V) (hVW : V ≤ W) (hFG : F ≤ G) :
    Real.sqrt ((F:ℝ)*V)+2*(F:ℝ)*E ≤ Real.sqrt ((G:ℝ)*W)+2*(G:ℝ)*E := by
  have hfg : (F:ℝ) ≤ G := by exact_mod_cast hFG
  apply add_le_add
  · exact Real.sqrt_le_sqrt (mul_le_mul hfg hVW hV (Nat.cast_nonneg _))
  · nlinarith only [mul_le_mul_of_nonneg_right hfg hE]

theorem source_initial_power_overlap {q N E : ℝ} {k : ℕ}
    (hq : q ∈ Set.Ioc 0 (1/2:ℝ)) (H : SourceInitialGeometry q N)
    (hN : 1 ≤ N) (hk : 1 ≤ k)
    (C : OracleTracePair q (sourceInitialWord q N (-1)) (sourceInitialWord q N 1)
      k E (N^(-11/5:ℝ)))
    (U : OracleTracePair q (sourceInitialPure q N) (sourceInitialWord q N 1)
      k E (N^(-7/5:ℝ)))
    (hsmall : Real.sqrt (((sourceInitialCount q N+1:ℕ):ℝ)*(N^(-7/5:ℝ)))+
      2*((sourceInitialCount q N+1:ℕ):ℝ)*E ≤ 1/16) :
    initialOverlapLower q ≤ listTraceOverlap q ⟨hq.1.le,by linarith [hq.2]⟩
      (pureAtomRun (sourceInitialWord q N (-1)) (sourceInitialCount q N))
      (pureAtomRun (sourceInitialWord q N (-1)) (sourceInitialCount q N+1)) := by
  let F := sourceInitialCount q N
  have hm : 4 ≤ sourceInitialM N := (by norm_num : 4 ≤ 128).trans H.m_large
  let off := sourceInitialOffset (sourceInitialM N) hm
  have ht := initialSideCount_bounds hq ((by norm_num : 32 ≤ 128).trans H.m_large) H.seed
  have hqm : 2 ≤ q*(sourceInitialM N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (show q^2 ≤ 1 by nlinarith [hq.1,hq.2])
      (mul_nonneg hq.1.le (Nat.cast_nonneg (sourceInitialM N)))
    nlinarith [H.seed]
  have ht1 : 1 ≤ initialSideCount q (sourceInitialM N) := by
    have hh : (1:ℝ) ≤ initialSideCount q (sourceInitialM N) := by linarith [ht.1]
    exact_mod_cast hh
  have hP : 1 ≤ sourceInitialP q N := by unfold sourceInitialP; have := H.K_pos; omega
  have hω : initialOverlapLower q ∈ Set.Ioc 0 (1/8:ℝ) :=
    ⟨initialOverlapLower_pos q,(initialOverlapLower_lt_eighth hq.1).le⟩
  have hqc : q ∈ Set.Icc 0 1 := ⟨hq.1.le,by linarith [hq.2]⟩
  have hu := U.lifted_power_overlap hqc hk ht1 hP hω (sourceOverlapConstant_large hq)
    (Nat.le_ceil _) (initial_pure_trace_overlap hq
      ((by norm_num : 32 ≤ 128).trans H.m_large) H.seed off ((sourceInitialOffset_middle _ hm).trans (by norm_num)))
  have hv0 := Real.rpow_nonneg (by linarith : 0 ≤ N) (-11/5:ℝ)
  have hw0 := Real.rpow_nonneg (by linarith : 0 ≤ N) (-7/5:ℝ)
  have hvw : N^(-11/5:ℝ) ≤ N^(-7/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have hs0 := (powerTransferBudget_mono C.error_nonneg hw0 le_rfl (Nat.le_succ F)).trans hsmall
  have hs1 := (powerTransferBudget_mono C.error_nonneg hv0 hvw (Nat.le_succ F)).trans hsmall
  have hs2 := (powerTransferBudget_mono C.error_nonneg hv0 hvw (le_refl (F+1))).trans hsmall
  have htrans := C.transfer_power_overlap hqc hk hu
  have hω' := hω.2
  dsimp only [F,sourceInitialCount] at hs0 hs1 hs2 hsmall ⊢
  linarith only [htrans,hs0,hs1,hs2,hsmall,hω']

/-- The exact initial overlap error is negligible, including channel-dependent
 count factors. This is a consequence, not a hypothesis of the initial pair. -/
theorem source_initial_overlap_budget_eventually {q N E : ℕ→ℝ}
    (hN : Tendsto N atTop atTop) (hq : PowerRate N q 0)
    (hω : PowerRate N (fun t=>initialOverlapLower (q t)) 0)
    (hE : ∀ᶠt in atTop,0 ≤ E t ∧ E t ≤ (N t)^(-100:ℝ)) :
    ∀ᶠt in atTop,Real.sqrt (((sourceInitialCount (q t) (N t)+1:ℕ):ℝ)*((N t)^(-7/5:ℝ)))+
      2*((sourceInitialCount (q t) (N t)+1:ℕ):ℝ)*E t ≤ 1/16 := by
  have hF := (sourceInitialCount_rate hN hq hω).add_const hN (by norm_num) (by norm_num : (0:ℝ) ≤ 1)
  have hw := (PowerRate.base hN).rpow (-7/5:ℝ)
  have he := (PowerRate.base hN).rpow (-100:ℝ)
  have hs := ((hF.mul hw).sqrt.upper hN).tendsto_zero hN (by norm_num)
  have ht := (((hF.mul he).const_mul hN (by norm_num : (0:ℝ)<2)).upper hN).tendsto_zero hN (by norm_num)
  have hsum := hs.add ht
  rw [zero_add] at hsum
  have HH := hsum.eventually_le_const (by norm_num : (0:ℝ)<1/16)
  filter_upwards [HH,hE] with t ht he
  simp only [Nat.cast_add,Nat.cast_one]
  simp only [←mul_assoc] at ht
  apply le_trans _ ht
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left he.2 (by positivity)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem source_initial_level_eventually {N q n A : ℕ→ℝ} {k : ℕ→ℕ}
    (hN : Tendsto N atTop atTop) (hn : Tendsto n atTop atTop)
    (hA : ∀ᶠt in atTop,1 ≤ A t) (hq : ∀t,q t ∈ Set.Ioc 0 (1/2:ℝ))
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0))
    (hk : PowerRate N (fun t=>(k t:ℝ)) 0) (hk1 : ∀ᶠt in atTop,1 ≤ k t)
    (hmoment : ∀ᶠt in atTop,10^6*A t*Real.log (n t) ≤ (k t:ℝ)*Real.log (N t))
    (hscale : ∀ᶠt in atTop,N t ≤ n t) :
    ∀ᶠt in atTop,Nonempty (ConcreteLevelPair (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩
      (N t) ((n t)^(-100*A t)) (11/5) (initialOverlapLower (q t))
      ((sourceOverlapConstant (q t))^2) 0 (k t)) := by
  have hor := source_initial_oracles_eventually hN hn hA hq hΛ hk hk1 hmoment
  have hq' (t) : q t ∈ Set.Ioc 0 1 := ⟨(hq t).1,by linarith [(hq t).2]⟩
  have hqr := deletion_rate_zero hN hq' hΛ
  have hωr := initialOverlap_rate hN (fun t=>(hq t).1) hΛ
  have he : ∀ᶠt in atTop,0 ≤ sourceInitialError (q t) (N t) (k t) ∧
      sourceInitialError (q t) (N t) (k t) ≤ (N t)^(-100:ℝ) := by
    filter_upwards [hor,hA,hscale,hN.eventually_gt_atTop 1] with t ht ha hs hNt
    obtain ⟨C⟩ := ht.2.2.1
    refine ⟨C.error_nonneg,ht.2.1.trans ?_⟩
    calc
      (n t)^(-100*A t) ≤ (n t)^(-100:ℝ) := Real.rpow_le_rpow_of_exponent_le (hNt.le.trans hs) (by linarith)
      _ ≤ (N t)^(-100:ℝ) := Real.rpow_le_rpow_of_nonpos (by linarith) hs (by norm_num)
  have hsmall := source_initial_overlap_budget_eventually hN hqr hωr he
  filter_upwards [hor,hsmall,hk1,hN.eventually_gt_atTop 2,hn.eventually_gt_atTop 0] with t ht hs hk1 hNt hnt
  obtain ⟨H,herr,⟨C⟩,⟨U⟩⟩ := ht
  have hm : 4 ≤ sourceInitialM (N t) := (by norm_num : 4 ≤ 128).trans H.m_large
  have hlen := sourceInitialWord_length (q:=q t) hm (-1)
  have hlen' := sourceInitialWord_length (q:=q t) hm 1
  have hh := sourceInitialCount_bounds (hq t) H
  have hlower : N t/2 ≤ ((sourceInitialWord (q t) (N t) (-1)).length:ℝ) := by
    rw [hlen,Nat.cast_mul]; exact H.length_lower
  have hupper : ((sourceInitialWord (q t) (N t) (-1)).length:ℝ) ≤ N t := by
    rw [hlen,Nat.cast_mul]; exact H.length_upper
  have hell : (1:ℝ) ≤ (sourceInitialWord (q t) (N t) (-1)).length := by linarith only [hNt,hlower]
  have hp : 0 < ((sourceInitialWord (q t) (N t) (-1)).length:ℝ) := by linarith only [hell]
  refine ⟨C.toConcrete ⟨(hq t).1.le,by linarith [(hq t).2]⟩
    (hlen.trans hlen'.symm) (sourceInitialWord_different H) hlower hupper ?_ (by norm_num)
    (by simpa only [hlen] using hh.1) (by simpa only [hlen] using hh.2) ?_⟩
  · simp only [Nat.cast_zero,zero_add,one_mul]
    apply (div_le_iff₀ hp).mpr
    exact herr.trans (le_mul_of_one_le_right (Real.rpow_nonneg hnt.le _) hell)
  · exact source_initial_power_overlap (hq t) H (by linarith) hk1 C U hs

/-- All backwards targets are no larger than n, with the source epsilon. -/
theorem sourceScaleProduct_le_one (B D i : ℕ) (hB : 2 ≤ B) : sourceScaleProduct B D i ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro j _
    have hdim : sourceDimension B j ≤ B := by unfold sourceDimension; split_ifs <;> omega
    have he := sourceEpsilon_pos B D
    have hh := sourceEpsilon_small B D
    have hp : (1:ℝ) ≤ 2^B := one_le_pow₀ (by norm_num)
    have hd : 0 ≤ (D:ℝ) := Nat.cast_nonneg _
    have hu : (2:ℝ)^B*sourceEpsilon B D ≤ 1/2 := by
      nlinarith only [hh,mul_nonneg hd (mul_nonneg (le_trans zero_le_one hp) he.le)]
    have hx := scaleA_zero_lower (sourceDimension B j) B (sourceEpsilon B D) hdim he.le
    apply le_trans _ hx
    exact mul_nonneg (by positivity) (by nlinarith only [hu,he])
  · intro j _
    have he := sourceEpsilon_pos B D
    have hp : (1:ℝ) ≤ 2^(sourceDimension B j) := one_le_pow₀ (by norm_num)
    unfold scaleA
    norm_num only [pow_zero,mul_one]
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<2^(sourceDimension B j))).mpr
      (show 1+sourceEpsilon B D ≤ (1+sourceEpsilon B D)*2^(sourceDimension B j) from
        le_mul_of_one_le_right (by linarith only [he]) hp)
    linarith only [hh]

theorem sourceTargetScale_le (B D i : ℕ) (n : ℝ) (hB : 2 ≤ B) (hn : 1 ≤ n) :
    sourceTargetScale B D n i ≤ n := by
  simpa only [sourceTargetScale,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn (sourceScaleProduct_le_one B D i hB)

theorem sourceHalfMoment_sufficient (B D i : ℕ) {n : ℝ} (hB : 2 ≤ B) (hn : 1 < n) :
    10^6*(totalScoreExponent B D+B+1)*Real.log n ≤
      (sourceHalfMoment B D n i:ℝ)*Real.log (sourceTargetScale B D n i) := by
  have hlo := sourceScaleProduct_lower B D i hB
  have hs : 0 < sourceScaleProduct B D i := lt_of_lt_of_le (by positivity) hlo
  have hl : 0 < Real.log (sourceTargetScale B D n i) := by
    rw [sourceTargetScale,Real.log_rpow (by linarith : 0<n)]
    exact mul_pos hs (Real.log_pos hn)
  have hk := (div_le_iff₀ hl).mp (Nat.le_ceil
    ((10^8:ℝ)*2^(10*B)*(totalScoreExponent B D+B+1)*Real.log n/
      Real.log (sourceTargetScale B D n i)))
  apply le_trans _ hk
  have hd := (totalScoreExponent_bounds B D hB).1
  have hA : 0 ≤ (totalScoreExponent B D+B+1)*Real.log n := by positivity [hd,Real.log_pos hn]
  have hp : (1:ℝ) ≤ 2^(10*B) := one_le_pow₀ (by norm_num)
  have hc : (10^6:ℝ) ≤ 10^8*2^(10*B) := by linarith only [hp]
  nlinarith only [mul_le_mul_of_nonneg_right hc hA]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- The source base invariant, with literal target scales, moment ceiling,
 error threshold, count and overlap, uniformly in the joint deletion regime. -/
theorem source_initial_at_smallest_scale (B : ℕ) (ζ : ℝ) (hB : 2 ≤ B)
    (hζ : ζ∈Set.Ioo 0 1) {n q : ℕ→ℝ} (hn : Tendsto n atTop atTop)
    (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hH : Tendsto (fun t=>(q t)^3*Real.log (n t)) atTop atTop) :
    ∀ᶠt in atTop,Nonempty (ConcreteLevelPair (q t) ⟨(hq t).1.le,by linarith [(hq t).2]⟩
      (sourceTargetScale B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) 0)
      ((n t)^(-100*(totalScoreExponent B (sourceDepth B ζ ((q t)^3*Real.log (n t)))+B+1)))
      (11/5) (initialOverlapLower (q t)) ((sourceOverlapConstant (q t))^2) 0
      (sourceHalfMoment B (sourceDepth B ζ ((q t)^3*Real.log (n t))) (n t) 0)) := by
  let H := fun t=>(q t)^3*Real.log (n t)
  let Λ := fun t=>(q t)^(-3:ℤ)
  have hΛ (t) : 1 ≤ Λ t := by
    dsimp [Λ]
    rw [zpow_neg,zpow_ofNat,one_le_inv₀ (pow_pos (hq t).1 _)]
    exact pow_le_one₀ (hq t).1.le (by linarith [(hq t).2])
  have hrel (t) : Real.log (n t)=Λ t*H t := by
    dsimp [Λ,H]
    rw [zpow_neg,zpow_ofNat]
    field_simp [(hq t).1.ne']
  let D := fun t=>sourceDepth B ζ (H t)
  let N := fun t=>sourceTargetScale B (D t) (n t) 0
  have hN := sourceTargetScale_tendsto B ζ hB hζ (fun _=>0) hn hH hΛ hrel
  have hl := source_uniform_log_absorption B 0 ζ hB hζ (fun _=>0) hn hH hΛ hrel
  simp only [pow_zero,one_mul] at hl
  have hk := sourceHalfMoment_rate B ζ hB hζ (fun _=>0) hn hH hΛ hrel
  apply source_initial_level_eventually hN hn _ hq hl hk
  · filter_upwards [hn.eventually_gt_atTop 1] with t ht
    exact (sourceHalfMoment_bounds B (D t) 0 hB ht).1
  · filter_upwards [hn.eventually_gt_atTop 1] with t ht
    exact sourceHalfMoment_sufficient B (D t) 0 hB ht
  · filter_upwards [hn.eventually_ge_atTop 1] with t ht
    exact sourceTargetScale_le B (D t) 0 (n t) hB ht
  · filter_upwards [] with t
    have hd := (totalScoreExponent_bounds B (D t) hB).1
    have hbn : (0:ℝ) ≤ B := Nat.cast_nonneg _
    linarith only [hd,hbn]

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
