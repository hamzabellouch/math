import Mathlib
import OAI.Probability.SKFluctuations.PhysicalFiniteRawCover

namespace OAI

/-! Comparison Polynomial Room. -/

noncomputable section


namespace SKFluctuations
open Filter Set Hierarchy
open scoped Topology

 theorem comparisonCap_cubic_ratio (N E d δ v C : ℝ)
    (hN : 0<N) (hE : 0<E) (hd : 0<d) (hC : 0 ≤ C)
    (hupper : Real.sqrt N*E≤d^2) (hv : comparisonLowerScale N E d≤v)
    (hR : d^3/(N^2*E^3)≤1) :
    comparisonCap N δ (comparisonSmallMass N E) (comparisonConstraintLength N E d) E d (C*v) /
      (N*E*v)^2 ≤ N^δ*(2*(C+1)+(C+1)^2)*(d^3/(N^2*E^3)) := by
  have ha := comparisonLowerScale_pos hN hE hd
  have hrat := comparison_scale_ratios hN hE hd hupper
  have hu : comparisonSmallMass N E≤comparisonLowerScale N E d := by
    have hh := (div_le_iff₀ ha).mp (hrat.1.trans hR)
    simpa using hh
  have hp := comparisonCap_ratio N E d δ v C hN hE hd hC hv hu
  rw [hrat.2] at hp
  have hR0 : 0≤d^3/(N^2*E^3) := by positivity
  have hsq : (d^3/(N^2*E^3))^2 ≤ d^3/(N^2*E^3) := by nlinarith
  have ht := mul_le_mul_of_nonneg_left (add_le_add hrat.1 hsq) (show 0 ≤ C+1 by linarith)
  have ht' := mul_le_mul_of_nonneg_left
    (add_le_add_right ht ((C+1)^2*(d^3/(N^2*E^3)))) (Real.rpow_nonneg hN.le δ)
  exact hp.trans (by nlinarith [ht'])

 theorem eventually_comparisonCap_room {m δ C₀ C : ℝ} (hm : 0 < m)
    (hC₀ : 0 < C₀) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ E d v : ℝ, 0<E → 0<d →
      Real.sqrt (n:ℝ)*E≤d^2 →
      (n:ℝ)^(-(2:ℝ)/3+m)*d≤C₀*E →
      comparisonLowerScale n E d≤v →
      comparisonCap n δ (comparisonSmallMass n E) (comparisonConstraintLength n E d) E d (C*v) /
        ((n:ℝ)*E*v)^2 ≤
        ((2*(C+1)+(C+1)^2)*C₀^3)*(n:ℝ)^(-(3*m-δ)) := by
  have ht : Tendsto (fun n : ℕ => C₀^3*(n:ℝ)^(-3*m)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (show 0<3*m by positivity)).comp
      tendsto_natCast_atTop_atTop
    simpa [mul_neg] using hh.const_mul (C₀^3)
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro E d v hE hd hupper hlower hv
  have hN : 0<(n:ℝ) := by exact_mod_cast hn0
  have hR := comparison_cubic_margin hN hE hd hC₀ hlower
  have hcap := comparisonCap_cubic_ratio n E d δ v C hN hE hd hC hupper hv (hR.trans hn.le)
  have hp : 0≤(n:ℝ)^δ*(2*(C+1)+(C+1)^2) := by positivity
  calc _ ≤ _ := hcap
       _ ≤ (n:ℝ)^δ*(2*(C+1)+(C+1)^2)*(C₀^3*(n:ℝ)^(-3*m)) :=
         mul_le_mul_of_nonneg_left hR hp
       _ = ((2*(C+1)+(C+1)^2)*C₀^3)*((n:ℝ)^δ*(n:ℝ)^(-3*m)) := by ring
       _ = _ := by rw [← Real.rpow_add hN]; congr 2; ring

end SKFluctuations

 

 

namespace SKFluctuations
open Filter Set Hierarchy
open scoped Topology

 theorem comparison_strength_denominator {N E x v C : ℝ} {e : ℝ → ℝ}
    (hN : 0 < N) (_hE : 0 < E) (_hx : 0 < x) (hxv : x ≤ v) (hC : 0 ≤ C)
    (htest : N*E^2 ≤ C*e x*x^2)
    (hmono : MonotoneOn (fun r => e r*r^2) (Icc x v)) :
    (N*E*v)^2 ≤ C*(N*e v*v^4) := by
  have hh := hmono ⟨le_rfl,hxv⟩ ⟨hxv,le_rfl⟩ hxv
  have ht : N*E^2 ≤ C*(e v*v^2) := by nlinarith
  have ht' := mul_le_mul_of_nonneg_left ht (show 0 ≤ N*v^2 by positivity)
  nlinarith

 theorem comparisonCap_ge_rpow {N E d δ u : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hd : 0 < d) (hu : 0 ≤ u) :
    N^δ ≤ comparisonCap N δ (comparisonSmallMass N E) (comparisonConstraintLength N E d) E d u := by
  have hU := comparisonSmallMass_pos hN hE
  have ha := comparisonLowerScale_pos hN hE hd
  have hL : 0 < comparisonConstraintLength N E d := by
    unfold comparisonConstraintLength
    exact lt_min hU (by positivity)
  have hLU : comparisonConstraintLength N E d ≤ comparisonSmallMass N E := min_le_left _ _
  have huL : 1 ≤ (u+comparisonSmallMass N E)/comparisonConstraintLength N E d := by
    apply (le_div_iff₀ hL).mpr
    linarith
  unfold comparisonCap
  have hsecond : 0 ≤ (d^3/E)*(u+comparisonSmallMass N E)^2 := by positivity
  have hh := mul_le_mul_of_nonneg_left (show 1 ≤ (u+comparisonSmallMass N E)/comparisonConstraintLength N E d+
      (d^3/E)*(u+comparisonSmallMass N E)^2 by linarith) (Real.rpow_nonneg hN.le δ)
  simpa using hh

 theorem comparisonCap_strength_ratio {N E d δ x v C Ct : ℝ} {e : ℝ → ℝ}
    (hN : 0 < N) (hE : 0 < E) (hd : 0 < d) (hx : 0 < x) (hxv : x ≤ v)
    (hev : 0 < e v) (hC : 0 ≤ C) (hCt : 0 ≤ Ct)
    (htest : N*E^2 ≤ Ct*e x*x^2)
    (hmono : MonotoneOn (fun r => e r*r^2) (Icc x v)) :
    comparisonCap N δ (comparisonSmallMass N E) (comparisonConstraintLength N E d) E d (C*v)/(N*e v*v^4) ≤
      Ct*(comparisonCap N δ (comparisonSmallMass N E) (comparisonConstraintLength N E d) E d (C*v)/(N*E*v)^2) := by
  have hv : 0 < v := hx.trans_le hxv
  have hden := comparison_strength_denominator hN hE hx hxv hCt htest hmono
  have hcap : 0 ≤ comparisonCap N δ (comparisonSmallMass N E) (comparisonConstraintLength N E d) E d (C*v) :=
    (Real.rpow_nonneg hN.le δ).trans (comparisonCap_ge_rpow hN hE hd (mul_nonneg hC hv.le))
  apply (div_le_iff₀ (show 0 < N*e v*v^4 by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hden hcap
  have hh' := (le_div_iff₀ (show 0 < (N*E*v)^2 by positivity)).mpr hh
  convert hh' using 1; ring

end SKFluctuations

 

 

namespace SKFluctuations
open Filter Set Hierarchy
open scoped Topology

 theorem eventually_comparisonBalancedRawParameters {m δ K R κ₀ U V C₀ C Ct ε : ℝ}
    (hm : 0 < m) (hδ : 0 ≤ δ) (hmargin : δ < 3*m) (hK : 1 ≤ K)
    (hR : R ≤ 1) (hκ₀ : 0 < κ₀) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hC₀ : 0 < C₀) (hC : 0 ≤ C) (hCt : 0 ≤ Ct) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (E d xs a ab q : ℝ) (e : ℝ → ℝ),
      0 < E → 0 < d → 0 < xs → xs ≤ a → a ≤ R → ab ≤ K*a →
      1/(n:ℝ) ≤ a → 0 ≤ q → q ≤ C*a → C*a ≤ 1 →
      Real.sqrt (n:ℝ)*E ≤ d^2 → (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C₀*E →
      comparisonLowerScale n E d ≤ a → 0 < e a →
      (n:ℝ)*E^2 ≤ Ct*e xs*xs^2 →
      MonotoneOn (fun r =>  e r*r^2) (Icc xs a) →
      let A := comparisonCap n δ (comparisonSmallMass n E) (comparisonConstraintLength n E d) E d q
      ∃ J : ℕ, 1 ≤ J ∧ R ≤ (2:ℝ)^J*a ∧ (2:ℝ)^J*ab ≤ 2*K*R ∧
        0 < (1/Real.sqrt (A*((n:ℝ)*e a*a^4)))*a ∧
        (1/Real.sqrt (A*((n:ℝ)*e a*a^4)))*a ≤ a ∧
        ((J+3:ℕ):ℝ)^3*(U+V*(Real.log (n:ℝ))^4*(8*(K+1)/(κ₀/Real.log (n:ℝ))))*
          Real.sqrt (A/((n:ℝ)*e a*a^4))  ≤  ε := by
  let Cmargin := Ct*((2*(C+1)+(C+1)^2)*C₀^3)
  have hCm : 0 ≤ Cmargin := by dsimp [Cmargin]; positivity
  filter_upwards [eventually_balancedRawParameters (show 0 < 3*m-δ by linarith)
    hK hR hκ₀ hU hV hCm hε,
    eventually_comparisonCap_room (δ:=δ) hm hC₀ hC,eventually_ge_atTop (1:ℕ)] with n hn hroom hn1
  intro E d xs a ab q e hE hd hxs hxa haR hab hNa hq hqC hCa hupper hlower hasmall hea htest hmon
  have hN : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hN1 : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have ha : 0 < a := hxs.trans_le hxa
  have hUs := comparisonSmallMass_pos hN hE
  have hL : 0 < comparisonConstraintLength n E d := by
    unfold comparisonConstraintLength
    exact lt_min hUs (by have hc := comparisonLowerScale_pos hN hE hd; positivity)
  have hcapmono := comparisonCap_monotoneOn (δ:=δ) hN hUs.le hL hE hd.le
  have hcaple := hcapmono ⟨hq,hqC.trans hCa⟩ ⟨by positivity,hCa⟩ hqC
  have hden : 0 < (n:ℝ)*e a*a^4 := by positivity
  have hratio := (div_le_div_of_nonneg_right hcaple hden.le).trans
    (comparisonCap_strength_ratio (δ:=δ) hN hE hd hxs hxa hea hC hCt htest hmon)
  have hratio' := hratio.trans (mul_le_mul_of_nonneg_left
    (hroom E d a hE hd hupper hlower hasmall) hCt)
  have hA : 1 ≤ comparisonCap n δ (comparisonSmallMass n E) (comparisonConstraintLength n E d) E d q :=
    (Real.one_le_rpow hN1 hδ).trans (comparisonCap_ge_rpow hN hE hd hq)
  apply hn a ab _ _ ha haR hab hNa hA hden
  simpa only [Cmargin, mul_assoc] using hratio'

end SKFluctuations

 

 

namespace SKFluctuations
open Filter Set Hierarchy
open scoped Topology

 theorem comparisonTravel_log_bound {N E d D : ℝ}
    (hN : 1 ≤ N) (hE : 0 < E) (hd : 0 < d) (hdD : d ≤ D)
    (hupper : Real.sqrt N*E ≤ d^2) :
    Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E) ≤
      Real.log N+Real.log (1+D^2) := by
  have hN0 : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hs : 1 ≤ Real.sqrt N := by
    exact (Real.le_sqrt (by norm_num) hN0.le).2 (by simpa using hN)
  have hD : 0 ≤ D := hd.le.trans hdD
  have hEbound : E ≤ D^2 := by
    have hsq := pow_le_pow_left₀ hd.le hdD 2
    nlinarith
  have hU : comparisonSmallMass N E ≠ 0 := ne_of_gt (comparisonSmallMass_pos hN0 hE)
  have heq : (1+comparisonSmallMass N E)/comparisonSmallMass N E = 1+N*E := by
    unfold comparisonSmallMass
    field_simp
    ring
  rw [heq]
  calc
    Real.log (1+N*E) ≤ Real.log (N*(1+D^2)) := by
      apply Real.log_le_log (by positivity)
      nlinarith
    _ = _ := Real.log_mul hN0.ne' (by positivity)

 theorem comparisonTravel_ratio_bound {N E d D C m δ : ℝ}
    (hN : 1 ≤ N) (hE : 0 < E) (hd : 0 < d) (hdD : d ≤ D) (hC : 0 < C)
    (hupper : Real.sqrt N*E ≤ d^2)
    (hlower : N^(-(2:ℝ)/3+m)*d ≤ C*E) :
    ((comparisonConstraintLength N E d/N^δ)*
      Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E))/comparisonLowerScale N E d ≤
      C^3*N^(-(3*m+δ))*(Real.log N+Real.log (1+D^2)) := by
  have hN0 : 0<N := lt_of_lt_of_le zero_lt_one hN
  have ha := comparisonLowerScale_pos hN0 hE hd
  have hU := comparisonSmallMass_pos hN0 hE
  have hL : 0 < comparisonConstraintLength N E d := by
    unfold comparisonConstraintLength
    exact lt_min hU (by positivity)
  have hratio : comparisonConstraintLength N E d/comparisonLowerScale N E d ≤ C^3*N^(-3*m) :=
    (div_le_div_of_nonneg_right (min_le_left _ _) ha.le).trans
      ((comparison_scale_ratios hN0 hE hd hupper).1.trans (comparison_cubic_margin hN0 hE hd hC hlower))
  have hlog := comparisonTravel_log_bound hN hE hd hdD hupper
  have hlog0 : 0 ≤ Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E) := by
    apply Real.log_nonneg
    exact (one_le_div hU).mpr (by linarith)
  have hpow := Real.rpow_pos_of_pos hN0 (-δ)
  have hm := mul_le_mul hratio hlog hlog0 (by positivity : 0 ≤ C^3*N^(-3*m))
  have hm' := mul_le_mul_of_nonneg_right hm hpow.le
  have hpeq : N^(-3*m)*N^(-δ)=N^(-(3*m+δ)) := by
    rw [←Real.rpow_add hN0]
    congr 1
    ring
  have hpeq2 : N^(-δ)=(N^δ)⁻¹ := Real.rpow_neg hN0.le δ
  calc
    _ = (comparisonConstraintLength N E d/comparisonLowerScale N E d*
      Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E))*N^(-δ) := by
        rw [hpeq2]
        ring
    _ ≤ _ := hm'.trans_eq (by rw [show C^3*N^(-3*m)*(Real.log N+Real.log (1+D^2))*N^(-δ)=
        C^3*(N^(-3*m)*N^(-δ))*(Real.log N+Real.log (1+D^2)) by ring,hpeq])

 theorem eventually_comparisonTravel_small {C D m δ ε : ℝ} (hC : 0<C)
    (hκ : 0<3*m+δ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ E d : ℝ, 0<E → 0<d → d≤D →
      Real.sqrt (n:ℝ)*E ≤ d^2 → (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C*E →
      (comparisonConstraintLength n E d/(n:ℝ)^δ)*
        Real.log ((1+comparisonSmallMass n E)/comparisonSmallMass n E) ≤
        ε*comparisonLowerScale n E d := by
  have h₁ := tendsto_raw_log_margin 1 hκ
  have h₀ := tendsto_raw_log_margin 0 hκ
  have ht : Tendsto (fun n : ℕ => C^3*(n:ℝ)^(-(3*m+δ))*
      (Real.log (n:ℝ)+Real.log (1+D^2))) atTop (𝓝 0) := by
    convert (h₁.add (h₀.mul_const (Real.log (1+D^2)))).const_mul (C^3) using 1
    · funext n
      simp only [pow_one,pow_zero,one_mul]
      ring
    · simp
  filter_upwards [eventually_ge_atTop 1,ht.eventually (gt_mem_nhds hε)] with n hn ht
  intro E d hE hd hdD hupper hlower
  have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hh := comparisonTravel_ratio_bound (δ:=δ) hN hE hd hdD hC hupper hlower
  have ha := comparisonLowerScale_pos (lt_of_lt_of_le zero_lt_one hN) hE hd
  exact (div_le_iff₀ ha).mp (hh.trans ht.le)

end SKFluctuations

 

 

namespace SKFluctuations
open Filter Set Hierarchy
open scoped Topology

 theorem eventually_comparisonSmallMass_small {C m ε : ℝ}
    (hC : 0 < C) (hm : 0 < m) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ E d : ℝ, 0 < E → 0 < d →
      Real.sqrt (n:ℝ)*E ≤ d^2 → (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C*E →
      comparisonSmallMass n E  <  ε*comparisonLowerScale n E d := by
  have ht : Tendsto (fun n : ℕ => C^3*(n:ℝ)^(-3*m)) atTop (𝓝 0) := by
    simpa using (((tendsto_rpow_neg_atTop (show 0 < 3*m by positivity)).comp
      tendsto_natCast_atTop_atTop).const_mul (C^3))
  filter_upwards [ht.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro E d hE hd hupper hlower
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn0
  have ha := comparisonLowerScale_pos hN hE hd
  exact (div_lt_iff₀ ha).mp (((comparison_scale_ratios hN hE hd hupper).1.trans
    (comparison_cubic_margin hN hE hd hC hlower)).trans_lt hn)

 theorem eventually_comparisonLowerScale_depth {C m : ℝ} (hC : 0 < C) (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, ∀ E d : ℝ, 0 < E → 0 < d →
      (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C*E → 1/(n:ℝ) ≤ comparisonLowerScale n E d := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^((5:ℝ)/6+m)) atTop atTop :=
    (tendsto_rpow_atTop (show 0 < (5:ℝ)/6+m by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop C),eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro E d hE hd hlower
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hs : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hN
  have hp : (n:ℝ)*Real.sqrt (n:ℝ)*(n:ℝ)^(-(2:ℝ)/3+m)=(n:ℝ)^((5:ℝ)/6+m) := by
    rw [Real.sqrt_eq_rpow]
    nth_rw 1 [←Real.rpow_one (n:ℝ)]
    rw [←Real.rpow_add hN,←Real.rpow_add hN]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_left hlower (mul_nonneg hN.le hs.le)
  have hdC : C*d  ≤  (n:ℝ)*Real.sqrt (n:ℝ)*(C*E) := by
    calc C*d  ≤  (n:ℝ)^((5:ℝ)/6+m)*d := mul_le_mul_of_nonneg_right hn hd.le
         _ = (n:ℝ)*Real.sqrt (n:ℝ)*((n:ℝ)^(-(2:ℝ)/3+m)*d) := by rw [←mul_assoc,hp]
         _  ≤  _ := hmul
  unfold comparisonLowerScale
  have hcancel : C*d ≤ C*((n:ℝ)*Real.sqrt (n:ℝ)*E) := by nlinarith [hdC]
  have hd' : d ≤ (n:ℝ)*Real.sqrt (n:ℝ)*E := (mul_le_mul_iff_right₀ hC).mp hcancel
  apply (div_le_div_iff₀ hN hd).mpr
  nlinarith [hd']

end SKFluctuations

 

 

namespace SKFluctuations
open Filter Set Hierarchy
open scoped Topology

 theorem eventually_comparison_regular_band_margins
    (ℓ : ℕ) {m δ B cl cu Az Ca K R C μ F κ₀ C₀ Ct D : ℝ}
    (hm : 0 < m) (hδ : 0 ≤ δ) (hδm : δ < 3*m)
    (hB : 2 ≤ B) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hBcu : cu ≤ B) (hBA : 2*cu*Az < B) (hCa : 0 < Ca) (hCaB : B/cl ≤ Ca)
    (hK : 1 ≤ K) (hKcu : 2*cu/cl ≤ K)
    (_hR : 0 < R) (hR1 : R ≤ 1) (hKR : 2*K*R ≤ 1) (hcuR : 2*cu*R ≤ 1)
    (hC : 3*B/cl+1 < C) (_hμ : 0 < μ) (hμR : Ca*μ ≤ R)
    (hκ₀ : 0 < κ₀) (hC₀ : 0 < C₀) (hCt : 0 ≤ Ct) :
    ∀ᶠ n : ℕ in atTop, ∀ E d xs v r₀ z a ab ac : ℝ,
      0 < E → 0 < d → d ≤ D → 0 < xs →
      comparisonLowerScale n E d ≤ xs → xs ≤ v → v < μ →
      Real.sqrt (n:ℝ)*E ≤ d^2 → (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C₀*E →
      r₀ ≤ comparisonSmallMass n E → z ∈ Icc r₀ 1 → z ≤ Az*xs →
      a ∈ Icc r₀ 1 → ab ∈ Icc r₀ 1 → ac ∈ Icc r₀ 1 →
    ∀ (α e : ℝ → ℝ), Monotone α → α a=B*v → α ab=2*B*v → α ac=3*B*v →
      (∀ r ∈ Icc z 1, cl*r ≤ α r ∧ α r ≤ cu*r) →
      ContDiff ℝ 1 e → (∀ r ∈ Icc r₀ 1, 0 < e r) →
      (∀ r ∈ Ioc r₀ 1, comparisonLogSlope e r ∈ Icc (0:ℝ) 1) →
      (∀ r ∈ Icc z 1, κ₀/Real.log (n:ℝ) ≤ 1-comparisonLogSlope e r) →
      (n:ℝ)*E^2 ≤ Ct*e xs*xs^2 →
    let M := comparisonCap n δ (comparisonSmallMass n E) (comparisonConstraintLength n E d) E d
    ∃ η : ℝ, ∃ J : ℕ,
      1 ≤ J ∧ (n:ℝ)^(-δ)*comparisonSmallMass n E < B*v ∧
      ac+(comparisonConstraintLength n E d/(n:ℝ)^δ)*
        Real.log ((1+comparisonSmallMass n E)/comparisonSmallMass n E) < C*v ∧
      xs ≤ a ∧ a ≤ Ca*v ∧ ab ≤ K*a ∧ cl*a ≤ B*v ∧ B*v ≤ K*cu*a ∧
      0 < M (2*B*v) ∧ 0 < η ∧ η ≤ a ∧ r₀ < a/2 ∧
      η=(1/Real.sqrt (M (2*B*v)*((n:ℝ)*e a*a^4)))*a ∧
      (2:ℝ)^J*ab ≤ 1 ∧ R ≤ (2:ℝ)^J*a ∧
      (∀ r ∈ Icc (a/2) ((2:ℝ)^J*ab), cl*r ≤ α r ∧ α r ≤ cu*r) ∧
      (∀ r ∈ Icc (a/2) ((2:ℝ)^J*ab), κ₀/Real.log (n:ℝ) ≤ 1-comparisonLogSlope e r) ∧
      ((J+3:ℕ):ℝ)^3*(4*(K+1)*cu*nearPairMomentConstant (ℓ+1)^(((ℓ+1:ℕ):ℝ)⁻¹)*
        (1+(K+1)*cu)^2 +
        4*K*cu*(projectionLpConstant ℓ)^2*(Real.log (n:ℝ))^4*(F^2/((cl/2)/4)^2)*
          (8*(K+1)/(κ₀/Real.log (n:ℝ))))*
        Real.sqrt (M (2*B*v)/((n:ℝ)*e a*a^4)) ≤
        (cl/(4*Ca))^2/(1+(2*(ℓ+1:ℕ):ℝ)^2/3) := by
  let U := 4*(K+1)*cu*nearPairMomentConstant (ℓ+1)^(((ℓ+1:ℕ):ℝ)⁻¹)*(1+(K+1)*cu)^2
  let V := 4*K*cu*(projectionLpConstant ℓ)^2*(F^2/((cl/2)/4)^2)
  let ε := (cl/(4*Ca))^2/(1+(2*(ℓ+1:ℕ):ℝ)^2/3)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hU : 0 ≤ U := by
    have hc := nearPairMomentConstant_nonneg (ℓ+1)
    dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  filter_upwards [eventually_comparisonBalancedRawParameters (R:=R) hm hδ hδm hK hR1 hκ₀ hU hV hC₀
      (show 0 ≤ 2*cu by positivity) hCt hε,
    eventually_comparisonSmallMass_small hC₀ hm (show (0:ℝ) < 1 by norm_num),
    eventually_comparisonLowerScale_depth hC₀ hm,
    eventually_comparisonTravel_small (D:=D) hC₀ (show 0 < 3*m+δ by linarith) (show (0:ℝ) < 1 by norm_num),
    eventually_ge_atTop (1:ℕ)] with n hbalanced hsmall hdepth htravel hn
  intro E d xs v r₀ z a ab ac hE hd hdD hxs has hxsV hvμ hupper hlower hr₀U hz hzxs
    ha hab hac α e hα hαa hαb hαc hreg he hep hes hslow htest
  dsimp only
  have hN1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < (n:ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hv : 0 < v := hxs.trans_le hxsV
  have hB0 : 0 < B := by linarith
  have hUsmall : comparisonSmallMass n E < comparisonLowerScale n E d := by
    simpa only [one_mul] using hsmall E d hE hd hupper hlower
  have hUxs : comparisonSmallMass n E < xs := hUsmall.trans_le has
  have hr₀xs : r₀ < xs := hr₀U.trans_lt hUxs
  have hstart : cu*z < B*v := by
    have h₁ := mul_le_mul_of_nonneg_left hzxs hcu.le
    have h₂ := mul_le_mul_of_nonneg_left hxsV (mul_nonneg hcu.le hAz)
    have h₃ := mul_lt_mul_of_pos_right hBA hv
    nlinarith only [h₁,h₂,h₃,mul_nonneg (mul_nonneg hcu.le hAz) hv.le]
  have hA := radius_in_regular_region hα ha hz hαa hstart hreg
  have hB' := radius_in_regular_region hα hab hz hαb (by nlinarith only [hstart,mul_pos hB0 hv]) hreg
  have hC' := radius_in_regular_region hα hac hz hαc (by nlinarith only [hstart,mul_pos hB0 hv]) hreg
  have ha0 : 0 < a := by nlinarith only [hA.2.2,hcu,mul_pos hB0 hv]
  have hxa : xs ≤ a := by
    have hh := mul_le_mul_of_nonneg_right hBcu hv.le
    exact hxsV.trans ((mul_le_mul_iff_right₀ hcu).mp (hh.trans hA.2.2))
  have hav : a ≤ Ca*v := by
    have hh : a ≤ (B/cl)*v := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hcl).mpr
      nlinarith only [hA.2.1]
    exact hh.trans (mul_le_mul_of_nonneg_right hCaB hv.le)
  have haR : a ≤ R := hav.trans ((mul_le_mul_of_nonneg_left hvμ.le hCa.le).trans hμR)
  have hba : ab ≤ K*a := by
    have hh : ab ≤ (2*cu/cl)*a := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hcl).mpr
      nlinarith only [hA.2.2,hB'.2.1]
    exact hh.trans (mul_le_mul_of_nonneg_right hKcu ha0.le)
  have hmasslo : cl*a ≤ B*v := hA.2.1
  have hmasshi : B*v ≤ K*cu*a := by nlinarith only [hA.2.2,mul_le_mul_of_nonneg_right hK (mul_nonneg hcu.le ha0.le)]
  have hqC : 2*B*v ≤ (2*cu)*a := by nlinarith only [hA.2.2]
  have hCa1 : (2*cu)*a ≤ 1 := (mul_le_mul_of_nonneg_left haR (by positivity)).trans hcuR
  have hza2 : z < a/2 := by
    have h₁ := mul_le_mul_of_nonneg_left hzxs (show 0 ≤ 2*cu by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hxsV (show 0 ≤ 2*cu*Az by positivity)
    have h₃ := mul_lt_mul_of_pos_right hBA hv
    nlinarith only [h₁,h₂,h₃,hA.2.2,hcu]
  have hemon : MonotoneOn (fun r => e r*r^2) (Icc xs a) :=
    (strength_radial_monotonicities hxs hxa
      (fun r _ => he.differentiable (by norm_num) |>.differentiableAt)
      (fun r hr => hep r ⟨hr₀xs.le.trans hr.1,hr.2.trans ha.2⟩)
      (fun r hr => hes r ⟨hr₀xs.trans_le hr.1,hr.2.trans ha.2⟩)).2.2
  obtain ⟨J,hJ,hreach,hstop,hη,hηa,hloss⟩ := hbalanced E d xs a ab (2*B*v) e hE hd hxs hxa haR hba
    ((hdepth E d hE hd hlower).trans (has.trans hxa)) (by positivity) hqC hCa1 hupper hlower
    (has.trans hxa) (hep a ha) htest hemon
  refine ⟨_,J,hJ,?_,?_,hxa,hav,hba,hmasslo,hmasshi,?_,hη,hηa,hz.1.trans_lt hza2,rfl,hstop.trans hKR,hreach,?_,?_,?_⟩
  · have hp : (n:ℝ)^(-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (neg_nonpos.mpr hδ)
    have hU0 := comparisonSmallMass_pos hN hE
    have hh := mul_le_mul_of_nonneg_right hp hU0.le
    have hh' : comparisonSmallMass n E < B*v := hUxs.trans_le (hxsV.trans (by nlinarith only [hB,hv]))
    exact hh.trans_lt (by simpa only [one_mul] using hh')
  · have hh := htravel E d hE hd hdD hupper hlower
    have hc' : ac ≤ (3*B/cl)*v := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hcl).mpr
      nlinarith only [hC'.2.1]
    have hc'' := mul_lt_mul_of_pos_right hC hv
    nlinarith only [hh,has,hxsV,hc',hc'']
  · exact lt_of_lt_of_le (Real.rpow_pos_of_pos hN δ) (comparisonCap_ge_rpow hN hE hd (by positivity))
  · intro r hr
    exact hreg r ⟨hza2.le.trans hr.1,hr.2.trans (hstop.trans hKR)⟩
  · intro r hr
    exact hslow r ⟨hza2.le.trans hr.1,hr.2.trans (hstop.trans hKR)⟩
  · simpa only [U,V,ε,mul_assoc,mul_left_comm,mul_comm] using hloss

end SKFluctuations

 

 

namespace SKFluctuations
open Set

 theorem finite_dyadic_small_cover {x B μ : ℝ} (hx : 0 < x) (hB : 0 < B)
    (_hμ : 0 < μ) (hμB : 3*B*μ ≤ 1) :
    ∃ vs : Finset ℝ, (∀ v ∈ vs, x≤v ∧ v<μ ∧ 3*B*v≤1) ∧
      ∀ y : ℝ, x ≤ y → μ ≤ y ∨ ∃ v ∈ vs, v ≤ y ∧ y < 2*v := by
  obtain ⟨N,hN⟩ := exists_nat_gt (μ/x)
  classical
  let vs := ((Finset.range N).image (fun j : ℕ => (2:ℝ)^j*x)).filter (fun v => v<μ)
  refine ⟨vs,?_,?_⟩
  · intro v hv
    obtain ⟨hj,hv⟩ := Finset.mem_filter.mp hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hj
    refine ⟨?_,hv,?_⟩
    · simpa using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hx.le
    · exact (mul_le_mul_of_nonneg_left hv.le (by positivity : 0≤3*B)).trans hμB
  · intro y hxy
    by_cases hmy : μ ≤ y
    · exact Or.inl hmy
    · right
      have hym : y < μ := lt_of_not_ge hmy
      have hrat : 1 ≤ y/x := (le_div_iff₀ hx).mpr (by simpa using hxy)
      obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near hrat (show (1:ℝ) < 2 by norm_num)
      have hvy : (2:ℝ)^j*x ≤ y := (le_div_iff₀ hx).mp hlo
      have hyv : y < 2*((2:ℝ)^j*x) := by
        have hh := (div_lt_iff₀ hx).mp hhi
        rw [pow_succ] at hh
        nlinarith
      have hjpow : (j:ℝ) < (2:ℝ)^j := by exact_mod_cast (Nat.lt_two_pow_self (n := j))
      have hjN : j < N := by
        have hyx : y/x < μ/x := div_lt_div_of_pos_right hym hx
        have hh : (j:ℝ) < N := lt_trans (hjpow.trans_le hlo) (hyx.trans hN)
        exact_mod_cast hh
      refine ⟨(2:ℝ)^j*x,Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hjN,rfl⟩,?_⟩,hvy,hyv⟩
      exact hvy.trans_lt hym

end SKFluctuations

 

 

namespace SKFluctuations
open Set Hierarchy

 structure RawFutureCutFamily (xs B μ u₀ : ℝ) (u : PositiveMass) where
  bands : Finset ℝ
  p : ℝ → PositiveMass
  q : ℝ → PositiveMass
  t : ℝ → PositiveMass
  retained : List PositiveMass
  observation_mem : u ∈ retained
  retained_le_one : ∀ w ∈ retained, w.val ≤ 1
  band_bounds : ∀ v ∈ bands, xs ≤ v ∧ v < μ
  mass_values : ∀ v ∈ bands, (p v).val=B*v ∧ (q v).val=2*B*v ∧ (t v).val=3*B*v
  cut_order : ∀ v ∈ bands, p v ∈ retained ∧ q v ∈ retained ∧ u₀ < (p v).val ∧
    (p v).val < (q v).val ∧ (q v).val < (t v).val ∧ (t v).val ≤ 1 ∧ 2*v ≤ (p v).val
  cover : ∀ y : ℝ, xs ≤ y → μ ≤ y ∨ ∃ v ∈ bands, v ≤ y ∧ y < 2*v

 theorem rawFutureCutFamily_nonempty {xs B μ u₀ : ℝ} (u : PositiveMass)
    (hxs : 0 < xs) (hB : 2 ≤ B) (hμ : 0 < μ) (hμB : 3*B*μ ≤ 1)
    (hu₀ : u₀ ≤ xs) (hu : u.val ≤ 1) : Nonempty (RawFutureCutFamily xs B μ u₀ u) := by
  classical
  have hB0 : 0 < B := by linarith only [hB]
  obtain ⟨vs,hvs,hcover⟩ := finite_dyadic_small_cover hxs hB0 hμ hμB
  let p : ℝ → PositiveMass := fun v => ⟨B*max v xs,mul_pos hB0 (hxs.trans_le (le_max_right v xs))⟩
  let q : ℝ → PositiveMass := fun v => ⟨2*B*max v xs,by positivity⟩
  let t : ℝ → PositiveMass := fun v => ⟨3*B*max v xs,by positivity⟩
  let us := u :: vs.toList.flatMap (fun v => [p v,q v,t v])
  have hval : ∀ v ∈ vs, (p v).val=B*v ∧ (q v).val=2*B*v ∧ (t v).val=3*B*v := by
    intro v hv
    dsimp only [p,q,t]
    rw [max_eq_left (hvs v hv).1]
    exact ⟨rfl,rfl,rfl⟩
  have hmem : ∀ v ∈ vs, p v ∈ us ∧ q v ∈ us ∧ t v ∈ us := by
    intro v hv
    have hv' : v ∈ vs.toList := Finset.mem_toList.mpr hv
    refine ⟨List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨v,hv',by simp⟩),
      List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨v,hv',by simp⟩),
      List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨v,hv',by simp⟩)⟩
  refine ⟨⟨vs,p,q,t,us,by exact List.mem_cons_self,?_,?_,hval,?_,hcover⟩⟩
  · intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hu
    obtain ⟨v,hv,hw⟩ := List.mem_flatMap.mp hw
    have hv' := Finset.mem_toList.mp hv
    have hvp := hxs.trans_le (hvs v hv').1
    obtain ⟨hp,hq,ht⟩ := hval v hv'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl | rfl
    · rw [hp]
      nlinarith only [(hvs v hv').2.2,mul_pos hB0 hvp]
    · rw [hq]
      nlinarith only [(hvs v hv').2.2,mul_pos hB0 hvp]
    · rw [ht]
      exact (hvs v hv').2.2
  · intro v hv
    exact ⟨(hvs v hv).1,(hvs v hv).2.1⟩
  · intro v hv
    obtain ⟨hp,hq,ht⟩ := hval v hv
    have hvp := hxs.trans_le (hvs v hv).1
    refine ⟨(hmem v hv).1,(hmem v hv).2.1,?_,?_,?_,?_,?_⟩
    all_goals simp only [hp,hq,ht]
    · nlinarith only [hu₀,(hvs v hv).1,hvp,hB]
    · nlinarith only [mul_pos hB0 hvp]
    · nlinarith only [mul_pos hB0 hvp]
    · exact (hvs v hv).2.2
    · exact mul_le_mul_of_nonneg_right hB hvp.le

end SKFluctuations

end

end OAI
