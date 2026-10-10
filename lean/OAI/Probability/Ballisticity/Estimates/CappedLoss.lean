import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace DirectionalTransience

noncomputable def cappedLogLoss (a q : ℝ) : ℝ :=
  if q=0 then a else min a (-Real.log q)

lemma cappedLogLoss_bounds {a q : ℝ} (ha : 0≤a) (hq : 0≤q) (hq1 : q≤1) :
    0≤cappedLogLoss a q ∧ cappedLogLoss a q≤a := by
  unfold cappedLogLoss
  split
  · exact ⟨ha,le_rfl⟩
  · have hlog : Real.log q≤0 := Real.log_nonpos hq hq1
    exact ⟨le_min ha (neg_nonneg.mpr hlog),min_le_left _ _⟩

lemma lt_cappedLogLoss_iff {a q x : ℝ} (hq : 0≤q) (hx : 0≤x) :
    x<cappedLogLoss a q ↔ x<a ∧ q<Real.exp (-x) := by
  by_cases hnonpos : a ≤ 0
  · have hax : a ≤ x := hnonpos.trans hx
    unfold cappedLogLoss
    split
    · simp only [not_lt_of_ge hax, false_and]
    · simp only [lt_min_iff, not_lt_of_ge hax, false_and]
  unfold cappedLogLoss
  by_cases hq0 : q=0
  · simp [hq0,Real.exp_pos]
  · rw [ite_eq_right hq0,lt_min_iff]
    constructor
    · rintro ⟨ha,hq'⟩
      refine ⟨ha,?_⟩
      have : Real.log q < -x := by linarith
      simpa [Real.exp_log (lt_of_le_of_ne hq (Ne.symm hq0))] using Real.exp_lt_exp.mpr this
    · rintro ⟨ha,hq'⟩
      have hh := Real.log_lt_log (lt_of_le_of_ne hq (Ne.symm hq0)) hq'
      rw [Real.log_exp] at hh
      exact ⟨ha,by linarith⟩

lemma measurable_cappedLogLoss {Ω : Type*} [MeasurableSpace Ω]
    (a : ℝ) (q : Ω → ℝ) (hq : Measurable q) :
    Measurable (fun ω => cappedLogLoss a (q ω)) := by
  unfold cappedLogLoss
  exact Measurable.ite (measurableSet_eq_fun hq measurable_const)
    measurable_const (measurable_const.min hq.log.neg)

lemma integrable_cappedLogLoss {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (a : ℝ) (ha : 0≤a)
    (q : Ω → ℝ) (hq : Measurable q) (hq0 : ∀ ω, 0≤q ω) (hq1 : ∀ ω, q ω≤1) :
    Integrable (fun ω => cappedLogLoss a (q ω)) μ := by
  apply (integrable_const a).mono' (measurable_cappedLogLoss a q hq).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (cappedLogLoss_bounds ha (hq0 ω) (hq1 ω)).1]
    exact (cappedLogLoss_bounds ha (hq0 ω) (hq1 ω)).2

lemma integrable_exp_cappedLogLoss {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (a t : ℝ) (ha : 0≤a) (ht : 0≤t)
    (q : Ω → ℝ) (hq : Measurable q) (hq0 : ∀ ω, 0≤q ω) (hq1 : ∀ ω, q ω≤1) :
    Integrable (fun ω => Real.exp (t*cappedLogLoss a (q ω))) μ := by
  apply (integrable_const (Real.exp (t*a))).mono'
    ((measurable_cappedLogLoss a q hq).const_mul t).exp.aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (cappedLogLoss_bounds ha (hq0 ω) (hq1 ω)).2 ht)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace DirectionalTransience

lemma exp_moment_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0≤X ω) (a : ℝ) (hXa : ∀ ω, X ω≤a)
    (t D : ℝ) (ht : 0<t) (hD : 0≤D)
    (htail : ∀ x : ℝ, 0≤x → μ {ω | x<X ω} ≤ ENNReal.ofReal (D*Real.exp (-2*t*x))) :
    (∫ ω, Real.exp (t*X ω) ∂μ) ≤ 1+D := by
  have hE : Integrable (fun ω => Real.exp (t*X ω)) μ := by
    apply (integrable_const (Real.exp (t*a))).mono' (hX.const_mul t).exp.aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hXa ω) ht.le)
  have hg : Continuous (fun x : ℝ => t*Real.exp (t*x)) := by fun_prop
  have hprim (x : ℝ) : (∫ u in 0..x, t*Real.exp (t*u))=Real.exp (t*x)-1 := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => Real.exp (t*u)) (f' := fun u => t*Real.exp (t*u))
      (a := 0) (b := x) (fun u _ => by
        simpa only [id_eq,mul_one,mul_comm] using ((hasDerivAt_id u).const_mul t).exp) (hg.intervalIntegrable 0 x)
    simpa only [mul_zero, Real.exp_zero] using hh
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ hX0) hX.aemeasurable (fun x _ => hg.intervalIntegrable 0 x)
    (g := fun x => t*Real.exp (t*x)) (ae_of_all _ fun x => mul_nonneg ht.le (Real.exp_pos _).le)
  simp_rw [hprim] at hlayer
  have hi : IntegrableOn (fun x : ℝ => D*t*Real.exp (-t*x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ht) 0).const_mul (D*t)
  have hint : (∫ x in Ioi 0, D*t*Real.exp (-t*x))=D := by
    rw [integral_const_mul,integral_exp_mul_Ioi (neg_lt_zero.mpr ht)]
    simp only [mul_zero,Real.exp_zero]
    field_simp
  have hbound : (∫⁻ x in Ioi 0, μ {ω | x<X ω} * ENNReal.ofReal (t*Real.exp (t*x))) ≤ ENNReal.ofReal D := by
    calc
      _ ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal (D*t*Real.exp (-t*x)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        calc
          _ ≤ ENNReal.ofReal (D*Real.exp (-2*t*x))*ENNReal.ofReal (t*Real.exp (t*x)) :=
            by gcongr; exact htail x hx.le
          _ = ENNReal.ofReal (D*t*Real.exp (-t*x)) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg hD (Real.exp_pos _).le)]
            congr 1
            calc
              _ = D*t*(Real.exp (-2*t*x)*Real.exp (t*x)) := by ring
              _ = _ := by rw [← Real.exp_add]; congr 2; ring
      _ = ENNReal.ofReal D := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by positivity),hint]
  have hnon : ∀ ω, 0≤Real.exp (t*X ω)-1 := fun ω => sub_nonneg.mpr
    (Real.one_le_exp_iff.mpr (mul_nonneg ht.le (hX0 ω)))
  have hId := ofReal_integral_eq_lintegral_ofReal (f := fun ω => Real.exp (t*X ω)-1)
    (hE.sub (integrable_const 1)) (ae_of_all _ hnon)
  rw [← hId] at hlayer
  have hh : (∫ ω, Real.exp (t*X ω)-1 ∂μ)≤D :=
    (ENNReal.ofReal_le_ofReal_iff hD).mp (hlayer.trans_le hbound)
  rw [integral_sub hE (integrable_const 1),integral_const] at hh
  simpa using (show (∫ ω, Real.exp (t*X ω) ∂μ)≤1+D by simpa [add_comm] using (sub_le_iff_le_add.mp hh))

end DirectionalTransience

end

section

open Filter
open scoped Topology
namespace DirectionalTransience

lemma exp_le_half_exp {u v : ℝ} (h : u+Real.log 2≤v) :
    Real.exp u≤Real.exp v/2 := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ)<2)]
  calc
    Real.exp u*2 = Real.exp (u+Real.log 2) := by rw [Real.exp_add,Real.exp_log (by norm_num)]
    _ ≤ Real.exp v := Real.exp_le_exp.mpr h

lemma late_step_tail_arithmetic (lam C θ K : ℝ) (hlam : 0<lam) (hC : 0≤C)
    (hθ : 0<θ) (hK : 0≤K) :
    ∃ C₀ : ℝ, 0<C₀ ∧ ∀ (k : ℕ), 1≤k → ∀ a : ℝ, 1≤a →
      ∀ D : ℕ → ℝ, (∀ L, 0≤D L) → ∃ l₀ : ℕ,
      ∀ l≥l₀, ∀ T : ℝ → ℝ, (∀ x, T x≤1) →
        (∀ L : ℕ, 1≤L → ∀ x : ℝ, (k:ℝ)*L*K≤x → x≤a*(l+1) →
          T x≤(Real.exp (C*k-lam*x/L)+D L*Real.exp (x/L-θ*l))^L) →
        (∀ x : ℝ, 0≤x → x≤a*(l+1) → T x≤Real.exp (C₀*k-lam*x/2)) ∧
        T (a*(l+1))≤Real.exp (-lam*(a*(l+1))/2) := by
  let C₀ := C+lam*K+2
  have hC₀ : 0<C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀,hC₀,?_⟩
  intro k hk a ha D hD
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hk0 : 0≤(k:ℝ) := Nat.cast_nonneg k
  have ha0 : 0<a := by linarith
  let c := min (1/2:ℝ) (θ/(4*(1+lam)))
  have hc : 0<c := lt_min (by norm_num) (div_pos hθ (by positivity))
  have hc1 : c≤1/2 := min_le_left _ _
  have hcθ : (1+lam)*c≤θ/4 := by
    have hh := min_le_right (1/2:ℝ) (θ/(4*(1+lam)))
    have hh' := (le_div_iff₀ (show 0<4*(1+lam) by positivity)).mp hh
    dsimp [c]
    nlinarith only [hh']
  obtain ⟨L,hL⟩ := exists_nat_gt (max 1 (4*(1+lam)*a/θ))
  have hL1 : 1≤L := by have := (le_max_left 1 (4*(1+lam)*a/θ)).trans_lt hL; exact_mod_cast this.le
  have hL0 : 0<(L:ℝ) := by exact_mod_cast (by omega : 0<L)
  have hθL : 4*(1+lam)*a<θ*L := by
    have hh := (le_max_right 1 (4*(1+lam)*a/θ)).trans_lt hL
    exact (div_lt_iff₀ hθ).mp hh |>.trans_eq (mul_comm _ _)
  let D₁ := max (D 1) 1
  let D₂ := max (D L) 1
  have hD₁ : 0<D₁ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hD₂ : 0<D₂ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let R := max 1 (max (2*Real.log D₁/θ)
    (max (2*L*(C*k+Real.log 2)/(lam*c))
      (max ((k:ℝ)*L*K/c) (2*Real.log (2*D₂)/θ))))
  obtain ⟨l₀,hl₀⟩ := exists_nat_gt R
  refine ⟨l₀,?_⟩
  intro l hl T hT htail
  have hlR : R≤(l:ℝ) := hl₀.le.trans (by exact_mod_cast hl)
  have hl1 : (1:ℝ)≤l := (le_max_left _ _).trans hlR
  have hl0 : 0≤(l:ℝ) := Nat.cast_nonneg l
  have hR₂ : max (2*Real.log D₁/θ)
      (max (2*L*(C*k+Real.log 2)/(lam*c))
        (max ((k:ℝ)*L*K/c) (2*Real.log (2*D₂)/θ)))≤(l:ℝ) := (le_max_right _ _).trans hlR
  have hlog₁ : Real.log D₁≤θ*l/2 := by
    have hh := (div_le_iff₀ hθ).mp ((le_max_left _ _).trans hR₂)
    nlinarith only [hh]
  have hR₃ := (le_max_right _ _).trans hR₂
  have hfirst : 2*L*(C*k+Real.log 2)≤lam*c*l := by
    have hh := (div_le_iff₀ (mul_pos hlam hc)).mp ((le_max_left _ _).trans hR₃)
    nlinarith only [hh]
  have hR₄ := (le_max_right _ _).trans hR₃
  have hell : (k:ℝ)*L*K≤c*l := by
    have hh := (div_le_iff₀ hc).mp ((le_max_left _ _).trans hR₄)
    nlinarith only [hh]
  have hlog₂ : Real.log (2*D₂)≤θ*l/2 := by
    have hh := (div_le_iff₀ hθ).mp ((le_max_right _ _).trans hR₄)
    nlinarith only [hh]
  have hlarge (x : ℝ) (hxc : c*l≤x) (hxa : x≤a*(l+1)) :
      T x≤Real.exp (-lam*x/2) := by
    have hx0 : 0≤x := (mul_nonneg hc.le hl0).trans hxc
    have hbound := htail L hL1 x (hell.trans hxc) hxa
    have hab : Real.exp (C*k-lam*x/L)≤Real.exp (-lam*x/(2*L))/2 := by
      apply exp_le_half_exp
      have hfh : 2*L*(C*k+Real.log 2)≤lam*x := hfirst.trans
        (by nlinarith only [mul_le_mul_of_nonneg_left hxc hlam.le])
      have hf : C*k+Real.log 2≤lam*x/(2*L) :=
        (le_div_iff₀ (mul_pos (by norm_num) hL0)).mpr (by nlinarith only [hfh])
      have hid : lam*x/L=2*(lam*x/(2*L)) := by field_simp
      rw [hid]
      ring_nf at hf ⊢
      linarith only [hf]
    have hfrac : (1+lam/2)*x/L≤θ*l/2 := by
      apply (div_le_iff₀ hL0).mpr
      have hx2 : x≤2*a*l := by nlinarith only [hxa,mul_le_mul_of_nonneg_left hl1 ha0.le]
      have hml := mul_le_mul_of_nonneg_left hx2 (show 0≤1+lam/2 by positivity)
      have hθL' : 4*(1+lam/2)*a≤θ*L := by nlinarith only [hθL,mul_nonneg hlam.le ha0.le]
      have hh := mul_le_mul_of_nonneg_right hθL' hl0
      nlinarith only [hml,hh]
    have hbb : D L*Real.exp (x/L-θ*l)≤Real.exp (-lam*x/(2*L))/2 := by
      calc
        _ ≤ D₂*Real.exp (x/L-θ*l) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
        _ = Real.exp (Real.log D₂+x/L-θ*l) := by simp only [Real.exp_sub,Real.exp_add,Real.exp_log hD₂]; ring
        _ ≤ _ := by
          apply exp_le_half_exp
          have hh : Real.log D₂+Real.log 2≤θ*l/2 := by
            rw [← Real.log_mul (ne_of_gt hD₂) (by norm_num),mul_comm]
            exact hlog₂
          have : Real.log D₂+Real.log 2+(1+lam/2)*x/L≤θ*l := by linarith only [hh,hfrac]
          have hid : -lam*x/(2*L)= -(lam/2)*x/L := by ring
          rw [hid]
          ring_nf at this ⊢
          linarith only [this]
    calc
      T x ≤ (Real.exp (C*k-lam*x/L)+D L*Real.exp (x/L-θ*l))^L := hbound
      _ ≤ (Real.exp (-lam*x/(2*L)))^L := by
        apply pow_le_pow_left₀ (add_nonneg (Real.exp_pos _).le (mul_nonneg (hD L) (Real.exp_pos _).le))
        linarith only [hab,hbb]
      _ = Real.exp (-lam*x/2) := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  constructor
  · intro x hx0 hxa
    by_cases hxc : c*l≤x
    · exact (hlarge x hxc hxa).trans (Real.exp_le_exp.mpr (by linarith only [mul_nonneg hC₀.le hk0]))
    · by_cases hell1 : (k:ℝ)*K≤x
      · have hh := htail 1 (by omega) x (by simpa using hell1) hxa
        simp only [Nat.cast_one,div_one,pow_one] at hh
        have hb : D 1*Real.exp (x-θ*l)≤Real.exp (-lam*x) := by
          calc
            _ ≤ D₁*Real.exp (x-θ*l) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
            _ = Real.exp (Real.log D₁+x-θ*l) := by simp only [Real.exp_sub,Real.exp_add,Real.exp_log hD₁]; ring
            _ ≤ _ := by
              apply Real.exp_le_exp.mpr
              have hh := mul_le_mul_of_nonneg_left (not_le.mp hxc).le (show 0≤1+lam by positivity)
              have hh' := mul_le_mul_of_nonneg_right hcθ hl0
              nlinarith only [hh,hh',hlog₁,mul_nonneg hθ.le hl0]
        have hcpos : 0≤C*k := mul_nonneg hC hk0
        calc
          T x ≤ 2*Real.exp (C*k-lam*x) := by
            have he := Real.exp_le_exp.mpr (show -lam*x≤C*k-lam*x by linarith only [hcpos])
            linarith only [hh,hb,he]
          _ = Real.exp (Real.log 2+C*k-lam*x) := by simp only [Real.exp_sub,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]; ring
          _ ≤ Real.exp (C₀*k-lam*x/2) := by
            apply Real.exp_le_exp.mpr
            have hlog2 : Real.log 2≤1 := by
              convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2) using 1
              norm_num
            dsimp [C₀]
            have hm := mul_nonneg (mul_nonneg hlam.le hK) hk0
            nlinarith only [hlog2,hk1,hm,mul_nonneg hlam.le hx0]
      · apply (hT x).trans
        apply Real.one_le_exp_iff.mpr
        have hxk := not_le.mp hell1
        dsimp [C₀]
        have hm₁ := mul_le_mul_of_nonneg_left hxk.le hlam.le
        have hm₂ := mul_nonneg hC hk0
        have hm₃ := mul_nonneg (mul_nonneg hlam.le hK) hk0
        nlinarith only [hm₁,hm₂,hm₃,hk1]
  · apply hlarge
    · nlinarith only [ha,hl0,mul_le_mul_of_nonneg_right ha hl0,mul_le_mul_of_nonneg_right hc1 hl0]
    · exact le_rfl

end DirectionalTransience

end

end OAI
