import Mathlib
import OAI.Probability.SLE.DyadicStrips
import OAI.Probability.SLE.NestedMeans

namespace OAI

/-! Strip Probabilities for chordal SLE. -/

section
section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge
theorem comparison_path_strip_zero {η : ℝ → ℂ} {T : ℝ}
    (hT : 0 < T) (hη : ContinuousOn η (Icc 0 T)) (hstart : η 0 = 0)
    (hend : ‖η T‖ = 1) (hupper : ∀ t ∈ Icc 0 T, 0 ≤ (η t).im)
    (Fbar : ℂ → OnePoint ℂ) (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H)
    (himage : ∀ t ∈ Icc 0 T, ∃ w : ℂ, Fbar (η t) = (w : OnePoint ℂ) ∧ ‖w-q‖ ≤ r)
    (v : ℝ) (hv : v ≤ 0) :
    ∃ φ : ℝ, φ ∈ Icc 0 Real.pi ∧
      sphericalTruncatedLog q r H (Fbar (Complex.exp ((v : ℂ)+(φ : ℂ)*Complex.I))) = 0 := by
  have her : Real.exp v ∈ Icc ‖η 0‖ ‖η T‖ := by
    rw [hstart,norm_zero,hend]
    exact ⟨(Real.exp_pos v).le,by simpa using Real.exp_le_exp.mpr hv⟩
  obtain ⟨t,ht,htr⟩ := intermediate_value_Icc hT.le hη.norm her
  change ‖η t‖ = Real.exp v at htr
  have hn : η t ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [htr]
    exact (Real.exp_pos v).ne'
  let φ := (η t).arg
  have hφ : φ ∈ Icc 0 Real.pi :=
    ⟨Complex.arg_nonneg_iff.mpr (hupper t ht),Complex.arg_le_pi _⟩
  have he : (v : ℂ)+(φ : ℂ)*Complex.I = Complex.log (η t) := by
    apply Complex.ext
    · simp [Complex.log_re,htr]
    · simp [Complex.log_im,φ]
  refine ⟨φ,hφ,?_⟩
  rw [he,Complex.exp_log hn]
  obtain ⟨w,hw,hwr⟩ := himage t ht
  rw [hw,sphericalTruncatedLog_coe]
  exact truncatedConformalLog_eq_zero hr hH.le hwr

end SLEExactGauge
end

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
lemma source_strip_log_locallyLipschitz {F : ℂ → ℂ} {Fbar : ℂ → OnePoint ℂ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hext : ∀ z : ℂ, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    LocallyLipschitzOn fullOpenStrip (fun z : ℂ => sphericalTruncatedLog q r H (Fbar (Complex.exp z))) := by
  let U := fun z : ℂ => sphericalTruncatedLog q r H (Fbar (Complex.exp z))
  let V := truncatedConformalLog (F ∘ Complex.exp) q r H
  have heq : EqOn U V fullOpenStrip := by
    intro z hz
    dsimp [U]
    rw [hext (Complex.exp z) (exp_strip_halfplane hz),sphericalTruncatedLog_coe]
    rfl
  have hcomp : DifferentiableOn ℂ (F ∘ Complex.exp) fullOpenStrip :=
    hF.comp Complex.differentiable_exp.differentiableOn exp_strip_halfplane
  intro z hz
  obtain ⟨K,S,hS,hzS,hK⟩ := truncated_log_lipschitz_near fullOpenStrip_isOpen hcomp hz q hr hH
  refine ⟨K,S ∩ fullOpenStrip,mem_nhdsWithin_of_mem_nhds ((hS.inter fullOpenStrip_isOpen).mem_nhds ⟨hzS,hz⟩),?_⟩
  intro x hx y hy
  change edist (U x) (U y) ≤ (K : ℝ≥0∞)*edist x y
  rw [heq hx.2,heq hy.2]
  exact hK hx.1 hy.1

 

def BeforeFirstModulus (γ : ℝ≥0 → ℂ) (A : ℝ) (t : ℝ≥0) : Prop :=
  ∀ s : ℝ≥0, s < t → ‖γ s‖ < A

universe u
 
def SourceUniformConformalLocalizationTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 → ∃ b C c L0 : ℝ,
    0 < b ∧ 0 < C ∧ 0 < c ∧ 1 < L0 ∧
    ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ γ : Ω → ℝ≥0 → ℂ, IsOrdinaryChordalSLE κ γ P →
    ∀ (F : ℂ → ℂ) (Fbar : ℂ → OnePoint ℂ),
    DifferentiableOn ℂ F {z | 0 < z.im} → InjOn F {z | 0 < z.im} →
    ContinuousOn Fbar {z : ℂ | 0 ≤ z.im} →
    (∀ z : ℂ, 0 < z.im → Fbar z = (F z : OnePoint ℂ)) →
    ∀ (q : ℂ) (r : ℝ), 0 < r →
    ∀ (η : ℝ → ℂ) (T : ℝ), 0 < T → ContinuousOn η (Icc 0 T) →
    η 0 = 0 → ‖η T‖ = 1 → (∀ t ∈ Icc 0 T, 0 ≤ (η t).im) →
    (∀ t ∈ Icc 0 T, ∃ w : ℂ, Fbar (η t) = (w : OnePoint ℂ) ∧ ‖w-q‖ ≤ r) →
    ∀ L : ℝ, L0 ≤ L →
      P {xi | ∃ t : ℝ≥0, BeforeFirstModulus (γ xi) (L^b) t ∧
        Fbar (γ xi t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)} ≤
        ENNReal.ofReal (C*L^(-c))

lemma beforeFirstModulus_norm_le {γ : ℝ≥0 → ℂ} (hc : Continuous γ) (h0 : γ 0 = 0)
    {A : ℝ} (hA : 0 < A) {t : ℝ≥0} (ht : BeforeFirstModulus γ A t) :
    ‖γ t‖ ≤ A := by
  by_cases ht0 : t = 0
  · simp [ht0,h0,hA.le]
  have htpos : 0 < t := bot_lt_iff_ne_bot.mpr ht0
  have hcl : t ∈ closure (Iio t : Set ℝ≥0) := by
    rw [closure_Iio' (show (Iio t : Set ℝ≥0).Nonempty from ⟨0,htpos⟩)]
    exact (show t ≤ t from le_rfl)
  have hclosed : IsClosed {s : ℝ≥0 | ‖γ s‖ ≤ A} := isClosed_le hc.norm continuous_const
  exact (closure_minimal (fun s hs => (ht s hs).le) hclosed) hcl

lemma sphericalTruncatedLog_eq_height_of_notin_ball (q : ℂ) (r H : ℝ) (hr : 0 < r)
    (x : OnePoint ℂ)
    (hx : x ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (Real.exp H*r)) :
    sphericalTruncatedLog q r H x = H := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe z =>
    rw [sphericalTruncatedLog_coe]
    apply truncatedConformalLog_eq_height hr
    apply le_of_not_gt
    intro h
    apply hx
    exact ⟨z,by simpa [Metric.mem_ball,dist_eq_norm] using h,rfl⟩

lemma escape_forces_strip_level {γ : ℝ≥0 → ℂ} (hc : Continuous γ) (h0 : γ 0 = 0)
    (hupper : ∀ t, 0 ≤ (γ t).im)
    (Fbar : ℂ → OnePoint ℂ) (q : ℂ) {r L H b : ℝ} (hr : 0 < r) (hL : 1 < L)
    (hH : H = Real.log L)
    (hstart : ∃ w : ℂ, Fbar 0 = (w : OnePoint ℂ) ∧ ‖w-q‖ ≤ r)
    (t : ℝ≥0) (ht : BeforeFirstModulus γ (L^b) t)
    (hbad : Fbar (γ t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)) :
    ∃ z : ℂ, Complex.exp z ∈ range γ ∧ 0 ≤ z.im ∧ z.im ≤ Real.pi ∧ z.re ≤ b*H ∧
      sphericalTruncatedLog q r H (Fbar (Complex.exp z)) = H := by
  have hLp : 0 < L := by linarith
  have hnorm := beforeFirstModulus_norm_le hc h0 (Real.rpow_pos_of_pos hLp b) ht
  have hn : γ t ≠ 0 := by
    intro heq
    rw [heq] at hbad
    obtain ⟨w,hw,hwr⟩ := hstart
    apply hbad
    exact ⟨w,by rw [Metric.mem_ball,dist_eq_norm]; nlinarith,hw.symm⟩
  refine ⟨Complex.log (γ t),by rw [Complex.exp_log hn]; exact mem_range_self t,?_,?_,?_,?_⟩
  · simpa only [Complex.log_im] using Complex.arg_nonneg_iff.mpr (hupper t)
  · simpa only [Complex.log_im] using Complex.arg_le_pi (γ t)
  · rw [Complex.log_re,hH]
    exact (Real.log_le_log (norm_pos_iff.mpr hn) hnorm).trans_eq (Real.log_rpow hLp b)
  · rw [Complex.exp_log hn]
    apply sphericalTruncatedLog_eq_height_of_notin_ball q r H hr
    simpa only [hH,Real.exp_log hLp] using hbad

theorem sourceUniformConformalLocalization : SourceUniformConformalLocalizationTarget := by
  intro κ hκ hκ8
  obtain ⟨C0,α,hC0,hα,hhit⟩ := ordinary_sle_strip_hitting_constants κ hκ hκ8
  obtain ⟨b,C,c,H0,hb,hC,hc,hH0,hstrip⟩ := sourceStripLocalization C0 α hC0 hα
  refine ⟨b,C,c,Real.exp (max H0 1),hb,hC,hc,?_,?_⟩
  · exact Real.one_lt_exp_iff.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  intro Ω mΩ P hP γ hγ F Fbar hF hi hbar hext q r hr η T hT hη hs he hu him L hL
  let := hP
  have hL1 : 1 < L := (Real.one_lt_exp_iff.mpr
    (lt_of_lt_of_le zero_lt_one (le_max_right H0 1))).trans_le hL
  have hLp : 0 < L := by linarith
  have hlog : max H0 1 ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hL
  have hHH : H0 ≤ Real.log L := (le_max_left _ _).trans hlog
  have hHp : 0 < Real.log L := hH0.trans_le hHH
  let U := fun z : ℂ => sphericalTruncatedLog q r (Real.log L) (Fbar (Complex.exp z))
  let X := fun xi : Ω => Complex.exp ⁻¹' range (γ xi)
  obtain ⟨hcU,hbU,-,hgU,hEU⟩ := source_strip_log_regularity hF hi hbar hext q r (Real.log L) hr hHp
  have hzero (v : ℝ) (hv : v ≤ 0) : ∃ y ∈ Icc (0:ℝ) Real.pi, U (v+y*Complex.I) = 0 :=
    comparison_path_strip_zero hT hη hs he hu Fbar q r (Real.log L) hr hHp him v hv
  have hhits (j : ℤ) (k : ℕ) (i m : Fin (2^k)) :
      P {xi | (X xi ∩ dyadicStripRectangle j k i m).Nonempty} ≤
        ENNReal.ofReal (C0*(2:ℝ)^(-α*(k:ℝ))) := by
    apply (measure_mono ?_).trans (hhit γ hγ j k i m)
    rintro xi ⟨z,⟨t,ht⟩,hz⟩
    exact ⟨t,z,hz,ht.symm⟩
  have hh := hstrip (Real.log L) hHH U hcU
    (source_strip_log_locallyLipschitz hF hext q r (Real.log L) hr hHp)
    hbU hgU hEU hzero Ω mΩ P hP X hhits
  have hstart : ∃ w : ℂ, Fbar 0 = (w : OnePoint ℂ) ∧ ‖w-q‖ ≤ r := by
    simpa only [hs] using him 0 ⟨le_rfl,hT.le⟩
  obtain ⟨B,hB,htrace⟩ := hγ.2
  have hsub : {xi | ∃ t : ℝ≥0, BeforeFirstModulus (γ xi) (L^b) t ∧
        Fbar (γ xi t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)} ≤ᵐ[P]
      {xi | ∃ z ∈ X xi, 0 ≤ z.im ∧ z.im ≤ Real.pi ∧ z.re ≤ b*Real.log L ∧ U z = Real.log L} := by
    filter_upwards [htrace] with xi hxi
    obtain ⟨G,Fw,hFw⟩ := hxi
    rintro ⟨t,ht,hbad⟩
    exact escape_forces_strip_level hFw.1 hFw.2.1 hFw.2.2.1 Fbar q hr hL1 rfl hstart t ht hbad
  calc
    _ ≤ P {xi | ∃ z ∈ X xi, 0 ≤ z.im ∧ z.im ≤ Real.pi ∧ z.re ≤ b*Real.log L ∧ U z = Real.log L} :=
      measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (C*Real.exp (-c*Real.log L)) := hh
    _ = ENNReal.ofReal (C*L^(-c)) := by
      rw [Real.rpow_def_of_pos hLp]
      congr 2
      congr 1
      ring

end SLEExactGauge

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem ordinary_survival_bound_regular
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 4 < κ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (R : ℝ) (hR : 0 < R)
    (hN : greenLogNormSq κ (initialLogCoordinates z) 0 ≤ R^2)
    (T : ℝ≥0) (b : ℝ) (hb : 0 < b)
    (hbR : b ≤ Real.exp (((κ-4)/(2*κ))*Real.log R))
    (hbT : b ≤ (((κ-4)/(2*κ))*((κ-4)/4)*Real.exp ((((κ-4)/(2*κ))-2)*Real.log R)) * T) :
    P {ω | z ∈ survivingDomain (γ ω) T} ≤
      ENNReal.ofReal (swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8)
        (initialLogCoordinates z) 0 / b) := by
  let hm (t) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let q₀ := initialLogCoordinates z
  let lo (n : ℕ) : ℝ := q₀.1.im-(n:ℝ)-1
  have hlo (n : ℕ) : lo n ≤ q₀.1.im := by dsimp [lo]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  let c (n : ℕ) := Classical.choice
    (exists_clippedLogSolution B hm hBm hBc κ (lo n) q₀.1.im (hlo n) q₀)
  let a (n : ℕ) : RadialLocalization (c n) R T := Classical.choice
    (exists_radialLocalization hBc hB0 (c n) R T hN (hlo n))
  let E (n : ℕ) : Set Ω := {ω | (a n).τ ω = T ∨
    greenLogNormSq κ ((c n).Q ((a n).τ ω) ω) (B ((a n).τ ω) ω) = R^2}
  have hprob (n : ℕ) : P (E n) ≤
      ENNReal.ofReal (swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8) q₀ 0 / b) :=
    (a n).exit_probability hB hBm hBc hκ hR le_rfl b hb hbR hbT
  have hsub : {ω | z ∈ survivingDomain (γ ω) T} ≤ᵐ[P]
      {ω | ∀ᶠ n : ℕ in atTop, ω ∈ E n} := by
    filter_upwards [hw] with ω hω
    intro hlive
    obtain ⟨N, hN⟩ := exists_nat_gt (q₀.1.im-Real.log (G ω T z).im)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hlt : lo n < Real.log (G ω T z).im := by
      have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
      dsimp [lo]
      linarith
    exact (a n).alive_forces_radial_or_time_boundary hBc hz rfl le_rfl ω
      (γ ω) (G ω) (F ω) hω hlive hlt
  exact (measure_mono_ae hsub).trans (measure_eventually_sets_le P E _ hprob)

theorem ordinary_survival_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 4 < κ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (R : ℝ) (hR : 0 < R)
    (hN : greenLogNormSq κ (initialLogCoordinates z) 0 ≤ R^2)
    (T : ℝ≥0) (b : ℝ) (hb : 0 < b)
    (hbR : b ≤ Real.exp (((κ-4)/(2*κ))*Real.log R))
    (hbT : b ≤ (((κ-4)/(2*κ))*((κ-4)/4)*Real.exp ((((κ-4)/(2*κ))-2)*Real.log R)) * T) :
    P {ω | z ∈ survivingDomain (γ ω) T} ≤
      ENNReal.ofReal (swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8)
        (initialLogCoordinates z) 0 / b) := by
  obtain ⟨C, hCm, hCc, hC0, hC, hCB⟩ := exists_regular_brownian_version hB
  have hwC : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * C t ω) (γ ω) (G ω) (F ω) := by
    filter_upwards [hw,hCB] with ω hω he
    simpa only [he] using hω
  exact ordinary_survival_bound_regular hC hCm hCc hC0 κ hκ γ G F hwC
    z hz R hR hN T b hb hbR hbT

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma greenLogNormSq_initial_norm (κ : ℝ) (z : ℂ) (hz : 0 < z.im) :
    greenLogNormSq κ (initialLogCoordinates z) 0 = ‖z‖^2 := by
  have he : Real.exp (2 * Real.log z.im) = z.im ^ 2 := by
    rw [show 2 * Real.log z.im = Real.log z.im + Real.log z.im by ring,
      Real.exp_add, Real.exp_log hz, pow_two]
  rw [← Complex.normSq_eq_norm_sq]
  simp only [greenLogNormSq, initialLogCoordinates, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_self, add_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, he,
      Complex.normSq_apply, pow_two]

theorem ordinary_survival_radial_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 4 < κ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (hunit : ‖z‖ = 1)
    (R : ℝ) (hR : 1 ≤ R) :
    P {ω | z ∈ survivingDomain (γ ω) ((R^2).toNNReal)} ≤
      ENNReal.ofReal ((1+3*(κ-4)/8) / min 1 (((κ-4)/(2*κ))*((κ-4)/4)) *
        Real.exp (-((κ-4)/(2*κ))*Real.log R)) := by
  let β := (κ-4)/(2*κ)
  let C := 3*(κ-4)/8
  let d := β*((κ-4)/4)
  let m := min 1 d
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  have hβ : 0 < β := by dsimp [β]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hm : 0 < m := lt_min (by norm_num) hd
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hN : greenLogNormSq κ (initialLogCoordinates z) 0 ≤ R^2 := by
    rw [greenLogNormSq_initial_norm κ z hz, hunit]
    nlinarith
  have hN1 : greenLogNormSq κ (initialLogCoordinates z) 0 ≤ (1:ℝ)^2 := by
    rw [greenLogNormSq_initial_norm κ z hz, hunit]
  have hF : swallowLyapunov κ β C (initialLogCoordinates z) 0 ≤ 1+C := by
    have hr := radialLogPower_le κ β hβ.le (initialLogCoordinates z) 0 1 (by norm_num) hN1
    have hy := heightLogPower_le κ β hβ.le (initialLogCoordinates z) 0 1 (by norm_num) hN1
    simp only [Real.log_one, mul_zero, Real.exp_zero] at hr hy
    exact (add_le_add hr (mul_le_mul_of_nonneg_left hy hC)).trans_eq (by ring)
  have he : Real.exp ((β-2)*Real.log R)*R^2 = Real.exp (β*Real.log R) := by
    have hh : R^2 = Real.exp (2*Real.log R) := by
      rw [show 2*Real.log R = Real.log R+Real.log R by ring, Real.exp_add,Real.exp_log hR0,pow_two]
    rw [hh,← Real.exp_add]
    congr 1
    ring
  have hbR : m*Real.exp (β*Real.log R) ≤ Real.exp (β*Real.log R) := by
    exact mul_le_of_le_one_left (Real.exp_pos _).le (min_le_left _ _)
  have hbT : m*Real.exp (β*Real.log R) ≤ d*Real.exp ((β-2)*Real.log R)*((R^2).toNNReal:ℝ) := by
    rw [Real.coe_toNNReal _ (sq_nonneg R),mul_assoc,he]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le
  have hb : 0 < m*Real.exp (β*Real.log R) := mul_pos hm (Real.exp_pos _)
  have hp := ordinary_survival_bound hB κ hκ γ G F hw z hz R hR0 hN
    ((R^2).toNNReal) (m*Real.exp (β*Real.log R)) hb hbR hbT
  apply hp.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    swallowLyapunov κ β C (initialLogCoordinates z) 0/(m*Real.exp (β*Real.log R))
        ≤ (1+C)/(m*Real.exp (β*Real.log R)) := div_le_div_of_nonneg_right hF hb.le
    _ = (1+C)/m*Real.exp (-β*Real.log R) := by
      rw [show -β*Real.log R = -(β*Real.log R) by ring, Real.exp_neg]
      ring

 

theorem ordinary_survival_polynomial
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 4 < κ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ z ∈ upperHalfPlane, ‖z‖ = 1 →
      ∀ T : ℝ≥0, 1 ≤ T →
      P {ω | z ∈ survivingDomain (γ ω) T} ≤ ENNReal.ofReal (C*(T:ℝ)^(-c)) := by
  let β := (κ-4)/(2*κ)
  let C := (1+3*(κ-4)/8) / min 1 (β*((κ-4)/4))
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  have hβ : 0 < β := by dsimp [β]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,β/2,hC,by positivity,?_⟩
  intro z hz hu T hT
  have ht : 0 < (T:ℝ) := lt_of_lt_of_le (by norm_num) (NNReal.coe_le_coe.mpr hT)
  have hR : 1 ≤ Real.sqrt (T:ℝ) := (Real.le_sqrt (by norm_num) T.coe_nonneg).mpr (by simpa only [one_pow, NNReal.coe_one] using NNReal.coe_le_coe.mpr hT)
  have hp := ordinary_survival_radial_tail hB κ hκ γ G F hw z hz hu (Real.sqrt T) hR
  rw [Real.sq_sqrt T.coe_nonneg,Real.toNNReal_coe] at hp
  convert hp using 2
  rw [Real.rpow_def_of_pos ht,Real.log_sqrt ht.le]
  congr 2
  ring

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma linear_subsolution_initial_nonpos (T : ℝ) (hT : 0 ≤ T)
    (f a g : ℝ → ℝ) (ha : ContinuousOn a (Icc 0 T))
    (hf : ∀ u ∈ Icc 0 T, HasDerivWithinAt f (g u) (Icc 0 T) u)
    (hg : ∀ u ∈ Icc 0 T, a u*f u ≤ g u) (hfT : f T ≤ 0) : f 0 ≤ 0 := by
  let A (u : ℝ) := a (projIcc 0 T hT u)
  have hA : Continuous A := ha.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun u => (projIcc 0 T hT u).property)
  have hAa (u : ℝ) (hu : u ∈ Icc 0 T) : A u = a u := by simp only [A,projIcc_of_mem hT hu]
  let I (u : ℝ) := ∫ v in (0:ℝ)..u, A v
  have hI (u : ℝ) : HasDerivAt I (A u) u :=
    intervalIntegral.integral_hasDerivAt_right (hA.intervalIntegrable _ _)
      hA.aestronglyMeasurable.stronglyMeasurableAtFilter hA.continuousAt
  have hd (u : ℝ) (hu : u ∈ Icc 0 T) :
      HasDerivWithinAt (fun v => f v*Real.exp (-I v))
        ((g u-a u*f u)*Real.exp (-I u)) (Icc 0 T) u := by
    convert (hf u hu).mul ((hI u).neg.exp.hasDerivWithinAt) using 1; try rfl
    simp only [Pi.neg_apply]
    rw [hAa u hu]
    ring
  have hmono : MonotoneOn (fun v => f v*Real.exp (-I v)) (Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun u hu => (hd u hu).continuousWithinAt)
      (fun u hu => (hd u (interior_subset hu)).mono interior_subset)
      (fun u hu => mul_nonneg (sub_nonneg.mpr (hg u (interior_subset hu))) (Real.exp_pos _).le)
  have hh := hmono (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) ⟨hT,le_rfl⟩ hT
  simp only [I,intervalIntegral.integral_same,neg_zero,Real.exp_zero,mul_one] at hh
  exact hh.trans (mul_nonpos_of_nonpos_of_nonneg hfT (Real.exp_pos _).le)

lemma IsCapacityTwoWitness.real_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :
    HasDerivWithinAt (fun v : ℝ => (G v.toNNReal z).re)
      (2*((G u.toNNReal z).re-U u.toNNReal)/Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)))
      (Icc 0 (T:ℝ)) u := by
  have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt u (h.time_derivative T z hz u hu)
  simpa [Function.comp_def,Complex.div_re] using hh

lemma IsCapacityTwoWitness.initial_real_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (M : ℝ)
    (hbound : ∀ u : ℝ≥0, u ≤ T → U u ≤ M) (hend : (G T z).re ≤ M) : z.re ≤ M := by
  let a (u : ℝ) := 2/Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ))
  have hnorm : ContinuousOn (fun u : ℝ => Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ))) (Icc 0 (T:ℝ)) :=
    Complex.continuous_normSq.comp_continuousOn ((h.time_continuousOn T z hz).sub
      (Complex.continuous_ofReal.comp (hU.comp continuous_real_toNNReal)).continuousOn)
  have hne (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :
      Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (h.centered_ne_zero u.toNNReal z
      (survivingDomain_antitone γ (Real.toNNReal_le_iff_le_coe.mpr hu.2) hz))).ne'
  have ha : ContinuousOn a (Icc 0 (T:ℝ)) := continuousOn_const.div hnorm hne
  have hh := linear_subsolution_initial_nonpos T T.coe_nonneg
    (fun u => (G u.toNNReal z).re-M) a
    (fun u => 2*((G u.toNNReal z).re-U u.toNNReal)/Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ))) ha
    (fun u hu => (h.real_derivative T z hz u hu).sub_const M)
    (fun u hu => by
      dsimp only [a]
      have hb := hbound u.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hu.2)
      have hp : 0 ≤ Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)) := Complex.normSq_nonneg _
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by linarith) hp)
    (by simpa only [Real.toNNReal_coe] using sub_nonpos.mpr hend)
  simpa only [Real.toNNReal_zero,h.initial_value z hz.1.1,sub_nonpos] using hh

lemma IsCapacityTwoWitness.initial_real_ge
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (M : ℝ)
    (hbound : ∀ u : ℝ≥0, u ≤ T → M ≤ U u) (hend : M ≤ (G T z).re) : M ≤ z.re := by
  let a (u : ℝ) := 2/Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ))
  have hnorm : ContinuousOn (fun u : ℝ => Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ))) (Icc 0 (T:ℝ)) :=
    Complex.continuous_normSq.comp_continuousOn ((h.time_continuousOn T z hz).sub
      (Complex.continuous_ofReal.comp (hU.comp continuous_real_toNNReal)).continuousOn)
  have hne (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :
      Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (h.centered_ne_zero u.toNNReal z
      (survivingDomain_antitone γ (Real.toNNReal_le_iff_le_coe.mpr hu.2) hz))).ne'
  have ha : ContinuousOn a (Icc 0 (T:ℝ)) := continuousOn_const.div hnorm hne
  have hh := linear_subsolution_initial_nonpos T T.coe_nonneg
    (fun u => M-(G u.toNNReal z).re) a
    (fun u => -(2*((G u.toNNReal z).re-U u.toNNReal)/Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)))) ha
    (fun u hu => (h.real_derivative T z hz u hu).const_sub M)
    (fun u hu => by
      dsimp only [a]
      have hb := hbound u.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hu.2)
      have hp : 0 ≤ Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)) := Complex.normSq_nonneg _
      rw [div_mul_eq_mul_div,← neg_div]
      exact div_le_div_of_nonneg_right (by linarith) hp)
    (by simpa only [Real.toNNReal_coe] using sub_nonpos.mpr hend)
  simpa only [Real.toNNReal_zero,h.initial_value z hz.1.1,sub_nonpos] using hh

lemma IsCapacityTwoWitness.initial_imag_square_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) : z.im^2 ≤ (G T z).im^2+4*T := by
  have hd (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :=
    ((h.imag_derivative T z hz u hu).pow 2).add ((hasDerivWithinAt_id u (Icc 0 (T:ℝ))).const_mul 4)
  have hnonneg (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :
      0 ≤ (2:ℝ)*(G u.toNNReal z).im^(2-1)*
        (-2*(G u.toNNReal z).im/Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)))+1*4 := by
    have hp := Complex.normSq_pos.mpr (h.centered_ne_zero u.toNNReal z
      (survivingDomain_antitone γ (Real.toNNReal_le_iff_le_coe.mpr hu.2) hz))
    have hn : (G u.toNNReal z).im^2 ≤ Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)) := by
      simp only [Complex.normSq_apply,Complex.sub_re,Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,sub_zero]
      nlinarith [sq_nonneg ((G u.toNNReal z).re-U u.toNNReal)]
    norm_num only [Nat.reduceSub, pow_one, one_mul]
    field_simp
    nlinarith
  have hmono : MonotoneOn (fun u : ℝ => (G u.toNNReal z).im^2+4*u) (Icc 0 (T:ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun u hu => (hd u hu).continuousWithinAt)
      (fun u hu => (hd u (interior_subset hu)).mono interior_subset)
      (fun u hu => by simpa only [Nat.cast_ofNat, mul_one, one_mul] using hnonneg u (interior_subset hu))
  have hh := hmono (show (0:ℝ) ∈ Icc 0 (T:ℝ) from ⟨le_rfl,T.coe_nonneg⟩)
    ⟨T.coe_nonneg,le_rfl⟩ T.coe_nonneg
  simpa only [Real.toNNReal_zero,Real.toNNReal_coe,h.initial_value z hz.1.1,mul_zero,add_zero] using hh

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsCapacityTwoWitness.trace_real_bounds
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (M : ℝ)
    (hbound : ∀ u : ℝ≥0, u ≤ T → |U u| ≤ M) : |(γ T).re| ≤ M := by
  have hh := h
  obtain ⟨_,_,_,_,_,_,hFmap,_,hinv,_,_,_,htip⟩ := hh
  have hm (y : ℝ) (hy : 0 < y) :
      |(F T ((U T:ℂ)+(y:ℂ)*Complex.I)).re| ≤ M := by
    have hyH : (U T:ℂ)+(y:ℂ)*Complex.I ∈ upperHalfPlane := by
      simpa only [upperHalfPlane, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
        mul_zero, add_zero, zero_add] using hy
    have hz := hFmap T hyH
    have he := hinv T _ hyH
    apply abs_le.mpr
    constructor
    · apply IsCapacityTwoWitness.initial_real_ge hU h T _ hz (-M)
      · intro u hu; exact (abs_le.mp (hbound u hu)).1
      · rw [he]; simpa using (abs_le.mp (hbound T le_rfl)).1
    · apply IsCapacityTwoWitness.initial_real_le hU h T _ hz M
      · intro u hu; exact (abs_le.mp (hbound u hu)).2
      · rw [he]; simpa using (abs_le.mp (hbound T le_rfl)).2
  have ht := (continuous_abs.tendsto _).comp (Complex.continuous_re.tendsto _ |>.comp (htip T))
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun y hy => hm y hy)

lemma IsCapacityTwoWitness.trace_imag_square_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) : (γ T).im^2 ≤ 4*T := by
  have hh := h
  obtain ⟨_,_,_,_,_,_,hFmap,_,hinv,_,_,_,htip⟩ := hh
  have hm (y : ℝ) (hy : 0 < y) :
      (F T ((U T:ℂ)+(y:ℂ)*Complex.I)).im^2 ≤ y^2+4*T := by
    have hyH : (U T:ℂ)+(y:ℂ)*Complex.I ∈ upperHalfPlane := by
      simpa only [upperHalfPlane, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
        mul_zero, add_zero, zero_add] using hy
    have hz := hFmap T hyH
    have he := hinv T _ hyH
    have hh := h.initial_imag_square_le T _ hz
    rw [he] at hh
    simpa using hh
  have ht := (Complex.continuous_im.tendsto _ |>.comp (htip T)).pow 2
  have hr : Tendsto (fun y : ℝ => y^2+4*(T:ℝ)) (𝓝[>] 0) (𝓝 (4*(T:ℝ))) := by
    simpa using (((tendsto_id : Tendsto (fun y : ℝ => y) (𝓝 (0:ℝ)) (𝓝 0)).pow 2).add_const (4*(T:ℝ))).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto ht hr (eventually_nhdsWithin_of_forall fun y hy => hm y hy)

lemma IsCapacityTwoWitness.trace_norm_square_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ u : ℝ≥0, u ≤ T → |U u| ≤ M) : ‖γ T‖^2 ≤ M^2+4*T := by
  have hr := h.trace_real_bounds hU T M hbound
  have hi := h.trace_imag_square_le T
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hs : (γ T).re^2 ≤ M^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr hr
  nlinarith

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma exists_compact_square_field (R : ℝ) (hR : 0 ≤ R) :
    ∃ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ x, |x| ≤ R → φ (0,x) = x^2) ∧
      (∀ x, |x| ≤ R → iteratedDeriv 2 (fun y => φ (0,y)) x = 2) := by
  let b : ContDiffBump (0 : ℝ × ℝ) := ⟨R+1,R+2,by linarith,by linarith⟩
  let φ (p : ℝ × ℝ) := b p*p.2^2
  have hnear (x : ℝ) (hx : |x| ≤ R) : (fun y => φ (0,y)) =ᶠ[𝓝 x] (fun y => y^2) := by
    have hball : (0,x) ∈ Metric.ball (0:ℝ × ℝ) b.rIn := by
      simpa only [Metric.mem_ball,dist_zero_right,Prod.norm_def,norm_zero,Real.norm_eq_abs,
        max_eq_right (abs_nonneg x)] using (show |x| < R+1 by linarith)
    have he := (b.eventuallyEq_one_of_mem_ball hball).comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto x)
    filter_upwards [he] with y hy
    change b (0,y) = 1 at hy
    simp only [φ,hy,one_mul]
  refine ⟨φ,b.contDiff.mul (contDiff_snd.pow 2),b.hasCompactSupport.mul_right,
    fun x hx => (hnear x hx).eq_of_nhds,?_⟩
  intro x hx
  rw [(hnear x hx).iteratedDeriv_eq 2,iteratedDeriv_pow]
  norm_num

lemma brownian_stopped_square
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (R : ℝ) (hR : 0 ≤ R) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hin : ∀ ω t, t ≤ τ ω → |B t ω| ≤ R) :
    Integrable (fun ω => (B (τ ω) ω)^2) P ∧
      (∫ ω, (B (τ ω) ω)^2 ∂P) = ∫ ω, (τ ω:ℝ) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨φ,hφ,hφc,he,h2⟩ := exists_compact_square_field R hR
  obtain ⟨K,hfield⟩ := compact_state_smooth_brownian_field B hm
    (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ)) 0 measurable_const (fun _ => measurable_const)
    (fun _ => LipschitzWith.const 0) measurable_const (by simp)
    (fun t ω ht => (hasDerivWithinAt_const t (Ici 0) (0:ℝ))) φ hφ hφc
  let F (t : ℝ≥0) (ω : Ω) (x : ℝ) := φ (0,x)
  let a (t : ℝ≥0) (ω : Ω) (x : ℝ) := fderiv ℝ φ (0,x) ((0:ℝ),0)
  have hg (ω : Ω) (u : ℝ) (hu : u ∈ Icc 0 (τ ω:ℝ)) : brownianFieldDrift B F a u ω = 1 := by
    have hi := hin ω u.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hu.2)
    simp only [brownianFieldDrift,F,a,show ((0:ℝ),0) = (0:ℝ × ℝ) from rfl,map_zero,h2 _ hi]
    norm_num
  have hopt := brownian_time_field_stopped_dynkin hB hm hBm hBc K F a hfield τ hτ T hb
  have hτm := stopping_time_measurable_nnreal hτ
  have hBi : Integrable (fun ω => (B (τ ω) ω)^2) P := by
    apply Integrable.of_bound ((hBm.comp (hτm.prodMk measurable_id)).pow_const 2).aestronglyMeasurable (R^2)
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hh : (B (τ ω) ω)^2 ≤ R^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (hin ω (τ ω) le_rfl)
      simpa only [Function.comp_def, id_eq] using hh
  refine ⟨hBi,?_⟩
  have hef : (fun ω => F (τ ω) ω (B (τ ω) ω)) = fun ω => (B (τ ω) ω)^2 :=
    funext fun ω => he _ (hin ω (τ ω) le_rfl)
  rw [hef] at hopt
  have h0 : (∫ ω, F 0 ω (B 0 ω) ∂P) = 0 := by
    have he0 : (fun ω => F 0 ω (B 0 ω)) =ᵐ[P] (fun _ => (0:ℝ)) := by
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
      change φ (0,B 0 ω) = 0
      rw [hω,he 0 (by simpa using hR)]
      norm_num
    rw [integral_congr_ae he0,integral_zero]
  rw [h0,zero_add] at hopt
  rw [hopt]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    calc
      (∫ u in (0:ℝ)..(τ ω:ℝ), brownianFieldDrift B F a u ω) = ∫ _ in (0:ℝ)..(τ ω:ℝ), (1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact hg ω u (by simpa only [uIcc_of_le (τ ω).coe_nonneg] using hu)
      _ = (τ ω:ℝ) := by simp

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

end SLEExactGauge
end
end

end OAI
