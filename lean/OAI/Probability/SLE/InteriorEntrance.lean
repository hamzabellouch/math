import Mathlib
import OAI.Probability.SLE.StripProbabilities

namespace OAI

/-! Interior Entrance for chordal SLE. -/

section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
lemma brownian_maximal_tail_regular
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (r : ℝ) (hr : 0 < r) (T : ℝ≥0) :
    P {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|} ≤ ENNReal.ofReal ((T:ℝ)/r^2) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hDa : Adapted f (fun t ω => r-|B t ω|) := by
    intro t
    have ha := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted t
    let : MeasurableSpace Ω := f t
    exact measurable_const.sub ha.abs
  obtain ⟨τ,hτ,hb,hin,hpre,hat⟩ := first_margin_stopping f (fun t ω => r-|B t ω|)
    hDa (fun ω => continuous_const.sub (hBc ω).abs)
    (fun ω => by rw [hB0 ω, abs_zero,sub_zero]; exact hr.le) T
  have hsq := brownian_stopped_square hB hm hBm hBc r hr.le τ hτ T hb
    (fun ω t ht => sub_nonneg.mp (hin ω t ht))
  have hτi := bounded_nnreal_integrable (P := P) τ (stopping_time_measurable_nnreal hτ) T hb
  have hmean : (∫ ω, (B (τ ω) ω)^2 ∂P) ≤ (T:ℝ) := by
    rw [hsq.2]
    calc
      (∫ ω, (τ ω:ℝ) ∂P) ≤ ∫ _ : Ω, (T:ℝ) ∂P :=
        integral_mono hτi (integrable_const _) (fun ω => NNReal.coe_le_coe.mpr (hb ω))
      _ = (T:ℝ) := by simp
  apply (measure_mono (show {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|}
      ⊆ {ω | r^2 ≤ (B (τ ω) ω)^2} from ?_)).trans
    (nonnegative_integral_tail _ hsq.1 (fun _ => sq_nonneg _) _ (r^2) (sq_pos_of_pos hr) hmean)
  rintro ω ⟨t,ht,he⟩
  have hlt : τ ω < T := by
    by_contra hh
    have htτ : t ≤ τ ω := ht.trans (not_lt.mp hh)
    exact (not_lt_of_ge (sub_nonneg.mp (hin ω t htτ))) he
  have heq : |B (τ ω) ω| = r := by linarith [hat ω hlt]
  change r^2 ≤ (B (τ ω) ω)^2
  rw [← sq_abs (B (τ ω) ω),heq]

 
theorem brownian_maximal_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (r : ℝ) (hr : 0 < r) (T : ℝ≥0) :
    P {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|} ≤ ENNReal.ofReal ((T:ℝ)/r^2) := by
  obtain ⟨C,hCm,hCc,hC0,hC,hCB⟩ := exists_regular_brownian_version hB
  have he : {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|} =ᵐ[P]
      {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |C t ω|} := by
    filter_upwards [hCB] with ω hω
    simp only [hω]
  rw [measure_congr he]
  exact brownian_maximal_tail_regular hC hCm hCc hC0 r hr T

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

theorem ordinary_trace_excursion_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (A : ℝ) (hA : 16 ≤ A) :
    P {ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖} ≤ ENNReal.ofReal (4*κ/A) := by
  obtain ⟨C,hCm,hCc,hC0,hC,hCB⟩ := exists_regular_brownian_version hB
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  let r := A/(2*Real.sqrt κ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hp := brownian_maximal_tail hC r hr A.toNNReal
  have hsub : {ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖} ≤ᵐ[P]
      {ω | ∃ t : ℝ≥0, t ≤ A.toNNReal ∧ r < |C t ω|} := by
    filter_upwards [hw,hCB] with ω hω he
    have hwC : IsCapacityTwoWitness (fun t => Real.sqrt κ*C t ω) (γ ω) (G ω) (F ω) := by
      simpa only [he] using hω
    rintro ⟨t,ht,hn⟩
    by_contra hh
    have hb : ∀ u, u ≤ t → |Real.sqrt κ*C u ω| ≤ A/2 := by
      intro u hu
      have hl : |C u ω| ≤ r := le_of_not_gt (fun hh' => hh ⟨u,
        (by apply NNReal.coe_le_coe.mp; rw [Real.coe_toNNReal _ hA0.le]; exact (NNReal.coe_le_coe.mpr hu).trans ht),hh'⟩)
      rw [abs_mul,abs_of_pos hs]
      calc
        Real.sqrt κ*|C u ω| ≤ Real.sqrt κ*r := mul_le_mul_of_nonneg_left hl hs.le
        _ = A/2 := by dsimp [r]; field_simp
    have hg := hwC.trace_norm_square_le (continuous_const.mul (hCc ω)) t (A/2) (by positivity) hb
    have hns : A^2 ≤ ‖γ ω t‖^2 := (sq_le_sq₀ hA0.le (norm_nonneg _)).mpr hn
    nlinarith [sq_nonneg (A-16)]
  apply (measure_mono_ae hsub).trans
  apply hp.trans
  apply ENNReal.ofReal_le_ofReal
  rw [Real.coe_toNNReal _ hA0.le]
  dsimp [r]
  have hs2 := Real.sq_sqrt hκ.le
  have hAe := ne_of_gt hA0
  have hse := ne_of_gt hs
  field_simp
  nlinarith

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

def PreSwallowExcursion (γ : ℝ≥0 → ℂ) (z : ℂ) (A : ℝ) : Prop :=
  ∃ t : ℝ≥0, A ≤ ‖γ t‖ ∧ ∀ u : ℝ≥0, u < t → z ∈ survivingDomain γ u

 

theorem ordinary_pre_swallow_excursion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 4 < κ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) :
    ∃ D c : ℝ, 0 < D ∧ 0 < c ∧ ∀ z ∈ upperHalfPlane, ‖z‖ = 1 →
      ∀ A : ℝ, 2 ≤ A → P {ω | PreSwallowExcursion (γ ω) z A} ≤
        ENNReal.ofReal (D*A^(-c)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C,c₀,hC,hc₀,hsurv⟩ := ordinary_survival_polynomial hB κ hκ γ G F hw
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  let c := min c₀ 1
  let D := C+4*κ+(16:ℝ)^c
  have hc : 0 < c := lt_min hc₀ (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,c,hD,hc,?_⟩
  intro z hz hunit A hA
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hA1 : 1 ≤ A := le_trans (by norm_num) hA
  have hpow : 0 < A^(-c) := Real.rpow_pos_of_pos hA0 _
  by_cases hlarge : 16 ≤ A
  · have hsub : {ω | PreSwallowExcursion (γ ω) z A} ⊆
        {ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖} ∪
        {ω | z ∈ survivingDomain (γ ω) A.toNNReal} := by
      rintro ω ⟨t,hn,hl⟩
      by_cases ht : (t:ℝ) ≤ A
      · exact Or.inl ⟨t,ht,hn⟩
      · exact Or.inr (hl A.toNNReal (by
          apply NNReal.coe_lt_coe.mp
          rw [Real.coe_toNNReal _ hA0.le]
          exact not_le.mp ht))
    have hT : (1:ℝ≥0) ≤ A.toNNReal := by
      apply NNReal.coe_le_coe.mp
      simpa only [Real.coe_toNNReal _ hA0.le, NNReal.coe_one] using hA1
    have hp₁ := ordinary_trace_excursion_tail hB κ hk γ G F hw A hlarge
    have hp₂ := hsurv z hz hunit A.toNNReal hT
    rw [Real.coe_toNNReal _ hA0.le] at hp₂
    have he₁ : A^(-1:ℝ) ≤ A^(-c) :=
      Real.rpow_le_rpow_of_exponent_le hA1 (neg_le_neg (min_le_right _ _))
    have he₂ : A^(-c₀) ≤ A^(-c) :=
      Real.rpow_le_rpow_of_exponent_le hA1 (neg_le_neg (min_le_left _ _))
    have hsum : 4*κ/A+C*A^(-c₀) ≤ D*A^(-c) := by
      calc
        _ = 4*κ*A^(-1:ℝ)+C*A^(-c₀) := by rw [Real.rpow_neg_one]; ring
        _ ≤ 4*κ*A^(-c)+C*A^(-c) := add_le_add
          (mul_le_mul_of_nonneg_left he₁ (by positivity))
          (mul_le_mul_of_nonneg_left he₂ hC.le)
        _ ≤ D*A^(-c) := by
          have hp16 : 0 ≤ (16:ℝ)^c := Real.rpow_nonneg (by norm_num) _
          dsimp [D]
          nlinarith
    calc
      _ ≤ P ({ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖} ∪
          {ω | z ∈ survivingDomain (γ ω) A.toNNReal}) := measure_mono hsub
      _ ≤ P {ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖}+
          P {ω | z ∈ survivingDomain (γ ω) A.toNNReal} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (4*κ/A)+ENNReal.ofReal (C*A^(-c₀)) := add_le_add hp₁ hp₂
      _ = ENNReal.ofReal (4*κ/A+C*A^(-c₀)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (D*A^(-c)) := ENNReal.ofReal_le_ofReal hsum
  · have hpowEq : A^c*A^(-c) = 1 := by rw [← Real.rpow_add hA0]; simp
    have h16 : A^c ≤ (16:ℝ)^c := Real.rpow_le_rpow hA0.le (not_le.mp hlarge).le hc.le
    have hD16 : (16:ℝ)^c ≤ D := by dsimp [D]; linarith
    have hbound : 1 ≤ D*A^(-c) := by
      rw [← hpowEq]
      exact mul_le_mul_of_nonneg_right (h16.trans hD16) hpow.le
    exact prob_le_one.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hbound)

end SLEExactGauge
end

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 
theorem ordinary_survival_constants
    (κ : ℝ) (hκ : 4 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {B : ℝ≥0 → Ω → ℝ}, IsBrownianReal B P →
      ∀ (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ),
      (∀ᵐ ω ∂P, IsCapacityTwoWitness
        (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) →
      ∀ z ∈ upperHalfPlane, ‖z‖ = 1 →
        ∀ T : ℝ≥0, 1 ≤ T →
        P {ω | z ∈ survivingDomain (γ ω) T} ≤ ENNReal.ofReal (C*(T:ℝ)^(-c)) := by
  let β := (κ-4)/(2*κ)
  let C := (1+3*(κ-4)/8) / min 1 (β*((κ-4)/4))
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  have hβ : 0 < β := by dsimp [β]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,β/2,hC,by positivity,?_⟩
  intro Ω _ P B hB γ G F hw z hz hu T hT
  have ht : 0 < (T:ℝ) := lt_of_lt_of_le (by norm_num) (NNReal.coe_le_coe.mpr hT)
  have hR : 1 ≤ Real.sqrt (T:ℝ) := (Real.le_sqrt (by norm_num) T.coe_nonneg).mpr (by simpa only [one_pow, NNReal.coe_one] using NNReal.coe_le_coe.mpr hT)
  have hp := ordinary_survival_radial_tail hB κ hκ γ G F hw z hz hu (Real.sqrt T) hR
  rw [Real.sq_sqrt T.coe_nonneg,Real.toNNReal_coe] at hp
  convert hp using 2
  rw [Real.rpow_def_of_pos ht,Real.log_sqrt ht.le]
  congr 2
  ring

theorem ordinary_pre_swallow_constants (κ : ℝ) (hκ : 4 < κ) :
    ∃ D c : ℝ, 0 < D ∧ 0 < c ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {B : ℝ≥0 → Ω → ℝ}, IsBrownianReal B P →
      ∀ (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ),
      (∀ᵐ ω ∂P, IsCapacityTwoWitness
        (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) →
      ∀ z ∈ upperHalfPlane, ‖z‖ = 1 →
      ∀ A : ℝ, 2 ≤ A → P {ω | PreSwallowExcursion (γ ω) z A} ≤
        ENNReal.ofReal (D*A^(-c)) := by
  obtain ⟨C,c₀,hC,hc₀,hsurv⟩ := ordinary_survival_constants κ hκ
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  let c := min c₀ 1
  let D := C+4*κ+(16:ℝ)^c
  have hc : 0 < c := lt_min hc₀ (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,c,hD,hc,?_⟩
  intro Ω _ P B hB γ G F hw z hz hunit A hA
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hA1 : 1 ≤ A := le_trans (by norm_num) hA
  have hpow : 0 < A^(-c) := Real.rpow_pos_of_pos hA0 _
  by_cases hlarge : 16 ≤ A
  · have hsub : {ω | PreSwallowExcursion (γ ω) z A} ⊆
        {ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖} ∪
        {ω | z ∈ survivingDomain (γ ω) A.toNNReal} := by
      rintro ω ⟨t,hn,hl⟩
      by_cases ht : (t:ℝ) ≤ A
      · exact Or.inl ⟨t,ht,hn⟩
      · exact Or.inr (hl A.toNNReal (by
          apply NNReal.coe_lt_coe.mp
          rw [Real.coe_toNNReal _ hA0.le]
          exact not_le.mp ht))
    have hT : (1:ℝ≥0) ≤ A.toNNReal := by
      apply NNReal.coe_le_coe.mp
      simpa only [Real.coe_toNNReal _ hA0.le, NNReal.coe_one] using hA1
    have hp₁ := ordinary_trace_excursion_tail hB κ hk γ G F hw A hlarge
    have hp₂ := hsurv hB γ G F hw z hz hunit A.toNNReal hT
    rw [Real.coe_toNNReal _ hA0.le] at hp₂
    have he₁ : A^(-1:ℝ) ≤ A^(-c) :=
      Real.rpow_le_rpow_of_exponent_le hA1 (neg_le_neg (min_le_right _ _))
    have he₂ : A^(-c₀) ≤ A^(-c) :=
      Real.rpow_le_rpow_of_exponent_le hA1 (neg_le_neg (min_le_left _ _))
    have hsum : 4*κ/A+C*A^(-c₀) ≤ D*A^(-c) := by
      calc
        _ = 4*κ*A^(-1:ℝ)+C*A^(-c₀) := by rw [Real.rpow_neg_one]; ring
        _ ≤ 4*κ*A^(-c)+C*A^(-c) := add_le_add
          (mul_le_mul_of_nonneg_left he₁ (by positivity))
          (mul_le_mul_of_nonneg_left he₂ hC.le)
        _ ≤ D*A^(-c) := by
          have hp16 : 0 ≤ (16:ℝ)^c := Real.rpow_nonneg (by norm_num) _
          dsimp [D]
          nlinarith
    calc
      _ ≤ P ({ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖} ∪
          {ω | z ∈ survivingDomain (γ ω) A.toNNReal}) := measure_mono hsub
      _ ≤ P {ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖}+
          P {ω | z ∈ survivingDomain (γ ω) A.toNNReal} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (4*κ/A)+ENNReal.ofReal (C*A^(-c₀)) := add_le_add hp₁ hp₂
      _ = ENNReal.ofReal (4*κ/A+C*A^(-c₀)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (D*A^(-c)) := ENNReal.ofReal_le_ofReal hsum
  · have hpowEq : A^c*A^(-c) = 1 := by rw [← Real.rpow_add hA0]; simp
    have h16 : A^c ≤ (16:ℝ)^c := Real.rpow_le_rpow hA0.le (not_le.mp hlarge).le hc.le
    have hD16 : (16:ℝ)^c ≤ D := by dsimp [D]; linarith
    have hbound : 1 ≤ D*A^(-c) := by
      rw [← hpowEq]
      exact mul_le_mul_of_nonneg_right (h16.trans hD16) hpow.le
    exact prob_le_one.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hbound)

 

lemma mapped_live_exit_split (γ : ℝ≥0 → ℂ) (Fbar : ℂ → OnePoint ℂ)
    (z q : ℂ) (A R : ℝ)
    (h : ∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧
      Fbar (γ t) ∉ (fun w : ℂ => (w : OnePoint ℂ)) '' Metric.ball q R) :
    (∃ t : ℝ≥0, BeforeFirstModulus γ A t ∧
      Fbar (γ t) ∉ (fun w : ℂ => (w : OnePoint ℂ)) '' Metric.ball q R) ∨
      PreSwallowExcursion γ z A := by
  classical
  obtain ⟨t,hl,hout⟩ := h
  by_cases hp : BeforeFirstModulus γ A t
  · exact Or.inl ⟨t,hp,hout⟩
  · simp only [BeforeFirstModulus,not_forall,not_lt] at hp
    obtain ⟨s,hst,hs⟩ := hp
    exact Or.inr ⟨s,hs,fun u hu => survivingDomain_antitone γ (hu.trans hst).le hl⟩

universe u
 

def SourceChartedDiskRuleTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 → ∃ C c : ℝ,
    0 < C ∧ 0 < c ∧
    ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ γ : Ω → ℝ≥0 → ℂ, IsOrdinaryChordalSLE κ γ P →
    ∀ (F : ℂ → ℂ) (Fbar : ℂ → OnePoint ℂ),
    DifferentiableOn ℂ F {z | 0 < z.im} → InjOn F {z | 0 < z.im} →
    ContinuousOn Fbar {z : ℂ | 0 ≤ z.im} →
    (∀ z : ℂ, 0 < z.im → Fbar z = (F z : OnePoint ℂ)) →
    ∀ (q : ℂ) (r : ℝ), 0 < r →
    ∀ (η : ℝ → ℂ) (T : ℝ), 0 < T → ContinuousOn η (Icc 0 T) →
    η 0 = 0 → ‖η T‖ = 1 → 0 < (η T).im → F (η T) = q →
    (∀ t ∈ Icc 0 T, 0 ≤ (η t).im) →
    (∀ t ∈ Icc 0 T, ∃ w : ℂ, Fbar (η t) = (w : OnePoint ℂ) ∧ ‖w-q‖ ≤ r) →
    ∀ L : ℝ, 1 ≤ L →
      P {xi | ∃ t : ℝ≥0, η T ∈ survivingDomain (γ xi) t ∧
        Fbar (γ xi t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)} ≤
        ENNReal.ofReal (C*L^(-c))

theorem sourceChartedDiskRule : SourceChartedDiskRuleTarget := by
  intro κ hκ hκ8
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  obtain ⟨b,C₁,c₁,L₀,hb,hC₁,hc₁,hL₀,hloc⟩ := sourceUniformConformalLocalization κ hk hκ8
  obtain ⟨C₂,c₂,hC₂,hc₂,hsw⟩ := ordinary_pre_swallow_constants κ hκ
  let c : ℝ := min c₁ (b*c₂)
  let L₁ : ℝ := max L₀ ((2:ℝ)^(1/b))
  let C : ℝ := C₁+C₂+L₁^c
  have hc : 0 < c := lt_min hc₁ (mul_pos hb hc₂)
  have hL₁ : 1 < L₁ := hL₀.trans_le (le_max_left _ _)
  have hC : 0 < C := by
    have hpow : 0 ≤ L₁^c := Real.rpow_nonneg (by linarith) _
    dsimp [C]; linarith
  refine ⟨C,c,hC,hc,?_⟩
  intro Ω mΩ P hP γ hγ F Fbar hF hi hbar hext q r hr η T hT hη hη0 hu hηi hηq hupper hpath L hL
  let : IsProbabilityMeasure P := hP
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpow : 0 < L^(-c) := Real.rpow_pos_of_pos hLp _
  by_cases hlarge : L₁ ≤ L
  · have hA : 2 ≤ L^b := by
      have hh := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (1/b))
        ((le_max_right L₀ ((2:ℝ)^(1/b))).trans hlarge) hb.le
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),one_div_mul_cancel hb.ne',Real.rpow_one] at hh
      exact hh
    have hp₁ := hloc Ω mΩ P hP γ hγ F Fbar hF hi hbar hext q r hr η T hT hη hη0 hu hupper hpath L
      ((le_max_left _ _).trans hlarge)
    obtain ⟨B,G,Fw,hB,hw⟩ := hγ.exists_charts
    have hp₂ := hsw hB γ G Fw hw (η T) hηi hu (L^b) hA
    have heq : (L^b)^(-c₂) = L^(-(b*c₂)) := by
      rw [← Real.rpow_mul hLp.le]
      congr 1
      ring
    rw [heq] at hp₂
    have hsub : {xi | ∃ t : ℝ≥0, η T ∈ survivingDomain (γ xi) t ∧
        Fbar (γ xi t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)} ⊆
      {xi | ∃ t : ℝ≥0, BeforeFirstModulus (γ xi) (L^b) t ∧
        Fbar (γ xi t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)} ∪
      {xi | PreSwallowExcursion (γ xi) (η T) (L^b)} := by
      intro xi hxi
      exact mapped_live_exit_split (γ xi) Fbar (η T) q (L^b) (L*r) hxi
    have he₁ : L^(-c₁) ≤ L^(-c) :=
      Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_left _ _))
    have he₂ : L^(-(b*c₂)) ≤ L^(-c) :=
      Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_right _ _))
    have hsum : C₁*L^(-c₁)+C₂*L^(-(b*c₂)) ≤ C*L^(-c) := by
      have hnon : 0 ≤ L₁^c := Real.rpow_nonneg (by linarith) _
      calc
        _ ≤ C₁*L^(-c)+C₂*L^(-c) := add_le_add
          (mul_le_mul_of_nonneg_left he₁ hC₁.le)
          (mul_le_mul_of_nonneg_left he₂ hC₂.le)
        _ ≤ C*L^(-c) := by dsimp [C]; nlinarith
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans
      ((add_le_add hp₁ hp₂).trans (by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal hsum)))
  · have hprod : L^c*L^(-c) = 1 := by
      rw [← Real.rpow_add hLp,add_neg_cancel,Real.rpow_zero]
    have hle : L^c ≤ L₁^c := Real.rpow_le_rpow hLp.le (not_le.mp hlarge).le hc.le
    have hbound : 1 ≤ C*L^(-c) := by
      rw [← hprod]
      apply mul_le_mul_of_nonneg_right _ hpow.le
      dsimp [C]
      linarith
    exact prob_le_one.trans (by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hbound)

end SLEExactGauge
end

end OAI
