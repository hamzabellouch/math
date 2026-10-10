import Mathlib
import OAI.Probability.SLELocalization.BrownianSupport
import OAI.Probability.SLELocalization.CommonClocks
import OAI.Probability.SLELocalization.ConformalLocalization
import OAI.Probability.SLELocalization.FirstDisk
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.ItoIsometry

namespace OAI


/-! Conformal localization and Swallowing estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.Swallowing
open GreenPhysical LoewnerCutoff LoewnerExit

lemma cutoff_eq_until {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (U : C(I,ℝ)) (hU : EqOn (extendDriver T U) driver (Icc 0 T))
    (hc : ContinuousOn driver (Icc 0 T)) {z : ℂ} (hz : z ∈ localizationDomain γ T)
    (hy : ε < (g T z).im) :
    EqOn (position hε hT.le U z) (fun t => g t z) (Icc 0 T) ∧
      stop hε hT.le U z 0 0 = T := by
  have he := h.eq_cutoff_solution hT.le hε hc hz hy.le (position_initial hε hT.le U z) (by
    intro t ht
    rw [← hU ht]
    exact position_derivWithin hε hT.le U z ht)
  have hpos (t : ℝ) (ht : t ∈ Icc 0 T) : ε < (position hε hT.le U z t).im := by
    rw [← he ht]
    exact hy.trans_le (h.height_antitone hT.le hz ht ⟨hT.le,le_rfl⟩ ht.2)
  refine ⟨he.symm,?_⟩
  apply le_antisymm (stop_bounds hε hT.le U z 0 0).2
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hn0 := nonpos_at_of_lt hε hT.le hT U z 0 0 hlt
  have ht := stop_bounds hε hT.le U z 0 0
  have hh := hpos _ ht
  have hp : 0 < deficit hε hT.le U z 0 0 (stop hε hT.le U z 0 0) := by
    apply (deficit_pos_iff hε hT.le U z 0 0 _).2
    refine ⟨?_,hh,?_⟩
    · exact div_pos (mul_pos (by norm_num) (hε.trans hh)) (Real.exp_pos _)
    · exact div_pos (hε.trans hh) (norm_pos_iff.2 (clampIm_ne_zero hε _))
  exact (not_lt_of_ge hn0) hp

def physicalQ {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ : ℝ)
    (g : Ω → ℝ → ℂ → ℂ) (z : ℂ) (ω : Ω) (t : ℝ) : ℝ :=
  ((g ω t z).re-Real.sqrt κ*B t.toNNReal ω)^2+(g ω t z).im^2

def physicalPhi {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β C : ℝ)
    (g : Ω → ℝ → ℂ → ℂ) (z : ℂ) (ω : Ω) (t : ℝ) : ℝ :=
  lyapunov β C ((g ω t z).re-Real.sqrt κ*B t.toNNReal ω) (g ω t z).im

lemma budget_dominates {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β : ℝ)
    (hκ : 4 < κ) (hβ : 0 < β) (hβκ : β < 1-4/κ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω=0)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (hT : 0 < (T:ℝ)) (z : ℂ)
    (hz : z ∈ localizationDomain (γ ω) T) (hy : ε < (g ω T z).im) :
    let C := (2*κ-8-κ*β)/4
    let d := β*(κ-4-κ*β)/2
    physicalPhi B κ β C g z ω T+d*(∫ t in (0:ℝ)..(T:ℝ), (physicalQ B κ g z ω t)^(β/2-1)) ≤
      budget B κ β C hε T z ω := by
  dsimp only
  let C := (2*κ-8-κ*β)/4
  let d := β*(κ-4-κ*β)/2
  let U := BrownianDriver.path B (Real.sqrt κ) T ω
  have hU : EqOn (extendDriver T U) (fun t => Real.sqrt κ*B t.toNNReal ω) (Icc 0 (T:ℝ)) :=
    fun t ht => BrownianDriver.extend_eq B _ T ω hc ht
  have hb := hc.comp continuous_real_toNNReal
  have hd : Continuous (fun t : ℝ => Real.sqrt κ*B t.toNNReal ω) := continuous_const.mul hb
  obtain ⟨he,hs⟩ := cutoff_eq_until h hε hT U hU hd.continuousOn hz hy
  have hh0 := h.height_antitone T.coe_nonneg hz ⟨le_rfl,T.coe_nonneg⟩ ⟨T.coe_nonneg,le_rfl⟩ T.coe_nonneg
  dsimp only at hh0
  rw [h.initial z hz.1.1] at hh0
  have hin := deterministic_budget hε hT κ β hκ hβ hβκ U z (hy.le.trans hh0)
    (fun t => B t.toNNReal ω) hb (by simpa using hb0) hU
  dsimp only at hin
  have heheight (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : LoewnerField.height hε T.coe_nonneg U z t = (g ω t z).im := by
    rw [LoewnerField.height,he ht,max_eq_right]
    exact hy.le.trans (h.height_antitone T.coe_nonneg hz ht ⟨T.coe_nonneg,le_rfl⟩ ht.2)
  have hE : (∫ t in (0:ℝ)..stop hε T.coe_nonneg U z 0 0,
      (((position hε T.coe_nonneg U z t).re-Real.sqrt κ*B t.toNNReal ω)^2+
        (LoewnerField.height hε T.coe_nonneg U z t)^2)^(β/2-1)) =
      ∫ t in (0:ℝ)..(T:ℝ), (physicalQ B κ g z ω t)^(β/2-1) := by
    rw [hs]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le T.coe_nonneg] at ht
    dsimp only
    rw [he ht,heheight t ht]
    rfl
  have hF : field hε T.coe_nonneg β C (Real.sqrt κ) U z (stop hε T.coe_nonneg U z 0 0)
      (B (stop hε T.coe_nonneg U z 0 0).toNNReal ω) = physicalPhi B κ β C g z ω T := by
    rw [hs]
    simp only [field,physicalPhi]
    rw [he ⟨T.coe_nonneg,le_rfl⟩,heheight _ ⟨T.coe_nonneg,le_rfl⟩]
  have hbound : physicalPhi B κ β C g z ω T+d*(∫ t in (0:ℝ)..(T:ℝ), (physicalQ B κ g z ω t)^(β/2-1)) ≤
      correction B κ β C hε T z ω+lyapunov β C z.re z.im := by
    have hh := hin.2
    simp only [Real.toNNReal_zero] at hh
    change field hε T.coe_nonneg β C (Real.sqrt κ) U z (stop hε T.coe_nonneg U z 0 0)
        (B (stop hε T.coe_nonneg U z 0 0).toNNReal ω) + d*_ ≤
      correction B κ β C hε T z ω+lyapunov β C z.re z.im at hh
    rw [hF,hE] at hh
    exact hh
  exact hbound.trans (by
    rw [budget,ite_eq_right (by exact ne_of_gt (show (0:ℝ≥0)<T from hT))]
    exact le_max_left _ _)

end SLEExactGauge.Swallowing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.Swallowing

lemma radial_occupation_point {q T α : ℝ} (hq : 0 < q) (hT : 0 < T)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) : T^α ≤ q^α+T*q^(α-1) := by
  by_cases hqT : T ≤ q
  · exact (Real.rpow_le_rpow hT.le hqT hα).trans (le_add_of_nonneg_right (by positivity))
  · have hh := Real.rpow_le_rpow_of_nonpos hq (not_le.1 hqT).le (by linarith : α-1≤0)
    have hid : T*T^(α-1)=T^α := by
      rw [Real.rpow_sub hT,Real.rpow_one]
      field_simp
    calc
      T^α = T*T^(α-1) := hid.symm
      _ ≤ T*q^(α-1) := mul_le_mul_of_nonneg_left hh hT.le
      _ ≤ q^α+T*q^(α-1) := le_add_of_nonneg_left (by positivity)

lemma occupation_lower {q φ : ℝ → ℝ} {T α : ℝ} (hT : 0 < T)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hq : ContinuousOn q (Icc 0 T)) (hφ : ContinuousOn φ (Icc 0 T))
    (hp : ∀ t ∈ Icc 0 T, 0 < q t) (hφq : ∀ t ∈ Icc 0 T, (q t)^α ≤ φ t) :
    T^α ≤ (∫ t in (0:ℝ)..T, (q t)^(α-1))+(∫ t in (0:ℝ)..T,φ t)/T := by
  have hH : ContinuousOn (fun t => (q t)^(α-1)) (Icc 0 T) :=
    hq.rpow_const (fun t ht => Or.inl (hp t ht).ne')
  have hiφ := hφ.intervalIntegrable_of_Icc (μ := volume) hT.le
  have hiH := hH.intervalIntegrable_of_Icc (μ := volume) hT.le
  have hm : (∫ _ in (0:ℝ)..T,T^α) ≤ ∫ t in (0:ℝ)..T,φ t+T*(q t)^(α-1) := by
    apply intervalIntegral.integral_mono_on hT.le (intervalIntegrable_const) (hiφ.add (hiH.const_mul T))
    intro t ht
    exact (radial_occupation_point (hp t ht) hT hα hα1).trans (add_le_add (hφq t ht) le_rfl)
  rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul,
    intervalIntegral.integral_add hiφ (hiH.const_mul T),intervalIntegral.integral_const_mul] at hm
  have hm := (le_div_iff₀ hT).2 (by simpa only [mul_comm] using hm)
  calc
    T^α ≤ ((∫ t in (0:ℝ)..T,φ t)+T*(∫ t in (0:ℝ)..T,(q t)^(α-1)))/T := hm
    _ = _ := by field_simp; ring

lemma average_riemann_tendsto {φ : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hφ : ContinuousOn φ (Icc 0 T)) :
    Tendsto (fun n => (∑ i ∈ Finset.range (2^n),φ (TaylorMeshes.mesh T n i))/(2:ℝ)^n)
      atTop (𝓝 ((∫ t in (0:ℝ)..T,φ t)/T)) := by
  have hh := (TaylorMeshes.mesh_riemann_tendsto hT.le hφ).div_const T
  convert hh using 1
  funext n
  rw [← Finset.sum_mul]
  field_simp

end SLEExactGauge.Swallowing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.Swallowing
open BrownianPredictable

def heightCut (z : ℂ) (n : ℕ) : ℝ := z.im / ((n:ℝ)+1)

lemma heightCut_pos {z : ℂ} (hz : z ∈ halfPlane) (n : ℕ) : 0 < heightCut z n :=
  div_pos hz (by positivity)

lemma heightCut_le {z : ℂ} (hz : z ∈ halfPlane) (n : ℕ) : heightCut z n ≤ z.im := by
  apply div_le_self hz.le
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma heightCut_tendsto (z : ℂ) : Tendsto (heightCut z) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => z.im/((n:ℝ)+1)) atTop (𝓝 0)
  simpa only [mul_one,mul_zero,div_eq_mul_inv,one_mul] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul z.im

def averagedBudget {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β : ℝ)
    (T : ℝ≥0) (z : ℂ) (hz : z∈halfPlane) (n : ℕ) (ω : Ω) : ℝ :=
  let C := (2*κ-8-κ*β)/4
  let d := β*(κ-4-κ*β)/2
  budget B κ β C (heightCut_pos hz n) T z ω/d+
    (∑ i ∈ Finset.range (2^n), budget B κ β C (heightCut_pos hz n) (dyadicTime T n i) z ω)/(2:ℝ)^n

lemma averagedBudget_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ β : ℝ)
    (hκ : 4 < κ) (hβ : 0 < β) (hβκ : β < 1-4/κ)
    (T : ℝ≥0) (z : ℂ) (hz : z∈halfPlane) (n : ℕ) :
    let C := (2*κ-8-κ*β)/4
    let d := β*(κ-4-κ*β)/2
    Integrable (averagedBudget B κ β T z hz n) P ∧
      (∫ ω,averagedBudget B κ β T z hz n ω ∂P) =
        lyapunov β C z.re z.im/d+lyapunov β C z.re z.im ∧
      ∀ ω, 0 ≤ averagedBudget B κ β T z hz n ω := by
  dsimp only
  let C := (2*κ-8-κ*β)/4
  let d := β*(κ-4-κ*β)/2
  have hd : 0 < d := (generator_negative hκ hβ hβκ z.re hz).2.1
  have hb (S : ℝ≥0) := budget_mean hB κ β hκ hβ hβκ (heightCut_pos hz n) S z (heightCut_le hz n)
  have hs : Integrable (fun ω => ∑ i ∈ Finset.range (2^n), budget B κ β C (heightCut_pos hz n) (dyadicTime T n i) z ω) P :=
    integrable_finsetSum _ (fun i hi => (hb _).1)
  refine ⟨((hb T).1.div_const d).add (hs.div_const _),?_,?_⟩
  · change (∫ ω,budget B κ β C (heightCut_pos hz n) T z ω/d+
      (∑ i ∈ Finset.range (2^n), budget B κ β C (heightCut_pos hz n) (dyadicTime T n i) z ω)/(2:ℝ)^n ∂P)=_
    rw [integral_add ((hb T).1.div_const _) (hs.div_const _),integral_div,integral_div,
      (hb T).2.1,integral_finsetSum _ (fun i hi => (hb _).1)]
    simp only [(hb _).2.1,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    change lyapunov β C z.re z.im/d+((2:ℝ)^n*lyapunov β C z.re z.im)/(2:ℝ)^n =
      lyapunov β C z.re z.im/d+lyapunov β C z.re z.im
    congr 1
    field_simp
  · intro ω
    apply add_nonneg
    · exact div_nonneg ((hb T).2.2 ω) hd.le
    · exact div_nonneg (Finset.sum_nonneg fun i hi => (hb _).2.2 ω) (by positivity)

end SLEExactGauge.Swallowing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.Swallowing
open BrownianPredictable BrownianField BrownianIto TaylorMeshes GreenPhysical

lemma budget_terminal_bound {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β : ℝ)
    (hκ : 4 < κ) (hβ : 0 < β) (hβκ : β < 1-4/κ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω=0)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ localizationDomain (γ ω) T) (hy : ε < (g ω T z).im) :
    let C := (2*κ-8-κ*β)/4
    physicalPhi B κ β C g z ω T ≤ budget B κ β C hε T z ω := by
  dsimp only
  by_cases ht : T=0
  · subst T
    simp [physicalPhi,h.initial z hz.1.1,hb0,budget]
  have hT : 0 < (T:ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht)
  have hh := budget_dominates B κ β hκ hβ hβκ γ g f ω h hc hb0 hε T hT z hz hy
  have hd := (generator_negative hκ hβ hβκ z.re hz.1.1).2.1
  have hE : 0 ≤ ∫ t in (0:ℝ)..(T:ℝ), (physicalQ B κ g z ω t)^(β/2-1) := by
    apply intervalIntegral.integral_nonneg T.coe_nonneg
    intro t ht
    exact Real.rpow_nonneg (by dsimp [physicalQ]; positivity) _
  exact (le_add_of_nonneg_right (mul_nonneg hd.le hE)).trans hh

lemma physical_continuous {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β C : ℝ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) {T : ℝ} (hT : 0 ≤ T) (z : ℂ)
    (hz : z ∈ localizationDomain (γ ω) T) :
    ContinuousOn (physicalQ B κ g z ω) (Icc 0 T) ∧
      ContinuousOn (physicalPhi B κ β C g z ω) (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, 0 < physicalQ B κ g z ω t := by
  have hg := h.continuous_eval hT hz
  have hx := (Complex.continuous_re.comp_continuousOn hg).sub
    ((continuous_const.mul (hc.comp continuous_real_toNNReal) : Continuous (fun t : ℝ => Real.sqrt κ*B t.toNNReal ω)).continuousOn)
  have hy := Complex.continuous_im.comp_continuousOn hg
  have hyp (t : ℝ) (ht : t∈Icc 0 T) := h.im_pos ht.1 (survivingDomain_mono ht.2 hz)
  have hq : ContinuousOn (physicalQ B κ g z ω) (Icc 0 T) := (hx.pow 2).add (hy.pow 2)
  have hqp (t : ℝ) (ht : t∈Icc 0 T) : 0 < physicalQ B κ g z ω t := q_pos _ (hyp t ht)
  refine ⟨hq,?_,hqp⟩
  exact (hq.rpow_const (fun t ht => Or.inl (hqp t ht).ne')).add
    (continuousOn_const.mul (hy.rpow_const (fun t ht => Or.inl (hyp t ht).ne')))

lemma averagedBudget_lower {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β : ℝ)
    (hκ : 4 < κ) (hβ : 0 < β) (hβκ : β < 1-4/κ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω=0)
    (T : ℝ≥0) (hT : 0 < (T:ℝ)) (z : ℂ) (hz : z ∈ halfPlane)
    (halive : z ∈ localizationDomain (γ ω) T) (n : ℕ) (hy : heightCut z n < (g ω T z).im) :
    let C := (2*κ-8-κ*β)/4
    (∫ t in (0:ℝ)..(T:ℝ), (physicalQ B κ g z ω t)^(β/2-1))+
      (∑ i ∈ Finset.range (2^n),physicalPhi B κ β C g z ω (mesh T n i))/(2:ℝ)^n ≤
        averagedBudget B κ β T z hz n ω := by
  dsimp only
  let C := (2*κ-8-κ*β)/4
  let d := β*(κ-4-κ*β)/2
  have hgen := generator_negative hκ hβ hβκ z.re hz
  have hd : 0 < d := hgen.2.1
  have hphi : 0 ≤ physicalPhi B κ β C g z ω T :=
    lyapunov_nonneg hgen.1.le _ (h.im_pos T.coe_nonneg halive)
  have hh := budget_dominates B κ β hκ hβ hβκ γ g f ω h hc hb0 (heightCut_pos hz n) T hT z halive hy
  have hEc : (∫ t in (0:ℝ)..(T:ℝ), (physicalQ B κ g z ω t)^(β/2-1)) ≤
      budget B κ β C (heightCut_pos hz n) T z ω/d := by
    apply (le_div_iff₀ hd).2
    change physicalPhi B κ β C g z ω T+d*(∫ t in (0:ℝ)..(T:ℝ), (physicalQ B κ g z ω t)^(β/2-1)) ≤
      budget B κ β C (heightCut_pos hz n) T z ω at hh
    nlinarith only [hh,hphi]
  apply add_le_add hEc
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro i hi
  have hti : (dyadicTime T n i : ℝ) ∈ Icc 0 (T:ℝ) := by
    rw [coe_dyadicTime]
    exact mesh_mem T T.coe_nonneg n i (Finset.mem_range.1 hi).le
  have hiY := hy.trans_le (h.height_antitone T.coe_nonneg halive hti ⟨T.coe_nonneg,le_rfl⟩ hti.2)
  have hbound := budget_terminal_bound B κ β hκ hβ hβκ γ g f ω h hc hb0 (heightCut_pos hz n)
    (dyadicTime T n i) z (survivingDomain_mono hti.2 halive) hiY
  simpa only [coe_dyadicTime] using hbound

lemma eventually_budget_large {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (κ β : ℝ)
    (hκ : 4 < κ) (hβ : 0 < β) (hβκ : β < 1-4/κ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω=0)
    (T : ℝ≥0) (hT : 0 < (T:ℝ)) (z : ℂ) (hz : z ∈ halfPlane)
    (halive : z ∈ localizationDomain (γ ω) T) :
    ∀ᶠ n in atTop, (T:ℝ)^(β/2)/2 ≤ averagedBudget B κ β T z hz n ω := by
  let C := (2*κ-8-κ*β)/4
  let E := ∫ t in (0:ℝ)..(T:ℝ), (physicalQ B κ g z ω t)^(β/2-1)
  let φ := physicalPhi B κ β C g z ω
  have hh := physical_continuous B κ β C γ g f ω h hc T.coe_nonneg z halive
  have hg := generator_negative hκ hβ hβκ z.re hz
  have hβ1 : β/2 ≤ 1 := by have h4 := div_pos (by norm_num : (0:ℝ)<4) (by linarith : 0<κ); linarith
  have hφq (t : ℝ) (ht : t∈Icc 0 (T:ℝ)) : (physicalQ B κ g z ω t)^(β/2) ≤ φ t := by
    apply le_add_of_nonneg_right
    exact mul_nonneg hg.1.le (Real.rpow_nonneg (h.im_pos ht.1 (survivingDomain_mono ht.2 halive)).le _)
  have hbound := occupation_lower hT (by positivity : (0:ℝ)≤β/2) hβ1 hh.1 hh.2.1 hh.2.2 hφq
  have hlim := (average_riemann_tendsto hT hh.2.1).const_add E
  have hlt : (T:ℝ)^(β/2)/2 < E+(∫ t in (0:ℝ)..(T:ℝ),φ t)/(T:ℝ) := by
    have hp := Real.rpow_pos_of_pos hT (β/2)
    linarith
  have hlower := hlim.eventually (lt_mem_nhds hlt)
  have hcut := (heightCut_tendsto z).eventually (gt_mem_nhds (h.im_pos T.coe_nonneg halive))
  filter_upwards [hcut,hlower] with n hcut hn
  exact hn.le.trans (averagedBudget_lower B κ β hκ hβ hβκ γ g f ω h hc hb0 T hT z hz halive n hcut)

end SLEExactGauge.Swallowing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.Swallowing

lemma initial_uniform {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C) {z : ℂ}
    (hz : z ∈ halfPlane) (hn : ‖z‖=1) : lyapunov β C z.re z.im ≤ 1+C := by
  have hq : z.re^2+z.im^2=1 := by
    have hh : ‖z‖^2=1 := by rw [hn]; norm_num
    rw [Complex.sq_norm] at hh
    simpa only [Complex.normSq_apply,pow_two] using hh
  have hy1 : z.im ≤ 1 := by simpa only [hn] using Complex.im_le_norm z
  have hpow := Real.rpow_le_rpow hz.le hy1 hβ
  simp only [Real.one_rpow] at hpow
  simp only [lyapunov,radial,hq,Real.one_rpow]
  exact add_le_add le_rfl (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hC)

lemma survival_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ β : ℝ)
    (hκ : 4 < κ) (hβ : 0 < β) (hβκ : β < 1-4/κ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ ω ∂P, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (T : ℝ≥0) (hT : 0 < (T:ℝ)) (z : ℂ) (hz : z∈halfPlane) (hn : ‖z‖=1) :
    let C := (2*κ-8-κ*β)/4
    let d := β*(κ-4-κ*β)/2
    P {ω | z ∈ localizationDomain (γ ω) T} ≤
      ENNReal.ofReal (2*((1+C)/d+(1+C))*(T:ℝ)^(-(β/2))) := by
  dsimp only
  let C := (2*κ-8-κ*β)/4
  let d := β*(κ-4-κ*β)/2
  let M := lyapunov β C z.re z.im/d+lyapunov β C z.re z.im
  have hgen := generator_negative hκ hβ hβκ z.re hz
  have hd : 0 < d := hgen.2.1
  have hW (n : ℕ) := averagedBudget_mean hB κ β hκ hβ hβκ T z hz n
  have he : ∀ᵐ ω ∂P, z ∈ localizationDomain (γ ω) T →
      ∀ᶠ n in atTop, (T:ℝ)^(β/2)/2 ≤ averagedBudget B κ β T z hz n ω := by
    filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hm hc hb0
    intro halive
    exact eventually_budget_large B κ β hκ hβ hβκ γ g f ω hm hc hb0 T hT z hz halive
  have hbound := measure_eventually_budget (averagedBudget B κ β T z hz) M ((T:ℝ)^(β/2)/2)
    (by positivity) (fun n => (hW n).1) (fun n ω => (hW n).2.2 ω) (fun n => (hW n).2.1)
    {ω | z ∈ localizationDomain (γ ω) T} he
  have hinit := initial_uniform hβ.le hgen.1.le hz hn
  have hM : M ≤ (1+C)/d+(1+C) := add_le_add (div_le_div_of_nonneg_right hinit hd.le) hinit
  have hp : 0 < (T:ℝ)^(β/2) := Real.rpow_pos_of_pos hT _
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    M/((T:ℝ)^(β/2)/2) ≤ ((1+C)/d+(1+C))/((T:ℝ)^(β/2)/2) := div_le_div_of_nonneg_right hM (by positivity)
    _ = _ := by
      change ((1+C)/d+(1+C))/((T:ℝ)^(β/2)/2) = 2*((1+C)/d+(1+C))*(T:ℝ)^(-(β/2))
      rw [Real.rpow_neg hT.le]
      field_simp

end SLEExactGauge.Swallowing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open Swallowing

theorem swallowingTime_tail (κ : ℝ) (hκ : 4 < κ ∧ κ < 8) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
        (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
        (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
        (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
          (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
        (z : ℂ), z ∈ halfPlane → ‖z‖ = 1 → ∀ t : ℝ, 0 < t →
        P {sample | z ∈ localizationDomain (γ sample) t} ≤ ENNReal.ofReal (C*t^(-c)) := by
  let β := (1-4/κ)/2
  have hκ0 : 0 < κ := by linarith [hκ.1]
  have ha : 0 < 1-4/κ := sub_pos.2 ((div_lt_one hκ0).2 hκ.1)
  have hβ : 0 < β := half_pos ha
  have hβκ : β < 1-4/κ := half_lt_self ha
  let C := (2*κ-8-κ*β)/4
  let d := β*(κ-4-κ*β)/2
  have hgen := generator_negative hκ.1 hβ hβκ 0 (by norm_num : (0:ℝ)<1)
  have hC : 0 < C := hgen.1
  have hd : 0 < d := hgen.2.1
  refine ⟨2*((1+C)/d+(1+C)),β/2,by positivity,by positivity,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps z hz hn t ht
  exact survival_bound hB κ β hκ.1 hβ hβκ γ g f hmaps ⟨t,ht.le⟩ ht z hz hn

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

def excursionBeforeSwallowing (γ : ℝ → ℂ) (z : ℂ) (A : ℝ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ A ≤ ‖γ t‖ ∧
    ∀ s ∈ Ico 0 t, z ∈ localizationDomain γ s

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
namespace Swallowing

lemma early_excursion_forces_driver {κ A : ℝ} (hκ : 0 < κ) (hA : 8 < A)
    {B : ℝ≥0 → ℝ} (hB : Continuous B) {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ * B t.toNNReal) γ g f)
    {t : ℝ} (ht : t ∈ Icc 0 A) (he : A ≤ ‖γ t‖) :
    ∃ s ∈ Icc 0 (A.toNNReal), A/(2*Real.sqrt κ) < |B s| := by
  by_contra! hmax
  have hsqrt : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hbound : ∀ s ∈ Icc 0 A,
      -A/2 ≤ Real.sqrt κ * B s.toNNReal ∧ Real.sqrt κ * B s.toNNReal ≤ A/2 := by
    intro s hs
    have hb := hmax s.toNNReal ⟨by positivity, Real.toNNReal_le_toNNReal hs.2⟩
    have ha : |Real.sqrt κ * B s.toNNReal| ≤ A/2 := by
      rw [abs_mul,abs_of_pos hsqrt]
      calc
        Real.sqrt κ * |B s.toNNReal| ≤ Real.sqrt κ*(A/(2*Real.sqrt κ)) :=
          mul_le_mul_of_nonneg_left hb hsqrt.le
        _ = A/2 := by field_simp
    exact ⟨by linarith [(abs_le.1 ha).1], (abs_le.1 ha).2⟩
  have hr := trace_driver_rectangle hm (by linarith : 0 ≤ A)
    ((continuous_const.mul (hB.comp continuous_real_toNNReal)).continuousOn) hbound t ht
  have hx : (γ t).re^2 ≤ A^2/4 := by nlinarith [sq_nonneg ((γ t).re+A/2),sq_nonneg ((γ t).re-A/2)]
  have hn : A^2 ≤ (γ t).re^2+(γ t).im^2 := by
    have hh := sq_le_sq₀ (by linarith : 0 ≤ A) (norm_nonneg (γ t)) |>.2 he
    rw [Complex.sq_norm,Complex.normSq_apply] at hh
    simpa only [pow_two] using hh
  nlinarith [sq_nonneg (A-8),hr.2.2,ht.2]

lemma excursion_split {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ ω ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (z : ℂ) (A : ℝ) (hA : 8 < A) :
    P {ω | excursionBeforeSwallowing (γ ω) z A} ≤
      P {ω | z ∈ localizationDomain (γ ω) A}+ ENNReal.ofReal (4*κ/A) := by
  have hsub : ∀ᵐ ω ∂P, excursionBeforeSwallowing (γ ω) z A →
      z ∈ localizationDomain (γ ω) A ∨
      ∃ s ∈ Icc 0 A.toNNReal, A/(2*Real.sqrt κ) < |B s ω| := by
    filter_upwards [hmaps,hB.cont] with ω hm hc he
    obtain ⟨t,ht,hn,hlive⟩ := he
    by_cases hta : t ≤ A
    · exact Or.inr (early_excursion_forces_driver hκ hA hc hm ⟨ht,hta⟩ hn)
    · exact Or.inl (hlive A ⟨by linarith,lt_of_not_ge hta⟩)
  have hb := BrownianSupport.brownian_oscillation_bound hB A.toNNReal
    (a := A/(2*Real.sqrt κ)) (by positivity)
  have hcalc : (A.toNNReal:ℝ)/(A/(2*Real.sqrt κ))^2 = 4*κ/A := by
    rw [Real.coe_toNNReal A (by linarith)]
    have ha0 : A ≠ 0 := by linarith
    have hs0 : Real.sqrt κ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hκ)
    field_simp
    nlinarith [Real.sq_sqrt hκ.le]
  rw [hcalc] at hb
  have hm : P {ω | excursionBeforeSwallowing (γ ω) z A} ≤
      P ({ω | z ∈ localizationDomain (γ ω) A} ∪
        {ω | ∃ s ∈ Icc 0 A.toNNReal, A/(2*Real.sqrt κ) < |B s ω|}) := measure_mono_ae hsub
  exact hm.trans ((measure_union_le _ _).trans (add_le_add le_rfl hb))

end Swallowing

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

theorem swallowing_excursion_tail (κ : ℝ) (hκ : 4 < κ ∧ κ < 8) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
        (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
        (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
        (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
          (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
        (z : ℂ), z ∈ halfPlane → ‖z‖ = 1 → ∀ A : ℝ, 2 ≤ A →
        P {sample | excursionBeforeSwallowing (γ sample) z A} ≤
          ENNReal.ofReal (C*A^(-c)) := by
  obtain ⟨C₀,c₀,hC₀,hc₀,htail⟩ := swallowingTime_tail κ hκ
  let c := min c₀ 1
  let C := C₀+4*κ+8
  have hκ0 : 0 < κ := by linarith [hκ.1]
  have hc : 0 < c := lt_min hc₀ zero_lt_one
  have hc1 : c ≤ 1 := min_le_right _ _
  have hcc : c ≤ c₀ := min_le_left _ _
  have hC8 : 8 ≤ C := by dsimp [C]; linarith
  refine ⟨C,c,by linarith,hc,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps z hz hn A hA
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hp : 0 < A^(-c) := Real.rpow_pos_of_pos hA0 _
  by_cases hlarge : 8 < A
  · have hsplit := Swallowing.excursion_split hB κ hκ0 γ g f hmaps z A hlarge
    have htime := htail P B hB γ g f hγ hmaps z hz hn A hA0
    refine (hsplit.trans (add_le_add htime le_rfl)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hpow := Real.rpow_le_rpow_of_exponent_le hA1 (neg_le_neg hcc)
    have hinv : (1:ℝ)/A ≤ A^(-c) := by
      have hh := Real.rpow_le_rpow_of_exponent_le hA1 (neg_le_neg hc1)
      simpa only [Real.rpow_neg_one,one_div] using hh
    calc
      C₀*A^(-c₀)+4*κ/A ≤ C₀*A^(-c)+4*κ*A^(-c) :=
        add_le_add (mul_le_mul_of_nonneg_left hpow hC₀.le) (by
          simpa only [div_eq_mul_inv,mul_one,one_mul,mul_assoc] using
            mul_le_mul_of_nonneg_left hinv (show 0 ≤ 4*κ by positivity))
      _ ≤ C*A^(-c) := by dsimp [C]; nlinarith
  · have hsmall : A ≤ 8 := le_of_not_gt hlarge
    have hac : A^c ≤ 8 := by
      have hh := Real.rpow_le_rpow_of_exponent_le hA1 hc1
      have hh' : A^c ≤ A := by simpa only [Real.rpow_one] using hh
      exact hh'.trans hsmall
    have h8 : (1:ℝ) ≤ 8*A^(-c) := by
      rw [Real.rpow_neg hA0.le,← div_eq_mul_inv]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hA0 c)).2 (by simpa using hac)
    have hone : (1:ℝ) ≤ C*A^(-c) := h8.trans (mul_le_mul_of_nonneg_right hC8 hp.le)
    exact prob_le_one.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hone)

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal NNReal OnePoint
namespace SLEExactGauge

def mappedLiveExit (Fbar : ℂ → OnePoint ℂ) (γ : ℝ → ℂ)
    (z q : ℂ) (radius : ℝ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ z ∈ localizationDomain γ t ∧
    Fbar (γ t) ∉ (fun w : ℂ => (w : OnePoint ℂ)) '' Metric.ball q radius

lemma mappedLiveExit_split {Fbar : ℂ → OnePoint ℂ} {γ : ℝ → ℂ}
    {z q : ℂ} {radius A : ℝ} (he : mappedLiveExit Fbar γ z q radius) :
    conformalExit Fbar γ q radius A ∨ excursionBeforeSwallowing γ z A := by
  obtain ⟨t,ht,hz,hout⟩ := he
  by_cases hpre : ∀ s : ℝ, 0 ≤ s → s < t → ‖γ s‖ < A
  · exact Or.inl ⟨t,ht,hpre,hout⟩
  · push Not at hpre
    obtain ⟨s,hs,hst,hn⟩ := hpre
    exact Or.inr ⟨s,hs,hn,fun u hu => survivingDomain_mono (hu.2.trans hst).le hz⟩

theorem mapped_live_exit_tail (κ : ℝ) (hκ : 4 < κ ∧ κ < 8) :
    ∃ c C L₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < L₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
        (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
        (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
        (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
          (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
        (F : ℂ → ℂ) (Fbar : ℂ → OnePoint ℂ)
        (_hF : AnalyticOnNhd ℂ F halfPlane) (_hinj : Set.InjOn F halfPlane)
        (_hext : ∀ z ∈ halfPlane, Fbar z = (F z : OnePoint ℂ))
        (_hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
        (η : ℝ → ℂ) (_hη : ContinuousOn η (Icc 0 1)) (_hη0 : η 0 = 0)
        (_hη1 : ‖η 1‖ = 1) (_hηH : ∀ t ∈ Icc 0 1, 0 ≤ (η t).im)
        (z q : ℂ) (_hz : z ∈ halfPlane) (_hznorm : ‖z‖ = 1) (_hzq : F z = q)
        (r : ℝ) (_hr : 0 < r)
        (_haccess : ∀ t ∈ Icc 0 1, Fbar (η t) ∈
          (fun w : ℂ => (w : OnePoint ℂ)) '' Metric.closedBall q r)
        (L : ℝ), L₀ ≤ L →
        P {sample | mappedLiveExit Fbar (γ sample) z q (L*r)} ≤
          ENNReal.ofReal (C*L^(-c)) := by
  have hκ0 : 0 < κ := by linarith [hκ.1]
  obtain ⟨b,c₁,C₁,L₁,hb,hc₁,hC₁,hL₁,hloc⟩ := uniform_conformal_localization κ ⟨hκ0,hκ.2⟩
  obtain ⟨C₂,c₂,hC₂,hc₂,hswallow⟩ := swallowing_excursion_tail κ hκ
  let c := min c₁ (b*c₂)
  let L₀ := max L₁ ((2:ℝ)^(1/b))
  have hc : 0 < c := lt_min hc₁ (mul_pos hb hc₂)
  refine ⟨c,C₁+C₂,L₀,hc,add_pos hC₁ hC₂,hL₁.trans_le (le_max_left _ _),?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps F Fbar hF hinj hext hcont η hη hη0 hη1 hηH z q hz hznorm hzq r hr haccess L hlarge
  have hLL : L₁ ≤ L := (le_max_left _ _).trans hlarge
  have hL : 1 < L := hL₁.trans_le hLL
  have hLp : 0 < L := zero_lt_one.trans hL
  have hA : (2:ℝ) ≤ L^b := by
    calc
      2 = ((2:ℝ)^(1/b))^b := by rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),one_div_mul_cancel hb.ne',Real.rpow_one]
      _ ≤ L^b := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) ((le_max_right _ _).trans hlarge) hb.le
  have hp₁ := hloc P B hB γ g f hγ hmaps F Fbar hF hinj hext hcont η hη hη0 hη1 hηH q r hr haccess L hLL
  have hp₂ := hswallow P B hB γ g f hγ hmaps z hz hznorm (L^b) hA
  have hsub : {ω | mappedLiveExit Fbar (γ ω) z q (L*r)} ⊆
      {ω | conformalExit Fbar (γ ω) q (L*r) (L^b)} ∪
        {ω | excursionBeforeSwallowing (γ ω) z (L^b)} := fun ω he => mappedLiveExit_split he
  have hpow₁ : L^(-c₁) ≤ L^(-c) := Real.rpow_le_rpow_of_exponent_le hL.le (neg_le_neg (min_le_left _ _))
  have hpow₂ : (L^b)^(-c₂) ≤ L^(-c) := by
    rw [← Real.rpow_mul hLp.le]
    apply Real.rpow_le_rpow_of_exponent_le hL.le
    nlinarith [show c ≤ b*c₂ from min_le_right _ _]
  calc
    _ ≤ P ({ω | conformalExit Fbar (γ ω) q (L*r) (L^b)} ∪
        {ω | excursionBeforeSwallowing (γ ω) z (L^b)}) := measure_mono hsub
    _ ≤ P {ω | conformalExit Fbar (γ ω) q (L*r) (L^b)}+
        P {ω | excursionBeforeSwallowing (γ ω) z (L^b)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁*L^(-c₁))+ENNReal.ofReal (C₂*(L^b)^(-c₂)) := add_le_add hp₁ hp₂
    _ = ENNReal.ofReal (C₁*L^(-c₁)+C₂*(L^b)^(-c₂)) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      calc
        _ ≤ C₁*L^(-c)+C₂*L^(-c) := add_le_add (mul_le_mul_of_nonneg_left hpow₁ hC₁.le) (mul_le_mul_of_nonneg_left hpow₂ hC₂.le)
        _ = _ := by ring)

end SLEExactGauge

end

end

end OAI
