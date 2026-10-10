import Mathlib
import OAI.Probability.Ballisticity.Geometry.BufferAllHeightRetention

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferRetentionCost_le_one (R g : ℝ) {κ : ℝ≥0} (hκ : κ ≤ 1) (hg : g ≤ 1) :
    bufferRetentionCost R g κ ≤ 1 := by
  have hk : (κ:ℝ≥0∞) ≤ 1 := by exact_mod_cast hκ
  have hgg : ENNReal.ofReal g ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hg
  have hp (n : ℕ) : (κ:ℝ≥0∞)^n ≤ 1 := pow_le_one₀ (show (0:ℝ≥0∞) ≤ κ from zero_le) hk
  unfold bufferRetentionCost
  calc
    (κ:ℝ≥0∞)^2*ENNReal.ofReal g*(κ:ℝ≥0∞)^(⌈max 0 R⌉₊+2) ≤ (1*1)*1 := by gcongr <;> exact hp _
    _ = 1 := by simp

lemma buffer_initial_partial_cost_bounds (R : ℝ) {g : ℝ} (hg0 : 0 < g) (hg : g ≤ 1)
    {κ : ℝ≥0} (hk0 : 0 < κ) (hk : κ ≤ 1) :
    0 < (κ:ℝ≥0∞)^(⌈R⌉₊+2)*((κ:ℝ≥0∞)^2*ENNReal.ofReal g) ∧
    (κ:ℝ≥0∞)^(⌈R⌉₊+2)*((κ:ℝ≥0∞)^2*ENNReal.ofReal g) ≤ 1 := by
  have hκ : (κ:ℝ≥0∞) ≤ 1 := by exact_mod_cast hk
  have hgg : ENNReal.ofReal g ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hg
  constructor
  · positivity
  · have hp (n : ℕ) : (κ:ℝ≥0∞)^n ≤ 1 := pow_le_one₀ (show (0:ℝ≥0∞) ≤ κ from zero_le) hκ
    calc
      (κ:ℝ≥0∞)^(⌈R⌉₊+2)*((κ:ℝ≥0∞)^2*ENNReal.ofReal g) ≤ 1*(1*1) := by gcongr <;> exact hp _
      _ = 1 := by simp
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma logarithmic_retention_bound {c q a b C W p : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hq1 : q ≤ 1) (ha : 0 < a) (hb : 0 ≤ b) (hW : 0 ≤ W)
    (n t : ℕ) (hp : c*q^n ≤ p)
    (hn : a*(n:ℝ) ≤ Real.log C+Real.log ((t:ℝ)+2)+b*W) :
    -Real.log p ≤ ((-Real.log q)/a)*Real.log ((t:ℝ)+2)+
      (1+|Real.log c|+((-Real.log q)/a)*(|Real.log C|+b))*(W+1) := by
  have hprod : 0 < c*q^n := mul_pos hc (pow_pos hq _)
  have hp0 := hprod.trans_le hp
  have hlog := Real.log_le_log hprod hp
  rw [Real.log_mul hc.ne' (pow_pos hq n).ne',Real.log_pow] at hlog
  have hqlog : 0 ≤ -Real.log q := neg_nonneg.mpr (Real.log_nonpos hq.le hq1)
  let u := (-Real.log q)/a
  have hu : 0 ≤ u := div_nonneg hqlog ha.le
  have hua : u*a = -Real.log q := div_mul_cancel₀ _ ha.ne'
  have hmul := mul_le_mul_of_nonneg_left hn hu
  have hmul' : (n:ℝ)*(-Real.log q) ≤ u*Real.log C+u*Real.log ((t:ℝ)+2)+u*b*W := by
    calc
      _ = u*(a*(n:ℝ)) := by rw [←mul_assoc,hua]; ring
      _ ≤ u*(Real.log C+Real.log ((t:ℝ)+2)+b*W) := hmul
      _ = _ := by ring
  have hCabs : u*Real.log C ≤ u*|Real.log C| := mul_le_mul_of_nonneg_left (le_abs_self _) hu
  have hcabs : -Real.log c ≤ |Real.log c| := neg_le_abs _
  have hcross : 0 ≤ (1+|Real.log c|+u*|Real.log C|)*W := by positivity
  have hub : 0 ≤ u*b := mul_nonneg hu hb
  change -Real.log p ≤ u*Real.log ((t:ℝ)+2)+(1+|Real.log c|+u*(|Real.log C|+b))*(W+1)
  nlinarith
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def outwardKernelMass {d : ℕ} (e f : Direction d) (H : ℕ)
    (x : Lattice d × Lattice d) (ω : Environment d) : ℝ :=
  (rawPairEndpointLaw (realPosition (step e)) H ω x
    {y | signedCoordinate f (x.2-x.1) ≤ signedCoordinate f (y.2-y.1)}).toReal

theorem actual_outward_log_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A D B : ℝ, 0 < A ∧ 0 < D ∧ 0 < B ∧
      ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ W : Environment d → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
        Integrable (fun ω => Real.exp (W ω)) (environmentLaw ν) ∧
        (∫ ω, Real.exp (W ω) ∂environmentLaw ν) ≤ B ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ t : ℕ,
          0 < outwardKernelMass e f (t+1) x ω ∧
          -Real.log (outwardKernelMass e f (t+1) x ω) ≤
            A*Real.log ((t:ℝ)+2)+D*(W ω+1)) := by
  obtain ⟨κ,α,s,g,R,C,hκ,hκ1,hκae,hα,hs,hg,hg1,hR,_,hdata⟩ :=
    actual_buffer_stage_count ν hue e f hef htrans
  let qE := bufferRetentionCost R g κ
  let cE := (κ:ℝ≥0∞)^(⌈R⌉₊+2)*((κ:ℝ≥0∞)^2*ENNReal.ofReal g)
  have hqE0 : 0 < qE := bufferRetentionCost_pos R hg hκ
  have hqE1 : qE ≤ 1 := bufferRetentionCost_le_one R g hκ1 hg1
  obtain ⟨hcE0,hcE1⟩ := buffer_initial_partial_cost_bounds R hg hg1 hκ hκ1
  have hqEt : qE ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hqE1
  have hcEt : cE ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hcE1
  let q := qE.toReal
  let c := cE.toReal
  have hq : 0 < q := ENNReal.toReal_pos hqE0.ne' hqEt
  have hc : 0 < c := ENNReal.toReal_pos hcE0.ne' hcEt
  have hq1 : q ≤ 1 := by simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hqE1
  let a₀ := s*Real.log (1+α)/8
  let b := Real.log (1+α)+a₀
  have halog : 0 < Real.log (1+α) := Real.log_pos (by linarith)
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let u := (-Real.log q)/a₀
  have hu : 0 ≤ u := div_nonneg (neg_nonneg.mpr (Real.log_nonpos hq.le hq1)) ha₀.le
  let D := 1+|Real.log c|+u*(|Real.log C|+b)
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < 1+(1-Real.exp (-s/4))⁻¹ := by
    have he : Real.exp (-s/4)<1 := Real.exp_lt_one_iff.mpr (by linarith)
    positivity
  refine ⟨u+1,D,1+(1-Real.exp (-s/4))⁻¹,by linarith,hD,hB,?_⟩
  intro a x hx
  obtain ⟨W,hW,hW0,hWi,hWB,hcount⟩ := hdata a x hx
  refine ⟨W,hW,hW0,hWi,hWB,?_⟩
  filter_upwards [hκae,hcount] with ω hκω hω
  intro t
  let ε := 1-Real.exp (-a₀)
  have hε0 : 0 ≤ ε := (buffer_contraction_choice hα hs).1.le
  have hε1 : ε ≤ 1 := (buffer_contraction_choice hα hs).2.1.le
  obtain ⟨n,hnt,hret⟩ := buffer_all_height_retention e f hef (zero_le_one.trans hR) a ε α g
    hκ hκ1 hg hg1 hε0 hε1 hα.le (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) x hx ω hκω t
  let pE := rawPairEndpointLaw (realPosition (step e)) (t+1) ω x
    {y | signedCoordinate f (x.2-x.1) ≤ signedCoordinate f (y.2-y.1)}
  have hpE1 : pE ≤ 1 := (measure_mono (Set.subset_univ _)).trans (rawPairEndpointLaw_total_le_one _ _ _ _)
  have hpEt : pE ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hpE1
  have hreal := ENNReal.toReal_mono hpEt hret
  have hcp : c*q^n ≤ outwardKernelMass e f (t+1) x ω := by
    simpa only [outwardKernelMass,c,q,cE,qE,ENNReal.toReal_mul,ENNReal.toReal_pow,
      mul_assoc,mul_left_comm,mul_comm] using hreal
  have hp : 0 < outwardKernelMass e f (t+1) x ω := (mul_pos hc (pow_pos hq n)).trans_le hcp
  have hn : a₀*(n:ℝ) ≤ Real.log C+Real.log ((t:ℝ)+2)+b*W ω := by
    have hh := hω n
    have hhlog := Real.log_le_log (show 0 < (bufferWordHeight (bufferHistory e f hef R
      (signedCoordinate f (x.2-x.1)) ε α g κ (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f)
      (bufferRootNode e f hef R a x hx) ω n):ℝ)+1 by positivity)
      (show (bufferWordHeight (bufferHistory e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
      (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) (bufferRootNode e f hef R a x hx) ω n):ℝ)+1 ≤ (t:ℝ)+2 by
        have ht : (bufferWordHeight (bufferHistory e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
          (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) (bufferRootNode e f hef R a x hx) ω n):ℝ) ≤ t := by exact_mod_cast hnt
        linarith)
    change a₀*(n:ℝ) ≤ Real.log C+_+W ω*b at hh
    linarith
  have hlog := logarithmic_retention_bound hc hq hq1 ha₀ hb (hW0 ω) n t hcp hn
  have htlog : 0 ≤ Real.log ((t:ℝ)+2) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) t; linarith)
  refine ⟨hp,hlog.trans ?_⟩
  change u*Real.log ((t:ℝ)+2)+D*(W ω+1) ≤ (u+1)*Real.log ((t:ℝ)+2)+D*(W ω+1)
  nlinarith
end DirectionalTransience

end

end

end OAI
