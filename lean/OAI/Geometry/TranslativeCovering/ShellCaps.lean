import OAI.Geometry.TranslativeCovering.RadialCost

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

namespace ShellCaps
open Set MeasureTheory SphericalLaw CapCost
open scoped BigOperators
noncomputable def A (l u : ℝ) : ℝ := 1/l+1/(1-u^2)
noncomputable def C (a l u : ℝ) : ℝ := Real.log 2+8*A l u/a

lemma A_pos {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1) : 0 < A l u := by
  have hu0 : 0 < u := hl.trans_le hlu
  have hsq : 0 < 1-u^2 := by nlinarith only [hu0,hu]
  unfold A
  positivity

lemma C_pos {a l u : ℝ} (ha : 0 < a) (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1) : 0 < C a l u := by
  have hA := A_pos hl hlu hu
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold C
  positivity

lemma shell_cost {a l u : ℝ} (ha : 1 ≤ a) (hl : 0 < l) (hlt : l < 1/a)
    (hu : 1/a < u) (hu1 : u < 1) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n],
    ∀ (e f : Sphere n) (r : ℝ),RadialShell.low a n ≤ r → r ≤ RadialShell.high a n →
    let μ := intensity e (1/a)
    let E := cap f.val ((1+3*RadialShell.η n)/r)
    l ≤ (1+3*RadialShell.η n)/r ∧ (1+3*RadialShell.η n)/r ≤ u ∧
    μ.real E ≤ Real.exp (8*A l u) ∧
    -Real.log (min (μ.real E) (1/2)) ≤ C a l u*RadialCost.weight n a r ∧
    -Real.log (min (μ.real E) (1/2)) ≤ (27*C a l u)*Real.log n ∧
    Real.exp (-(27*C a l u)*Real.log n) ≤ min (μ.real E) (1/2) := by
  have hap : 0 < a := by linarith only [ha]
  have hA : 0 < A l u := A_pos hl (hlt.le.trans hu.le) hu1
  have hC : 0 < C a l u := C_pos hap hl (hlt.le.trans hu.le) hu1
  obtain ⟨n₀,hn₀⟩ := RadialShell.thresholds hap hlt hu
  refine ⟨n₀,?_⟩
  intro n hn _ e f r hlo hhi
  obtain ⟨hn2,hlog,hlow,hnη,hτ⟩ := hn₀ n hn
  obtain ⟨hτl,hτu⟩ := hτ r hlo hhi
  have hr : a/2 ≤ r := hlow.trans hlo
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith only [hap]) hr
  have hη : 0 ≤ RadialShell.η n := by unfold RadialShell.η; positivity
  have htlo := RadialCost.lower_threshold (by omega : 0 < n) ha hr hη hnη (by simpa [RadialShell.high,one_div] using hhi)
  have hthi := RadialCost.upper_threshold ha hr hη hnη
  let μ := intensity e (1/a)
  let E := cap f.val ((1+3*RadialShell.η n)/r)
  have hraw : μ.real E ≤ Real.exp (8*A l u) := by
    apply (raw_upper e f hl hu1 hlt.le hu.le hτl hτu).trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left htlo hA.le
    dsimp [A] at hh ⊢
    nlinarith only [hh]
  have hcost : -Real.log (min (μ.real E) (1/2)) ≤ C a l u*RadialCost.weight n a r := by
    have hc := clipped_cost e f hl hu1 hlt.le hu.le hτl hτu
    have hh := mul_le_mul_of_nonneg_left hthi hA.le
    have hw := mul_le_mul_of_nonneg_left (RadialCost.weight_ge_one n a r)
      (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    dsimp [C,A] at hh ⊢
    dsimp [μ,E]
    linear_combination hc+hh+hw
  have hcost' : -Real.log (min (μ.real E) (1/2)) ≤ (27*C a l u)*Real.log n := by
    have hw := mul_le_mul_of_nonneg_left (RadialShell.weight_upper ha hlog hr0.le hlo hnη) hC.le
    apply hcost.trans
    dsimp [RadialCost.weight]
    nlinarith only [hw]
  have hpos : 0 < min (μ.real E) (1/2) := by
    apply lt_min _ (by norm_num)
    rw [show μ.real E = (σ n).real E/(σ n).real (cap e.val (1/a)) from intensity_real e _ _]
    exact div_pos (cap_real_pos f (hτu.trans_lt hu1)) (cap_real_pos e (hu.trans hu1))
  refine ⟨hτl,hτu,hraw,hcost,hcost',?_⟩
  calc
    _ ≤ Real.exp (Real.log (min (μ.real E) (1/2))) := Real.exp_le_exp.mpr (by linarith only [hcost'])
    _ = _ := Real.exp_log hpos

end ShellCaps

end OAI
