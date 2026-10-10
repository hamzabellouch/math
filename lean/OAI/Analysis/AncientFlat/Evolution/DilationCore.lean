import Mathlib

namespace OAI
noncomputable section
open Set Filter
open scoped Topology ZeroAtInfty BoundedContinuousFunction
namespace ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def dilHomeo (t : ℝ) : V ≃ₜ V := Homeomorph.smulOfNeZero (Real.exp (-t/4)) (Real.exp_ne_zero _)
@[simp] lemma dilHomeo_apply (t : ℝ) (x : V) : dilHomeo t x=Real.exp (-t/4) • x := rfl

def dilMap (t : ℝ) : C(V,V) := ⟨dilHomeo t,(dilHomeo t).continuous⟩

def dil (t : ℝ) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
  (ZeroAtInftyContinuousMap.compLinearMap (R := ℂ) (dilHomeo (V := V) t).toCocompactMap).mkContinuous 1
    (fun f => by
      change ‖f.toBCF.compContinuous (dilMap (V := V) t)‖≤1*‖f.toBCF‖
      simpa only [one_mul] using f.toBCF.norm_compContinuous_le (dilMap (V := V) t))
@[simp] lemma dil_apply (t : ℝ) (f : C₀(V,ℂ)) (x : V) :
    dil t f x=f (Real.exp (-t/4) • x) := rfl
lemma norm_dil_le (t : ℝ) (f : C₀(V,ℂ)) : ‖dil t f‖≤‖f‖ := by
  change ‖f.toBCF.compContinuous (dilMap (V := V) t)‖≤‖f.toBCF‖
  exact f.toBCF.norm_compContinuous_le _
lemma opNorm_dil_le (t : ℝ) : ‖dil (V := V) t‖≤1 := by
  let : NormedAddCommGroup C₀(V,ℂ) := inferInstance
  let : NormedSpace ℂ C₀(V,ℂ) := inferInstance
  apply (dil (V := V) t).opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using norm_dil_le t f
@[simp] lemma dil_zero : dil (V := V) 0=ContinuousLinearMap.id ℂ C₀(V,ℂ) := by
  ext f x
  simp
lemma dil_add (s t : ℝ) : dil (V := V) (s+t)=(dil s).comp (dil t) := by
  ext f x
  simp only [dil_apply,ContinuousLinearMap.comp_apply]
  rw [smul_smul,←Real.exp_add]
  congr 3
  ring
lemma dil_comm (s t : ℝ) (f : C₀(V,ℂ)) : dil s (dil t f)=dil t (dil s f) := by
  rw [←ContinuousLinearMap.comp_apply,←dil_add,add_comm, dil_add]
  rfl
lemma norm_dil (t : ℝ) (f : C₀(V,ℂ)) : ‖dil t f‖=‖f‖ := by
  apply le_antisymm (norm_dil_le t f)
  calc
    ‖f‖=‖dil (-t) (dil t f)‖ := by rw [←ContinuousLinearMap.comp_apply,←dil_add]; simp
    _≤‖dil t f‖ := norm_dil_le _ _

lemma tends_dil_zero (f : C₀(V,ℂ)) : Tendsto (fun t : ℝ => dil t f) (𝓝 0) (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R,hR⟩ := Metric.closedBall_compl_subset_of_mem_cocompact
    ((zero_at_infty f).eventually (Metric.ball_mem_nhds (0:ℂ) (by linarith : 0<ε/4))) (0:V)
  let M : ℝ := max R 1
  have hM : 0<M := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  obtain ⟨δ,hδ,huniform⟩ := Metric.uniformContinuous_iff.mp (ZeroAtInftyContinuousMap.uniformContinuous f) (ε/2) (by linarith)
  have hexp : Tendsto (fun t : ℝ => Real.exp (-t/4)) (𝓝 0) (𝓝 1) := by
    convert (Real.continuous_exp.comp (continuous_neg.div_const 4)).tendsto (0:ℝ) using 1 <;> first | rfl | simp
  have hevent := hexp.eventually (Metric.ball_mem_nhds (1:ℝ)
    (lt_min (by norm_num : (0:ℝ)<1/2) (div_pos hδ (by positivity : 0<2*M+1))))
  filter_upwards [hevent] with t ht
  have hc : |Real.exp (-t/4)-1|< min (1/2) (δ/(2*M+1)) := by simpa only [Metric.mem_ball,Real.dist_eq] using ht
  have hc1 : (1:ℝ)/2<Real.exp (-t/4) := by
    have := (abs_lt.mp (lt_of_lt_of_le hc (min_le_left _ _))).1
    linarith
  have hcδ : |Real.exp (-t/4)-1| *(2*M)<δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*M+1)).mp (lt_of_lt_of_le hc (min_le_right _ _))
    nlinarith [abs_nonneg (Real.exp (-t/4)-1)]
  have hb : dist (dil t f) f≤ε/2 := by
    change dist (dil t f).toBCF f.toBCF≤ε/2
    apply (BoundedContinuousFunction.dist_le (by linarith)).mpr
    intro x
    change dist (f (Real.exp (-t/4) • x)) (f x)≤ε/2
    by_cases hx : ‖x‖≤2*M
    · apply (huniform _).le
      calc
        dist (Real.exp (-t/4) • x) x=|Real.exp (-t/4)-1| *‖x‖ := by
          rw [dist_eq_norm,show Real.exp (-t/4) • x-x=(Real.exp (-t/4)-1) • x by rw [sub_smul,one_smul],norm_smul,Real.norm_eq_abs]
        _≤|Real.exp (-t/4)-1| *(2*M) := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
        _<δ := hcδ
    · have hx' : R<‖x‖ := lt_of_le_of_lt (le_max_left R 1) (by linarith : M<‖x‖)
      have hy' : R<‖Real.exp (-t/4) • x‖ := by
        rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
        have := le_max_left R 1
        nlinarith [norm_nonneg x]
      have hfx : ‖f x‖<ε/4 := by
        simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hR (by simpa only [mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le] using hx')
      have hfy : ‖f (Real.exp (-t/4) • x)‖<ε/4 := by
        simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hR (by simpa only [mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le] using hy')
      calc
        dist (f (Real.exp (-t/4) • x)) (f x)≤‖f (Real.exp (-t/4) • x)‖+‖f x‖ := dist_le_norm_add_norm _ _
        _≤ε/2 := by linarith
  exact lt_of_le_of_lt hb (by linarith)

lemma continuous_dil (f : C₀(V,ℂ)) : Continuous (fun t : ℝ => dil t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht : Tendsto (fun r : ℝ => r-t) (𝓝 t) (𝓝 0) := by
    convert ((continuous_id.sub continuous_const).tendsto t : Tendsto (fun r : ℝ => r-t) (𝓝 t) (𝓝 (t-t))) using 1 <;> first | rfl | simp
  have h := (tends_dil_zero (dil t f)).comp ht
  change Tendsto (fun r => dil r f) (𝓝 t) (𝓝 (dil t f))
  convert h using 1
  ext r x
  change dil r f x=dil (r-t) (dil t f) x
  rw [←ContinuousLinearMap.comp_apply,←dil_add,sub_add_cancel]
end ParametrixDilation

end

end OAI
