import Mathlib
import OAI.Probability.SKGap.Terminal.TerminalMatrixMeasurable

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology

lemma terminalMatrixData_small_eventually {j ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,terminalEntryScale n ≤ 1 ∧
      terminalEntryScale n*(1+terminalRowBound j/3) ≤ 2*ε/3 := by
  have ht := terminalEntryScale_tendsto
  have ht' := ht.mul_const (1+terminalRowBound j/3)
  exact (ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1))).and
    (by simpa only [zero_mul] using ht'.eventually (ge_mem_nhds (by simpa only [zero_mul] using (show (0:ℝ) < 2*ε/3 by positivity) : (0:ℝ)*(1+terminalRowBound j/3) < 2*ε/3)))

lemma terminalMatrixData_actual_bad {β α ε l : ℝ} (hβ : 0 < β) (hα : 0 ≤ α)
    (hε : 0 < ε) (hl : 0 ≤ l) (hedge : 2*sqrt (β^2*α) ≤ ε/6) :
    ∀ᶠ n : ℕ in atTop,(disorderLaw β n).real {g | ¬ terminalMatrixData (terminalMatrixBound (β^2)) α ε g} ≤
      terminalRawTail (β^2) α ε n l := by
  have hn : ∀ᶠ n : ℕ in atTop,1 ≤ n := eventually_ge_atTop 1
  filter_upwards [terminalMatrixData_small_eventually (j:=β^2) hε,hn] with n hn hnpos
  let : NeZero n := ⟨by omega⟩
  have hm := (terminalMatrixData_measurable (n:=n) (terminalMatrixBound (β^2)) α ε).compl
  change MeasurableSet {g : Disorder n | ¬terminalMatrixData (terminalMatrixBound (β^2)) α ε g} at hm
  rw [← (goe_actual_disorder_hasLaw β n).measureReal_eq hm]
  apply (measureReal_mono (μ:=gaussianCoordinates (MatrixCoordinates (Fin n))) ?_ (measure_ne_top _ _)).trans
    (terminalRaw_bad_bound (sq_pos_of_pos hβ) hα hε hl hedge)
  intro g hg hr
  exact hg (terminalMatrixData_of_raw (sq_pos_of_pos hβ) hε.le hn.1 hn.2 g hr)

lemma terminalMatrixData_actual_whp {β α ε l : ℝ} (hβ : 0 < β) (hα : 0 ≤ α)
    (hε : 0 < ε) (hl : 0 ≤ l) (hedge : 2*sqrt (β^2*α) ≤ ε/6)
    (h₅ : 0 < ε^2/(36*π^2*(β^2))-(l*α+log (1+exp (-l))))
    (h₆ : 0 < ε/(4*(β^2))-(l*α+log (1+exp (-l))+α*log 2)) :
    Tendsto (fun n : ℕ=>(disorderLaw β n).real {g | terminalMatrixData (terminalMatrixBound (β^2)) α ε g}) atTop (𝓝 1) := by
  have hb : Tendsto (fun n : ℕ=>(disorderLaw β n).real {g | ¬terminalMatrixData (terminalMatrixBound (β^2)) α ε g}) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _=>measureReal_nonneg))
      (terminalMatrixData_actual_bad hβ hα hε hl hedge) (terminalRawTail_tendsto (sq_pos_of_pos hβ) h₅ h₆)
  have he (n : ℕ) : (disorderLaw β n).real {g | terminalMatrixData (terminalMatrixBound (β^2)) α ε g}=
      1-(disorderLaw β n).real {g | ¬terminalMatrixData (terminalMatrixBound (β^2)) α ε g} := by
    have hm := terminalMatrixData_measurable (n:=n) (terminalMatrixBound (β^2)) α ε
    have h := measureReal_compl hm (μ:=disorderLaw β n)
    simp only [probReal_univ] at h
    change (disorderLaw β n).real {g | ¬terminalMatrixData (terminalMatrixBound (β^2)) α ε g}=1- _ at h
    linarith only [h]
  simp_rw [he]
  simpa only [sub_zero] using tendsto_const_nhds.sub hb
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Filter Real
open scoped Topology

lemma tendsto_cosh_real_atTop : Tendsto cosh atTop atTop := by
  have he : Tendsto (fun x : ℝ=>exp x/2) atTop atTop := by
    simpa only [div_eq_mul_inv,mul_comm,one_mul,id_eq] using tendsto_exp_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 1/2)
  apply tendsto_atTop_mono _ he
  intro x
  rw [cosh_eq]
  have hp := exp_pos (-x)
  linarith only [hp]

lemma terminalTime_exists {M α ε : ℝ} (_hM : 0 ≤ M) (hα : 0 < α)
    (hε : 400001*ε < 1/4) :
    ∃ T : ℝ,0 < T ∧ M^2 ≤ (T/4)^2*α/2 ∧
      400001*(ε+M*(2*sqrt (1/cosh (T/4)^2)+1/cosh (T/4)^2)) ≤ 1/4 ∧
      exp (-T/8)*(exp 1-1) ≤ α/4 := by
  have hT4 : Tendsto (fun T : ℝ=>T/4) atTop atTop := by
    simpa only [div_eq_mul_inv,mul_comm,one_mul,id_eq] using tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 1/4)
  have hs : Tendsto (fun T : ℝ=>1/cosh (T/4)^2) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.comp (tendsto_cosh_real_atTop.comp hT4)
    simpa only [Function.comp_apply,one_div,inv_pow,zero_pow (by decide : (2:ℕ) ≠ 0)] using h.pow 2
  have hsroot := hs.sqrt
  have hsfull : Tendsto (fun T : ℝ=>400001*(ε+M*(2*sqrt (1/cosh (T/4)^2)+1/cosh (T/4)^2))) atTop (𝓝 (400001*ε)) := by
    simpa only [sqrt_zero,mul_zero,add_zero] using (((hsroot.const_mul 2).add hs).const_mul M |>.const_add ε |>.const_mul 400001)
  have he : Tendsto (fun T : ℝ=>exp (-T/8)*(exp 1-1)) atTop (𝓝 0) := by
    have hT8 : Tendsto (fun T : ℝ=>T/8) atTop atTop := by
      simpa only [div_eq_mul_inv,mul_comm,one_mul,id_eq] using tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 1/8)
    simpa only [Function.comp_apply,neg_div,zero_mul] using (tendsto_exp_neg_atTop_nhds_zero.comp hT8).mul_const (exp 1-1)
  have ht : ∀ᶠ T : ℝ in atTop,4*sqrt (2*M^2/α)+1 ≤ T := eventually_ge_atTop _
  obtain ⟨T,⟨htT,htnum⟩,htp⟩ := (ht.and (hsfull.eventually (ge_mem_nhds hε))).and
    (he.eventually (ge_mem_nhds (by positivity : (0:ℝ) < α/4))) |>.exists
  refine ⟨T,?_,?_,htnum,htp⟩
  · have hr := sqrt_nonneg (2*M^2/α)
    linarith only [htT,hr]
  · have hr := sqrt_nonneg (2*M^2/α)
    have hsquare := sq_sqrt (by positivity : 0 ≤ 2*M^2/α)
    have hbound : 2*M^2/α ≤ (T/4)^2 := by nlinarith only [hr,hsquare,htT]
    have hmul := (div_le_iff₀ hα).mp hbound
    nlinarith only [hmul]
end SKGap

end
end

end OAI
