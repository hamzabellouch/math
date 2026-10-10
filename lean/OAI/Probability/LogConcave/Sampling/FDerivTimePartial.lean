import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open Set Filter Metric Function
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hasFDerivAt_of_time_partial {f g : ℝ → E → F} {s : Set (ℝ × E)}
    (hs : IsOpen s) {t : ℝ} {x : E} (hp : (t,x)∈s)
    (hg : ContinuousAt (uncurry g) (t,x))
    (ht : ∀ p∈s,HasDerivAt (fun u => f u p.2) (g p.1 p.2) p.1)
    {D : E →L[ℝ] F} (hx : HasFDerivAt (f t) D x) :
    HasFDerivAt (uncurry f)
      (((ContinuousLinearMap.fst ℝ ℝ E).smulRight (g t x))+
        D.comp (ContinuousLinearMap.snd ℝ ℝ E)) (t,x) := by
  apply HasFDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hgε : ∀ᶠ q in 𝓝 (t,x),q∈s ∧ ‖g q.1 q.2-g t x‖<ε/2 := by
    filter_upwards [hs.mem_nhds hp,(Metric.tendsto_nhds.mp hg) (ε/2) (by positivity)] with q hq hq'
    exact ⟨hq,by simpa [dist_eq_norm,Function.uncurry] using hq'⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hgε
  have hxε := (Asymptotics.isLittleO_iff.mp hx.isLittleO) (by positivity : 0<ε/2)
  filter_upwards [Metric.ball_mem_nhds (t,x) hδ,
    (continuous_snd.tendsto (t,x)) hxε] with q hq hqx
  have hqt : |q.1-t|<δ := lt_of_le_of_lt (le_max_left _ _) (by
    simpa [mem_ball,dist_eq_norm,Prod.norm_def,Real.norm_eq_abs] using hq)
  have hqxδ : ‖q.2-x‖<δ := lt_of_le_of_lt (le_max_right _ _) (by
    simpa [mem_ball,dist_eq_norm,Prod.norm_def,Real.norm_eq_abs] using hq)
  have hc (u : ℝ) (hu : u∈closedBall t |q.1-t|) :
      (u,q.2)∈s ∧ ‖g u q.2-g t x‖<ε/2 := by
    apply hball
    have hu' : |u-t|≤|q.1-t| := by simpa [mem_closedBall,dist_eq_norm,Real.norm_eq_abs] using hu
    simpa [mem_ball,dist_eq_norm,Prod.norm_def,Real.norm_eq_abs] using
      (max_lt (hu'.trans_lt hqt) hqxδ)
  have hd (u : ℝ) (hu : u∈closedBall t |q.1-t|) :
      HasFDerivWithinAt (fun v => f v q.2-v •g t x)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (g u q.2-g t x))
        (closedBall t |q.1-t|) u := by
    convert! ((ht (u,q.2) (hc u hu).1).sub
      ((hasDerivAt_id u).smul_const (g t x))).hasFDerivAt.hasFDerivWithinAt using 1
    ext
    simp
  have htime := (convex_closedBall t |q.1-t|).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd (fun u hu => by simpa using (hc u hu).2.le)
    (mem_closedBall_self (abs_nonneg _))
    (show q.1∈closedBall t |q.1-t| by simp [mem_closedBall,dist_eq_norm,Real.norm_eq_abs])
  have htime' : ‖f q.1 q.2-f t q.2-(q.1-t) •g t x‖≤(ε/2)*|q.1-t| := by
    have he : f q.1 q.2-f t q.2-(q.1-t) •g t x=
        f q.1 q.2-q.1 •g t x-(f t q.2-t •g t x) := by rw [sub_smul]; abel
    simpa only [he,Real.norm_eq_abs] using htime
  have he : f q.1 q.2-f t x-((q.1-t) •g t x+D (q.2-x))=
      (f q.1 q.2-f t q.2-(q.1-t) •g t x)+(f t q.2-f t x-D (q.2-x)) := by abel
  change ‖f q.1 q.2-f t x-((q.1-t) •g t x+D (q.2-x))‖≤ε*‖q-(t,x)‖
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add htime' hqx).trans
  change ε/2*|q.1-t|+ε/2*‖q.2-x‖≤ε*max |q.1-t| ‖q.2-x‖
  have he0 : 0≤ε/2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (le_max_left |q.1-t| ‖q.2-x‖) he0,
    mul_le_mul_of_nonneg_left (le_max_right |q.1-t| ‖q.2-x‖) he0]
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
