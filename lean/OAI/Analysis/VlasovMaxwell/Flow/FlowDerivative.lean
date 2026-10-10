import Mathlib
import OAI.Analysis.VlasovMaxwell.Maxwell.Variational

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal

namespace RVM
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

lemma hasFDerivAt_variational_flow {f : E → E} (hf : ContDiff ℝ 2 f)
    {x₀ : E} {r R ε : ℝ} (hε : 0 < ε)
    {α : E → ℝ → E} {A : E → ℝ → (E →L[ℝ] E)} {L : ℝ≥0}
    (hsol : ∀ x ∈ Metric.closedBall x₀ r, α x 0 = x ∧ A x 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (α x) (f (α x t)) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (A x)
        ((fderiv ℝ f (α x t)).comp (A x t)) (Icc (-ε) ε) t) ∧
      ∀ t, α x t ∈ Metric.closedBall x₀ R)
    (hLip : ∀ t ∈ Icc (-ε) ε, LipschitzOnWith L (α · t) (Metric.closedBall x₀ r))
    {x : E} (hx : x ∈ Metric.ball x₀ r) {t : ℝ} (ht : t ∈ Icc 0 ε) :
    HasFDerivAt (fun y => α y t) (A x t) x := by
  have hx' := Metric.ball_subset_closedBall hx
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨LD,hLD⟩ := hdf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall x₀ R) (isCompact_closedBall x₀ R)
  obtain ⟨M,hM⟩ := (isCompact_closedBall x₀ R).bddAbove_image hdf.continuous.norm.continuousOn
  let K := max 1 M
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let C : ℝ := ((LD : ℝ)*(L : ℝ)^2)/K * (Real.exp (K*t)-1)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (div_nonneg (mul_nonneg LD.2 (sq_nonneg _)) hK.le)
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hK.le ht.1)))
  apply hasFDerivAt_of_quadratic_bound hC
  filter_upwards [Metric.closedBall_mem_nhds_of_mem hx] with y hy
  have hsub : Icc 0 ε ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) le_rfl
  have hxs := hsol x hx'
  have hys := hsol y hy
  have hdα (z : E) (hz : z ∈ Metric.closedBall x₀ r) (s : ℝ) (hs : s ∈ Ico 0 ε) :
      HasDerivWithinAt (α z) (f (α z s)) (Ici s) s := by
    exact ((hsol z hz).2.2.1 s (hsub ⟨hs.1,hs.2.le⟩)).hasDerivAt
      (Icc_mem_nhds (by linarith [hs.1]) hs.2) |>.hasDerivWithinAt
  have hdA (s : ℝ) (hs : s ∈ Ico 0 ε) :
      HasDerivWithinAt (A x) ((fderiv ℝ f (α x s)).comp (A x s)) (Ici s) s := by
    exact (hxs.2.2.2.1 s (hsub ⟨hs.1,hs.2.le⟩)).hasDerivAt
      (Icc_mem_nhds (by linarith [hs.1]) hs.2) |>.hasDerivWithinAt
  have hb := variational_remainder_bound
    ((HasDerivWithinAt.continuousOn hxs.2.2.1).mono hsub)
    ((HasDerivWithinAt.continuousOn hys.2.2.1).mono hsub)
    ((HasDerivWithinAt.continuousOn hxs.2.2.2.1).mono hsub)
    (hdα x hx') (hdα y hy) hdA
    (v := y-x) (K := K) (ε := (LD : ℝ)*(L : ℝ)^2*‖y-x‖^2)
    (by simp [hxs.1,hys.1,hxs.2.1])
    (fun s _ => (hM ⟨α x s,hxs.2.2.2.2 s,rfl⟩).trans (le_max_right _ _))
    (fun s hs => ?_)
  · have hb' := hb t ht
    apply hb'.trans_eq
    rw [gronwallBound_of_K_ne_0 hK.ne']
    dsimp [C]
    ring_nf
  · have hTaylor := taylor_bound_lipschitz_derivative
      (convex_closedBall x₀ R) (fun z _ => (hf.differentiable (by norm_num)) z)
      hLD (hxs.2.2.2.2 s) (hys.2.2.2.2 s)
    apply hTaylor.trans
    have hn := (hLip s (hsub ⟨hs.1,hs.2.le⟩)).norm_sub_le hy hx'
    have hsq : ‖α y s-α x s‖^2 ≤ ((L : ℝ)*‖y-x‖)^2 :=
      sq_le_sq₀ (norm_nonneg _) (mul_nonneg L.2 (norm_nonneg _)) |>.mpr hn
    calc
      _ ≤ (LD : ℝ)*((L : ℝ)*‖y-x‖)^2 := mul_le_mul_of_nonneg_left hsq LD.2
      _ = _ := by ring

lemma exists_local_differentiable_flow {f : E → E} (hf : ContDiff ℝ 2 f) (x₀ : E) :
    ∃ ε > (0 : ℝ), ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E),
      (∀ x ∈ Metric.ball x₀ (1/2 : ℝ), α x 0 = x ∧ A x 0 = ContinuousLinearMap.id ℝ E ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (α x) (f (α x t)) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (A x)
          ((fderiv ℝ f (α x t)).comp (A x t)) (Icc (-ε) ε) t) ∧
        ∀ t ∈ Icc 0 ε, HasFDerivAt (fun y => α y t) (A x t) x) := by
  obtain ⟨ε,hε,α,A,L,hsol,hLip⟩ := exists_local_variational_flow hf x₀
  refine ⟨ε,hε,α,A,?_⟩
  intro x hx
  have h := hsol x (Metric.ball_subset_closedBall hx)
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,
    fun t ht => hasFDerivAt_variational_flow hf hε hsol hLip hx ht⟩
end RVM

open Set MeasureTheory

namespace RVM

def determinantMultilinear (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

lemma determinant_derivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => (A s).det)
      (∑ i, ((A t).updateRow i (A' i)).det) t := by
  have h := ((determinantMultilinear ι).hasFDerivAt (A t)).comp_hasDerivAt t hA
  have hd : ((determinantMultilinear ι).linearDeriv (A t)) A' =
      ∑ i, ((A t).updateRow i (A' i)).det := by
    erw [ContinuousMultilinearMap.linearDeriv_apply]
    rfl
  rw [hd] at h
  exact h

lemma determinant_row_mul_derivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : Matrix ι ι ℝ) :
    (∑ i, (A.updateRow i ((C*A) i)).det) = C.trace * A.det := by
  have hrow (i : ι) : (C*A) i = ∑ j, C i j • A j := by
    ext k
    simp [Matrix.mul_apply,Finset.sum_apply]
  simp_rw [hrow,Matrix.det_updateRow_sum,smul_eq_mul]
  rw [← Finset.sum_mul]
  rfl

lemma determinant_variational_derivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} {C : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A (C*A t) t) :
    HasDerivAt (fun s => (A s).det) (C.trace*(A t).det) t := by
  simpa only [determinant_row_mul_derivative] using determinant_derivative hA

lemma determinant_eq_one_of_trace_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A C : ℝ → Matrix ι ι ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hinit : A a = 1)
    (hder : ∀ t ∈ Ioo a b, HasDerivAt A (C t*A t) t)
    (htrace : ∀ t ∈ Ioo a b, (C t).trace = 0) :
    ∀ t ∈ Icc a b, (A t).det = 1 := by
  have hcont : ContinuousOn (fun t => (A t).det) (Icc a b) :=
    continuous_id.matrix_det.comp_continuousOn hA
  have hz : ∀ t ∈ Ioo a b, HasDerivAt (fun s => (A s).det) 0 t := by
    intro t ht
    simpa [htrace t ht] using determinant_variational_derivative (hder t ht)
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    intro t ht
    have : t = a := le_antisymm ht.2 ht.1
    simp [this,hinit]
  obtain ⟨c,hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo a b).isPreconnected
    (fun x hx => (hz x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hz x hx).deriv)
  have heq : EqOn (fun t => (A t).det) (fun _ => c) (Icc a b) := by
    rw [← closure_Ioo hlt.ne] at hcont ⊢
    exact Set.EqOn.of_subset_closure hc hcont continuousOn_const subset_closure Subset.rfl
  have ha := heq (left_mem_Icc.mpr hab)
  have hc1 : c = 1 := by simpa [hinit] using ha.symm
  intro t ht
  exact (heq ht).trans hc1

lemma determinant_retarded_rank_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U N : ι → ℝ) :
    (1 - Matrix.replicateCol Unit U * Matrix.replicateRow Unit N).det =
      1 - ∑ i, N i * U i := by
  have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) (-U) N
  have hn : Matrix.replicateCol Unit (-U) = - Matrix.replicateCol Unit U := by
    ext i j
    rfl
  simpa [hn,Matrix.neg_mul,sub_eq_add_neg,dotProduct,
    mul_neg,Finset.sum_neg_distrib] using h

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open Set MeasureTheory

namespace RVM
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

def endomorphismMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) : (E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ :=
  ((LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

lemma endomorphismMatrix_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E) :
    endomorphismMatrix b A = LinearMap.toMatrix b b A.toLinearMap := rfl

lemma endomorphismMatrix_comp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (A C : E →L[ℝ] E) :
    endomorphismMatrix b (C.comp A) = endomorphismMatrix b C * endomorphismMatrix b A := by
  exact LinearMap.toMatrix_comp b b b _ _

lemma hasDerivAt_endomorphismMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {A : ℝ → E →L[ℝ] E} {D : E →L[ℝ] E} {t : ℝ}
    (hA : HasDerivAt A D t) :
    HasDerivAt (fun s => endomorphismMatrix b (A s)) (endomorphismMatrix b D) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hd : HasDerivAt (fun s => A s (b j)) (D (b j)) t := by
    simpa using hA.clm_apply (hasDerivAt_const t (b j))
  have hh := (b.coord i).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hd
  simpa only [Function.comp_def,endomorphismMatrix_apply,LinearMap.toMatrix_apply,
    LinearMap.coe_toContinuousLinearMap',Module.Basis.coord_apply,ContinuousLinearMap.coe_coe] using hh

lemma determinant_clm_variational_derivative {A : ℝ → E →L[ℝ] E}
    {C : E →L[ℝ] E} {t : ℝ} (hA : HasDerivAt A (C.comp (A t)) t) :
    HasDerivAt (fun s => (A s).det)
      (LinearMap.trace ℝ E C.toLinearMap * (A t).det) t := by
  let b := Module.finBasis ℝ E
  have hd := hasDerivAt_endomorphismMatrix b hA
  have hd' : HasDerivAt (fun s => endomorphismMatrix b (A s))
      (endomorphismMatrix b C * endomorphismMatrix b (A t)) t := by
    simpa only [endomorphismMatrix_comp] using hd
  have h := determinant_variational_derivative hd'
  simpa only [Function.comp_def,endomorphismMatrix_apply,LinearMap.det_toMatrix,
    ← LinearMap.trace_eq_matrix_trace ℝ b] using h

lemma determinant_clm_eq_one_of_trace_zero
    {A C : ℝ → E →L[ℝ] E} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hinit : A a = ContinuousLinearMap.id ℝ E)
    (hder : ∀ t ∈ Ioo a b, HasDerivAt A ((C t).comp (A t)) t)
    (htrace : ∀ t ∈ Ioo a b, LinearMap.trace ℝ E (C t).toLinearMap = 0) :
    ∀ t ∈ Icc a b, (A t).det = 1 := by
  let e := Module.finBasis ℝ E
  have h := determinant_eq_one_of_trace_zero hab
    ((endomorphismMatrix e).continuous.comp_continuousOn hA)
    (show endomorphismMatrix e (A a) = 1 by
      rw [hinit,endomorphismMatrix_apply]
      exact LinearMap.toMatrix_id _)
    (A := fun t => endomorphismMatrix e (A t))
    (C := fun t => endomorphismMatrix e (C t))
    (fun t ht => by
      have hh := hasDerivAt_endomorphismMatrix e (hder t ht)
      simpa only [endomorphismMatrix_comp] using hh)
    (fun t ht => by
      rw [endomorphismMatrix_apply,← LinearMap.trace_eq_matrix_trace ℝ e]
      exact htrace t ht)
  simpa only [endomorphismMatrix_apply,LinearMap.det_toMatrix] using h

lemma flow_injOn_of_local_ode {f : E → E} (hf : ContDiff ℝ 1 f)
    {x₀ : E} {r R ε : ℝ} (hε : 0 < ε) {α : E → ℝ → E}
    (hinit : ∀ x ∈ Metric.closedBall x₀ r, α x 0 = x)
    (hder : ∀ x ∈ Metric.closedBall x₀ r, ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α x) (f (α x t)) (Icc (-ε) ε) t)
    (hrange : ∀ x ∈ Metric.closedBall x₀ r, ∀ t, α x t ∈ Metric.closedBall x₀ R)
    {t : ℝ} (ht : t ∈ Ico 0 ε) : Set.InjOn (fun x => α x t) (Metric.closedBall x₀ r) := by
  obtain ⟨K,hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall x₀ R) (isCompact_closedBall x₀ R)
  have hsub : Icc 0 t ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) ht.2.le
  have hd (x : E) (hx : x ∈ Metric.closedBall x₀ r) (s : ℝ) (hs : s ∈ Ioc 0 t) :
      HasDerivWithinAt (α x) (f (α x s)) (Iic s) s := by
    exact ((hder x hx s (hsub ⟨hs.1.le,hs.2⟩)).hasDerivAt
      (Icc_mem_nhds (by linarith [hs.1]) (lt_of_le_of_lt hs.2 ht.2))).hasDerivWithinAt
  intro x hx y hy heq
  have hu := ODE_solution_unique_of_mem_Icc_left
    (v := fun _ => f) (s := fun _ => Metric.closedBall x₀ R)
    (fun _ _ => hK)
    ((HasDerivWithinAt.continuousOn (hder x hx)).mono hsub) (hd x hx)
    (fun s _ => hrange x hx s)
    ((HasDerivWithinAt.continuousOn (hder y hy)).mono hsub) (hd y hy)
    (fun s _ => hrange y hy s) heq
  simpa only [hinit x hx,hinit y hy] using hu (left_mem_Icc.mpr ht.1)

lemma exists_local_volume_flow {f : E → E} (hf : ContDiff ℝ 2 f)
    (hdiv : ∀ x, LinearMap.trace ℝ E (fderiv ℝ f x).toLinearMap = 0) (x₀ : E) :
    ∃ η > (0 : ℝ), ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E),
      (∀ x ∈ Metric.ball x₀ (1/2 : ℝ), α x 0 = x ∧
        (∀ t ∈ Icc 0 η, HasDerivAt (α x) (f (α x t)) t) ∧
        (∀ t ∈ Icc 0 η, HasFDerivAt (fun y => α y t) (A x t) x) ∧
        ∀ t ∈ Icc 0 η, (A x t).det = 1) ∧
      ∀ t ∈ Icc 0 η, Set.InjOn (fun x => α x t) (Metric.ball x₀ (1/2 : ℝ)) := by
  obtain ⟨ε,hε,α,A,L,hsol,hLip⟩ := exists_local_variational_flow hf x₀
  have hsub : Icc 0 (ε/2) ⊆ Icc 0 ε := Icc_subset_Icc_right (by linarith)
  refine ⟨ε/2,by linarith,α,A,?_,?_⟩
  · intro x hx
    have hx' := Metric.ball_subset_closedBall hx
    have hs := hsol x hx'
    have hdet := determinant_clm_eq_one_of_trace_zero hε.le
      ((HasDerivWithinAt.continuousOn hs.2.2.2.1).mono
        (Icc_subset_Icc_left (by linarith : -ε ≤ 0))) hs.2.1
      (fun t ht => (hs.2.2.2.1 t ⟨by linarith [ht.1],ht.2.le⟩).hasDerivAt
        (Icc_mem_nhds (by linarith [ht.1]) ht.2)) (fun t _ => hdiv (α x t))
    refine ⟨hs.1,?_,?_,fun t ht => hdet t (hsub ht)⟩
    · intro t ht
      exact (hs.2.2.1 t ⟨by linarith [ht.1],(hsub ht).2⟩).hasDerivAt
        (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
    · intro t ht
      exact hasFDerivAt_variational_flow hf hε hsol hLip hx (hsub ht)
  · intro t ht
    exact (flow_injOn_of_local_ode (hf.of_le (by norm_num)) hε
      (fun x hx => (hsol x hx).1) (fun x hx => (hsol x hx).2.2.1)
      (fun x hx => (hsol x hx).2.2.2.2) ⟨ht.1,by linarith [ht.2]⟩).mono
        Metric.ball_subset_closedBall

lemma integral_image_volume_flow [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} {α : E → E} {A : E → E →L[ℝ] E}
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, HasFDerivAt α (A x) x)
    (hi : Set.InjOn α s) (hdet : ∀ x ∈ s, (A x).det = 1)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) :
    ∫ y in α '' s, g y ∂μ = ∫ x in s, g (α x) ∂μ := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul μ hs
    (fun x hx => (hd x hx).hasFDerivWithinAt) hi]
  apply setIntegral_congr_fun hs
  intro x hx
  simp [hdet x hx]

lemma lintegral_image_volume_flow [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} {α : E → E} {A : E → E →L[ℝ] E}
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, HasFDerivAt α (A x) x)
    (hi : Set.InjOn α s) (hdet : ∀ x ∈ s, (A x).det = 1) (g : E → ENNReal) :
    ∫⁻ y in α '' s, g y ∂μ = ∫⁻ x in s, g (α x) ∂μ := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs
    (fun x hx => (hd x hx).hasFDerivWithinAt) hi]
  apply setLIntegral_congr_fun hs
  intro x hx
  simp [hdet x hx]

end RVM

end

end OAI
