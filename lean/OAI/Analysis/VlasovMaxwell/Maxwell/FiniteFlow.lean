import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.FlowDerivative

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open scoped Topology NNReal ContDiff

namespace RVM
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_bounded_picard_flow {f : ℝ × E → E} {T L : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set E)))
    (hb : ∀ t ∈ Icc 0 T, ∀ z, ‖f (t,z)‖ ≤ L) (x₀ : E) :
    ∃ α : E → ℝ → E, ∃ K : ℝ≥0,
      (∀ x ∈ closedBall x₀ (1/2 : ℝ), α x 0 = x ∧
        ∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, LipschitzOnWith K (α · t) (closedBall x₀ (1/2 : ℝ)) := by
  let R : ℝ≥0 := ⟨L*T+1/2,by positivity⟩
  have hsub : Icc 0 T ×ˢ closedBall x₀ (R:ℝ) ⊆ Icc 0 T ×ˢ (univ : Set E) :=
    prod_mono_right (subset_univ _)
  obtain ⟨K,hK⟩ := (hf.mono hsub).exists_lipschitzOnWith (by norm_num)
    ((convex_Icc 0 T).prod (convex_closedBall x₀ (R:ℝ)))
    (isCompact_Icc.prod (isCompact_closedBall x₀ (R:ℝ)))
  have hpic : IsPicardLindelof (fun t z => f (t,z)) ⟨0,⟨le_rfl,hT⟩⟩
      x₀ R (1/2) ⟨L,hL⟩ K := by
    refine ⟨?_,?_,?_,?_⟩
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro z hz w hw
      simpa using hK.dist_le_mul (t,z) (show (t,z) ∈ Icc 0 T ×ˢ closedBall x₀ (R:ℝ) from ⟨ht,hz⟩)
        (t,w) (show (t,w) ∈ Icc 0 T ×ˢ closedBall x₀ (R:ℝ) from ⟨ht,hw⟩)
    · intro z _
      exact hf.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => ⟨ht,mem_univ z⟩)
    · intro t ht z _
      exact hb t ht z
    · change L * max (T-0) (0-0) ≤ (R:ℝ)-(1/2:ℝ≥0)
      simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,sub_zero,max_eq_left hT]
      change L*T ≤ L*T+1/2-1/2
      linarith
  obtain ⟨α,hα,K',hK'⟩ := picard_flow_with_range hpic
  refine ⟨α,K',?_,?_⟩
  · intro x hx
    exact ⟨(hα x (by simpa using hx)).1,(hα x (by simpa using hx)).2.1⟩
  · simpa using hK'

def cutVariationalField (f : E → E) (χ : (E →L[ℝ] E) → ℝ)
    (z : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (f z.1,χ z.2 • (fderiv ℝ f z.1).comp z.2)

omit [FiniteDimensional ℝ E] in
lemma contDiff_cutVariationalField {f : E → E} {χ : (E →L[ℝ] E) → ℝ}
    (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 1 χ) :
    ContDiff ℝ 1 (cutVariationalField f χ) := by
  exact ((hf.of_le (by norm_num)).comp contDiff_fst).prodMk
    ((hχ.comp contDiff_snd).smul
      (((hf.fderiv_right (by norm_num)).comp contDiff_fst).clm_comp contDiff_snd))

lemma cutVariationalField_bounded {f : E → E} {L K : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hb : ∀ x, ‖f x‖ ≤ L)
    (hd : ∀ x, ‖fderiv ℝ f x‖ ≤ K) (χ : ContDiffBump (0 : E →L[ℝ] E)) (z) :
    ‖cutVariationalField f χ z‖ ≤ max L (K*χ.rOut) := by
  change max ‖f z.1‖ ‖χ z.2 • (fderiv ℝ f z.1).comp z.2‖ ≤ _
  refine max_le ((hb _).trans (le_max_left _ _)) ?_
  by_cases hz : χ z.2 = 0
  · simp only [hz,zero_smul,norm_zero]
    exact hL.trans (le_max_left _ _)
  have hnorm : ‖z.2‖ ≤ χ.rOut := by
    have hh : z.2 ∈ Metric.ball 0 χ.rOut := by rwa [← χ.support_eq]
    exact (show ‖z.2‖ < χ.rOut by simpa only [Metric.mem_ball,dist_zero_right] using hh).le
  calc
    _ = χ z.2 * ‖(fderiv ℝ f z.1).comp z.2‖ := by rw [norm_smul,Real.norm_of_nonneg χ.nonneg]
    _ ≤ ‖(fderiv ℝ f z.1).comp z.2‖ := mul_le_of_le_one_left (norm_nonneg _) χ.le_one
    _ ≤ ‖fderiv ℝ f z.1‖ * ‖z.2‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K*χ.rOut := mul_le_mul (hd _) hnorm (norm_nonneg _) hK
    _ ≤ _ := le_max_right _ _

lemma exists_finite_variational_flow {f : E → E} {T L K : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hf : ContDiff ℝ 2 f) (hb : ∀ x, ‖f x‖ ≤ L)
    (hd : ∀ x, ‖fderiv ℝ f x‖ ≤ K) (x₀ : E) :
    ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E), ∃ L' : ℝ≥0,
      (∀ x ∈ closedBall x₀ (1/2 : ℝ), α x 0 = x ∧ A x 0 = ContinuousLinearMap.id ℝ E ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (α x t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (A x)
          ((fderiv ℝ f (α x t)).comp (A x t)) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, α x t ∈ closedBall x₀ (L*T+1/2)) ∧
      ∀ t ∈ Icc 0 T, LipschitzOnWith L' (α · t) (closedBall x₀ (1/2 : ℝ)) := by
  let χ : ContDiffBump (0 : E →L[ℝ] E) :=
    ⟨Real.exp (K*T)+1,Real.exp (K*T)+2,by positivity,by linarith⟩
  let M := max L (K*χ.rOut)
  let z₀ : E × (E →L[ℝ] E) := (x₀,ContinuousLinearMap.id ℝ E)
  obtain ⟨β,L',hβ,hLip⟩ := exists_bounded_picard_flow hT
    (hL.trans (le_max_left L (K*χ.rOut)))
    ((contDiff_cutVariationalField hf χ.contDiff).comp contDiff_snd).contDiffOn
    (fun _ _ z => cutVariationalField_bounded hL hK hb hd χ z) z₀
  let α : E → ℝ → E := fun x t => (β (x,ContinuousLinearMap.id ℝ E) t).1
  let A : E → ℝ → (E →L[ℝ] E) := fun x t => (β (x,ContinuousLinearMap.id ℝ E) t).2
  have hmem {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) :
      (x,ContinuousLinearMap.id ℝ E) ∈ closedBall z₀ (1/2 : ℝ) := by
    simpa only [z₀,Metric.mem_closedBall,Prod.dist_eq,dist_self,max_eq_left (dist_nonneg : 0 ≤ dist x x₀)] using hx
  have hα₀ {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) : α x 0 = x :=
    congrArg Prod.fst (hβ _ (hmem hx)).1
  have hA₀ {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) : A x 0 = ContinuousLinearMap.id ℝ E :=
    congrArg Prod.snd (hβ _ (hmem hx)).1
  have hαd {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (α x) (f (α x t)) (Icc 0 T) t :=
    ((hβ _ (hmem hx)).2 t ht).fst
  have hAd {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (A x) (χ (A x t) • (fderiv ℝ f (α x t)).comp (A x t)) (Icc 0 T) t :=
    ((hβ _ (hmem hx)).2 t ht).snd
  have hAbound {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      ‖A x t‖ ≤ Real.exp (K*T) := by
    have hh := norm_le_gronwallBound_of_norm_deriv_right_le
      (HasDerivWithinAt.continuousOn (fun t ht => hAd hx ht))
      (fun t ht => (hAd hx (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
      (δ := 1) (K := K) (ε := 0)
      (by rw [hA₀ hx]; exact ContinuousLinearMap.norm_id_le)
      (fun t ht => by
        rw [norm_smul,Real.norm_of_nonneg χ.nonneg,add_zero]
        calc
          _ ≤ ‖(fderiv ℝ f (α x t)).comp (A x t)‖ := mul_le_of_le_one_left (norm_nonneg _) χ.le_one
          _ ≤ ‖fderiv ℝ f (α x t)‖ * ‖A x t‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ K*‖A x t‖ := mul_le_mul_of_nonneg_right (hd _) (norm_nonneg _)) t ht
    rw [gronwallBound_ε0,one_mul,sub_zero] at hh
    exact hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK))
  have hone {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      χ (A x t) = 1 := by
    apply χ.one_of_mem_closedBall
    simp only [Metric.mem_closedBall,dist_zero_right]
    exact (hAbound hx ht).trans (by dsimp [χ]; linarith)
  refine ⟨α,A,L',?_,?_⟩
  · intro x hx
    refine ⟨hα₀ hx,hA₀ hx,(fun _ ht => hαd hx ht),?_,?_⟩
    · intro t ht
      simpa only [hone hx ht,one_smul] using hAd hx ht
    · intro t ht
      have hl : LipschitzOnWith ⟨L,hL⟩ (α x) (Icc 0 T) :=
        (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
          (fun s hs => hαd hx hs) (fun s _ => by exact_mod_cast hb (α x s))
      have hh := hl.dist_le_mul t ht 0 (show 0 ∈ Icc 0 T from ⟨le_rfl,hT⟩)
      rw [hα₀ hx,Real.dist_eq,sub_zero,abs_of_nonneg ht.1] at hh
      change dist (α x t) x₀ ≤ L*T+1/2
      exact (dist_triangle _ x _).trans (add_le_add
        (hh.trans (mul_le_mul_of_nonneg_left ht.2 hL)) hx)
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact (le_max_left _ _).trans (by
      simpa [Prod.dist_eq] using (hLip t ht).dist_le_mul _ (hmem hx) _ (hmem hy))

lemma hasFDerivAt_finite_variational_flow {f : E → E} (hf : ContDiff ℝ 2 f)
    {x₀ : E} {r R T : ℝ}
    {α : E → ℝ → E} {A : E → ℝ → (E →L[ℝ] E)} {L : ℝ≥0}
    (hsol : ∀ x ∈ closedBall x₀ r, α x 0 = x ∧ A x 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (α x t)) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt (A x)
        ((fderiv ℝ f (α x t)).comp (A x t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, α x t ∈ closedBall x₀ R)
    (hLip : ∀ t ∈ Icc 0 T, LipschitzOnWith L (α · t) (closedBall x₀ r))
    {x : E} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasFDerivAt (fun y => α y t) (A x t) x := by
  have hx' := ball_subset_closedBall hx
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
  filter_upwards [closedBall_mem_nhds_of_mem hx] with y hy
  have hxs := hsol x hx'
  have hys := hsol y hy
  have hdα (z : E) (hz : z ∈ closedBall x₀ r) (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasDerivWithinAt (α z) (f (α z s)) (Ici s) s :=
    ((hsol z hz).2.2.1 s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hdA (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasDerivWithinAt (A x) ((fderiv ℝ f (α x s)).comp (A x s)) (Ici s) s :=
    (hxs.2.2.2.1 s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hb := variational_remainder_bound
    (HasDerivWithinAt.continuousOn hxs.2.2.1)
    (HasDerivWithinAt.continuousOn hys.2.2.1)
    (HasDerivWithinAt.continuousOn hxs.2.2.2.1)
    (hdα x hx') (hdα y hy) hdA
    (v := y-x) (K := K) (ε := (LD : ℝ)*(L : ℝ)^2*‖y-x‖^2)
    (by simp [hxs.1,hys.1,hxs.2.1])
    (fun s hs => (hM ⟨α x s,hxs.2.2.2.2 s (Ico_subset_Icc_self hs),rfl⟩).trans (le_max_right _ _))
    (fun s hs => ?_)
  · have hb' := hb t ht
    apply hb'.trans_eq
    rw [gronwallBound_of_K_ne_0 hK.ne']
    dsimp [C]
    ring_nf
  · have hTaylor := taylor_bound_lipschitz_derivative
      (convex_closedBall x₀ R) (fun z _ => (hf.differentiable (by norm_num)) z)
      hLD (hxs.2.2.2.2 s (Ico_subset_Icc_self hs)) (hys.2.2.2.2 s (Ico_subset_Icc_self hs))
    apply hTaylor.trans
    have hn := (hLip s (Ico_subset_Icc_self hs)).norm_sub_le hy hx'
    have hsq : ‖α y s-α x s‖^2 ≤ ((L : ℝ)*‖y-x‖)^2 :=
      sq_le_sq₀ (norm_nonneg _) (mul_nonneg L.2 (norm_nonneg _)) |>.mpr hn
    calc
      _ ≤ (LD : ℝ)*((L : ℝ)*‖y-x‖)^2 := mul_le_mul_of_nonneg_left hsq LD.2
      _ = _ := by ring

lemma flow_injOn_of_finite_ode {f : E → E} (hf : ContDiff ℝ 1 f)
    {x₀ : E} {r R T : ℝ} {α : E → ℝ → E}
    (hinit : ∀ x ∈ closedBall x₀ r, α x 0 = x)
    (hder : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (α x) (f (α x t)) (Icc 0 T) t)
    (hrange : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc 0 T, α x t ∈ closedBall x₀ R)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Set.InjOn (fun x => α x t) (closedBall x₀ r) := by
  obtain ⟨K,hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall x₀ R) (isCompact_closedBall x₀ R)
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hd (x : E) (hx : x ∈ closedBall x₀ r) (s : ℝ) (hs : s ∈ Ioc 0 t) :
      HasDerivWithinAt (α x) (f (α x s)) (Iic s) s :=
    ((hder x hx s (hsub (Ioc_subset_Icc_self hs))).mono hsub).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem hs)
  intro x hx y hy heq
  have hu := ODE_solution_unique_of_mem_Icc_left
    (v := fun _ => f) (s := fun _ => closedBall x₀ R)
    (fun _ _ => hK)
    ((HasDerivWithinAt.continuousOn (hder x hx)).mono hsub) (hd x hx)
    (fun s hs => hrange x hx s (hsub (Ioc_subset_Icc_self hs)))
    ((HasDerivWithinAt.continuousOn (hder y hy)).mono hsub) (hd y hy)
    (fun s hs => hrange y hy s (hsub (Ioc_subset_Icc_self hs))) heq (show 0 ∈ Icc 0 t from ⟨le_rfl,ht.1⟩)
  simpa [hinit x hx,hinit y hy] using hu

lemma exists_finite_volume_flow {f : E → E} {T L K : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hf : ContDiff ℝ 2 f) (hb : ∀ x, ‖f x‖ ≤ L)
    (hd : ∀ x, ‖fderiv ℝ f x‖ ≤ K)
    (hdiv : ∀ x, LinearMap.trace ℝ E (fderiv ℝ f x).toLinearMap = 0) (x₀ : E) :
    ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E),
      (∀ x ∈ ball x₀ (1/2 : ℝ), α x 0 = x ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (α x t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasFDerivAt (fun y => α y t) (A x t) x) ∧
        ∀ t ∈ Icc 0 T, (A x t).det = 1) ∧
      ∀ t ∈ Icc 0 T, Set.InjOn (fun x => α x t) (ball x₀ (1/2 : ℝ)) := by
  obtain ⟨α,A,L',hsol,hLip⟩ := exists_finite_variational_flow hT hL hK hf hb hd x₀
  refine ⟨α,A,?_,?_⟩
  · intro x hx
    have hh := hsol x (ball_subset_closedBall hx)
    refine ⟨hh.1,hh.2.2.1,(fun _ ht => hasFDerivAt_finite_variational_flow hf hsol hLip hx ht),?_⟩
    exact determinant_clm_eq_one_of_trace_zero hT
      (HasDerivWithinAt.continuousOn hh.2.2.2.1) hh.2.1
      (fun t ht => (hh.2.2.2.1 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      (fun _ _ => hdiv _)
  · intro t ht
    exact (flow_injOn_of_finite_ode (hf.of_le (by norm_num))
      (fun x hx => (hsol x hx).1) (fun x hx => (hsol x hx).2.2.1)
      (fun x hx => (hsol x hx).2.2.2.2) ht).mono ball_subset_closedBall

lemma exists_bounded_volume_flow {f : E → E} {T L : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hf : ContDiff ℝ 2 f)
    (hb : ∀ x, ‖f x‖ ≤ L)
    (hdiv : ∀ x, LinearMap.trace ℝ E (fderiv ℝ f x).toLinearMap = 0) (x₀ : E) :
    ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E),
      (∀ x ∈ ball x₀ (1/2 : ℝ), α x 0 = x ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (α x t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasFDerivAt (fun y => α y t) (A x t) x) ∧
        ∀ t ∈ Icc 0 T, (A x t).det = 1) ∧
      ∀ t ∈ Icc 0 T, Set.InjOn (fun x => α x t) (ball x₀ (1/2 : ℝ)) := by
  let χ : ContDiffBump x₀ := ⟨L*T+1,L*T+2,by positivity,by linarith⟩
  let g : E → E := fun x => χ x • f x
  have hg : ContDiff ℝ 2 g := χ.contDiff.smul hf
  have hgc : HasCompactSupport g := χ.hasCompactSupport.smul_right
  have hgb (x : E) : ‖g x‖ ≤ L := by
    change ‖χ x • f x‖ ≤ L
    rw [norm_smul,Real.norm_of_nonneg χ.nonneg]
    exact (mul_le_of_le_one_left (norm_nonneg _) χ.le_one).trans (hb x)
  obtain ⟨K,hK⟩ := (hg.fderiv_right (m := 1) (by norm_num)).continuous.bounded_above_of_compact_support (hgc.fderiv ℝ)
  obtain ⟨α,A,L',hsol,hLip⟩ := exists_finite_variational_flow hT hL
    (le_max_left 0 K) hg hgb (fun x => (hK x).trans (le_max_right 0 K)) x₀
  have hlocal {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      g =ᶠ[𝓝 (α x t)] f := by
    have hm : α x t ∈ ball x₀ χ.rIn := by
      have hh := (hsol x hx).2.2.2.2 t ht
      change dist (α x t) x₀ < L*T+1
      change dist (α x t) x₀ ≤ L*T+1/2 at hh
      linarith
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hm] with z hz
    change χ z • f z = f z
    rw [hz]
    exact one_smul ℝ (f z)
  have hval {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      g (α x t) = f (α x t) := (hlocal hx ht).eq_of_nhds
  have hdval {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      fderiv ℝ g (α x t) = fderiv ℝ f (α x t) := (hlocal hx ht).fderiv_eq
  refine ⟨α,A,?_,?_⟩
  · intro x hx
    have hx' := ball_subset_closedBall hx
    have hh := hsol x hx'
    refine ⟨hh.1,?_,(fun _ ht => hasFDerivAt_finite_variational_flow hg hsol hLip hx ht),?_⟩
    · intro t ht
      simpa only [hval hx' ht] using hh.2.2.1 t ht
    · apply determinant_clm_eq_one_of_trace_zero hT
        (HasDerivWithinAt.continuousOn hh.2.2.2.1) hh.2.1
        (fun t ht => (hh.2.2.2.1 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      intro t ht
      rw [hdval hx' (Ioo_subset_Icc_self ht)]
      exact hdiv _
  · intro t ht
    exact (flow_injOn_of_finite_ode (hg.of_le (by norm_num))
      (fun x hx => (hsol x hx).1) (fun x hx => (hsol x hx).2.2.1)
      (fun x hx => (hsol x hx).2.2.2.2) ht).mono ball_subset_closedBall
end RVM

end

end OAI
