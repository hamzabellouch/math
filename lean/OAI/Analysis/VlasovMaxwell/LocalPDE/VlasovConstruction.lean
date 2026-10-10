import Mathlib
import OAI.Analysis.VlasovMaxwell.Maxwell.DifferenceFieldEnergy
import OAI.Analysis.VlasovMaxwell.Flow.WithinFlow
import OAI.Analysis.VlasovMaxwell.Population.LabelOccupationDurationMass

namespace OAI

noncomputable section

section

open Set MeasureTheory Metric Filter ODE
open scoped Topology NNReal ContDiff

namespace RVM

universe u

lemma contDiff_spaceDerivative {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (spaceDerivative f) := by
  have h := (hf.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_comp
    (contDiff_const (c := ContinuousLinearMap.inr ℝ ℝ E))
  convert h using 1
  funext z
  exact ((hf.differentiable (by simp) z).hasFDerivAt.comp z.2
    ((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2))).fderiv

lemma smooth_ode_unique {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℝ × E → E} {T : ℝ}
    (hf : ContDiff ℝ 1 f) {α β : ℝ → E}
    (hα : ∀ t ∈ Icc 0 T, HasDerivWithinAt α (f (t,α t)) (Icc 0 T) t)
    (hβ : ∀ t ∈ Icc 0 T, HasDerivWithinAt β (f (t,β t)) (Icc 0 T) t)
    (h0 : α 0 = β 0) : EqOn α β (Icc 0 T) := by
  have hαc := HasDerivWithinAt.continuousOn hα
  have hβc := HasDerivWithinAt.continuousOn hβ
  obtain ⟨R,hR⟩ := ((isCompact_Icc.image_of_continuousOn hαc).union
    (isCompact_Icc.image_of_continuousOn hβc)).isBounded.subset_closedBall (0 : E)
  obtain ⟨K,hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    ((convex_Icc 0 T).prod (convex_closedBall (0 : E) R))
    (isCompact_Icc.prod (isCompact_closedBall (0 : E) R))
  apply ODE_solution_unique_of_mem_Icc_right (v := fun t x => f (t,x))
    (s := fun _ => closedBall (0 : E) R) (K := K) _ hαc _ _ hβc _ _ h0
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist x y)]
      using hK.dist_le_mul (t,x) ⟨Ico_subset_Icc_self ht,hx⟩
        (t,y) ⟨Ico_subset_Icc_self ht,hy⟩
  · intro t ht
    exact (hα t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact hR (Or.inl ⟨t,Ico_subset_Icc_self ht,rfl⟩)
  · intro t ht
    exact (hβ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact hR (Or.inr ⟨t,Ico_subset_Icc_self ht,rfl⟩)

def BoundedFlowRegularity (n : ℕ) : Prop :=
  ∀ (E Z : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : ℝ × E → E) (T L : ℝ) (U : Set Z) (g : Z → E) (α : Z → ℝ → E),
    0 < T → 0 ≤ L → ContDiff ℝ ∞ f →
    (∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L) →
    IsOpen U → ContDiffOn ℝ ∞ g U →
    (∀ x ∈ U, α x 0 = g x) →
    (∀ x ∈ U, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) →
    ContDiffOn ℝ n (fun z : ℝ × Z => α z.2 z.1) (Ioo 0 T ×ˢ U)

lemma bounded_cutoff_vector_field {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℝ × E → E} (hf : ContDiff ℝ ∞ f) (T R : ℝ) :
    ∃ g : ℝ × E → E, ∃ L : ℝ, 0 ≤ L ∧ ContDiff ℝ ∞ g ∧
      (∀ t ∈ Icc 0 T, ∀ x, ‖g (t,x)‖ ≤ L) ∧
      ∀ t x, x ∈ closedBall (0 : E) R → g (t,x) = f (t,x) := by
  let χ : ContDiffBump (0 : E) := ⟨max 0 R + 1,max 0 R + 2,by positivity,by linarith⟩
  let g : ℝ × E → E := fun z => χ z.2 • f z
  have hg : ContDiff ℝ ∞ g := (χ.contDiff.comp contDiff_snd).smul hf
  obtain ⟨L,hL⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : E) χ.rOut)).bddAbove_image
    hg.continuous.norm.continuousOn
  refine ⟨g,max 0 L,le_max_left _ _,hg,?_,?_⟩
  · intro t ht x
    by_cases hx : x ∈ closedBall (0 : E) χ.rOut
    · exact (hL ⟨(t,x),⟨ht,hx⟩,rfl⟩).trans (le_max_right _ _)
    have hz : χ x = 0 := by
      apply Function.notMem_support.mp
      rw [χ.support_eq]
      exact fun hm => hx (ball_subset_closedBall hm)
    simp only [g,hz,zero_smul,norm_zero]
    exact le_max_left _ _
  · intro t x hx
    have hm : x ∈ closedBall (0 : E) χ.rIn := by
      exact closedBall_subset_closedBall (by dsimp [χ]; linarith [le_max_right (0 : ℝ) R]) hx
    change χ x • f (t,x) = f (t,x)
    rw [χ.one_of_mem_closedBall hm,one_smul]

lemma contDiffAt_flow_transfer {E Z : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : ℝ × E → E} {T : ℝ} {U : Set Z} {V : Set E} {g : Z → E}
    {α : Z → ℝ → E} {β : E → ℝ → E} {n : ℕ} {t : ℝ} {x : Z}
    (hf : ContDiff ℝ 1 f) (hU : IsOpen U) (hV : IsOpen V)
    (hg : ContDiffOn ℝ n g U)
    (hα0 : ∀ x ∈ U, α x 0 = g x)
    (hαd : ∀ x ∈ U, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t)
    (hβ0 : ∀ y ∈ V, β y 0 = y)
    (hβd : ∀ y ∈ V, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (β y) (f (t,β y t)) (Icc 0 T) t)
    (hβ : ContDiffOn ℝ n (fun z : ℝ × E => β z.2 z.1) (Ioo 0 T ×ˢ V))
    (ht : t ∈ Ioo 0 T) (hx : x ∈ U) (hmem : g x ∈ V) :
    ContDiffAt ℝ n (fun z : ℝ × Z => α z.2 z.1) (t,x) := by
  have hgc := (hg.contDiffAt (hU.mem_nhds hx)).comp (t,x) contDiffAt_snd
  have hh := (hβ.contDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨ht,hmem⟩)).comp
    (t,x) (contDiffAt_fst.prodMk hgc)
  apply hh.congr_of_eventuallyEq
  have heU : ∀ᶠ z : ℝ × Z in 𝓝 (t,x), z.2 ∈ U :=
    continuousAt_snd.eventually (hU.mem_nhds hx)
  have heV : ∀ᶠ z : ℝ × Z in 𝓝 (t,x), g z.2 ∈ V :=
    hgc.continuousAt.eventually (hV.mem_nhds hmem)
  have heT : ∀ᶠ z : ℝ × Z in 𝓝 (t,x), z.1 ∈ Ioo 0 T :=
    continuousAt_fst.eventually (isOpen_Ioo.mem_nhds ht)
  filter_upwards [heU,heV,heT] with z hzU hzV hzT
  exact smooth_ode_unique hf (hαd z.2 hzU) (hβd (g z.2) hzV)
    ((hα0 z.2 hzU).trans (hβ0 (g z.2) hzV).symm) (Ioo_subset_Icc_self hzT)

lemma boundedFlowRegularity_zero : BoundedFlowRegularity.{u} 0 := by
  intro E Z _ _ _ _ _ f T L U g α hT hL hf hb hU hg hα0 hαd z hz
  obtain ⟨β,A,K,hsol,hLip⟩ := exists_bounded_within_variational_flow hT hL
    (contDiff_infty.mp hf 2).contDiffOn hb (g z.2)
  have hβc : ContinuousOn (fun w : ℝ × E => β w.2 w.1)
      (Icc 0 T ×ˢ closedBall (g z.2) (1/2 : ℝ)) :=
    continuousOn_time_label_of_lipschitz
      (fun y hy => HasDerivWithinAt.continuousOn (hsol y hy).2.2.1)
      (fun t ht => (hLip t ht).1)
  have hreg : ContDiffOn ℝ 0 (fun w : ℝ × E => β w.2 w.1)
      (Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) :=
    contDiffOn_zero.mpr (hβc.mono (prod_mono Ioo_subset_Icc_self ball_subset_closedBall))
  exact (contDiffAt_flow_transfer (hf.of_le (by simp)) hU isOpen_ball (hg.of_le (by simp))
    hα0 hαd (fun y hy => (hsol y (ball_subset_closedBall hy)).1)
    (fun y hy => (hsol y (ball_subset_closedBall hy)).2.2.1)
    hreg hz.1 hz.2 (by simp)).contDiffWithinAt

lemma boundedFlowRegularity_succ {n : ℕ} (hn : BoundedFlowRegularity.{u} n) :
    BoundedFlowRegularity.{u} (n+1) := by
  intro E Z _ _ _ _ _ f T L U g α hT hL hf hb hU hg hα0 hαd z hz
  obtain ⟨β,A,K,hsol,hLip⟩ := exists_bounded_within_variational_flow hT hL
    (contDiff_infty.mp hf 2).contDiffOn hb (g z.2)
  have hβc : ContinuousOn (fun w : ℝ × E => β w.2 w.1)
      (Icc 0 T ×ˢ closedBall (g z.2) (1/2 : ℝ)) :=
    continuousOn_time_label_of_lipschitz
      (fun y hy => HasDerivWithinAt.continuousOn (hsol y hy).2.2.1)
      (fun t ht => (hLip t ht).1)
  have hAc : ContinuousOn (fun w : ℝ × E => A w.2 w.1)
      (Icc 0 T ×ˢ closedBall (g z.2) (1/2 : ℝ)) :=
    continuousOn_time_label_of_lipschitz
      (fun y hy => HasDerivWithinAt.continuousOn (hsol y hy).2.2.2.1)
      (fun t ht => (hLip t ht).2)
  obtain ⟨R,hR⟩ := (isCompact_Icc.prod (isCompact_closedBall (g z.2) (1/2 : ℝ))).bddAbove_image
    (hβc.prodMk hAc).norm
  let F : ℝ × (E × (E →L[ℝ] E)) → E × (E →L[ℝ] E) :=
    fun w => (f (w.1,w.2.1),(spaceDerivative f (w.1,w.2.1)).comp w.2.2)
  have hp : ContDiff ℝ ∞ (fun w : ℝ × (E × (E →L[ℝ] E)) => (w.1,w.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hF : ContDiff ℝ ∞ F := (hf.comp hp).prodMk
    (((contDiff_spaceDerivative hf).comp hp).clm_comp (contDiff_snd.comp contDiff_snd))
  obtain ⟨Fc,Lc,hLc,hFc,hFcb,hFceq⟩ := bounded_cutoff_vector_field hF T R
  have heq (x : E) (hx : x ∈ closedBall (g z.2) (1/2 : ℝ)) (t : ℝ) (ht : t ∈ Icc 0 T) :
      Fc (t,(β x t,A x t)) = F (t,(β x t,A x t)) := by
    apply hFceq
    simpa only [mem_closedBall,dist_zero_right] using hR ⟨(t,x),⟨ht,hx⟩,rfl⟩
  have hlift : ContDiffOn ℝ n (fun w : ℝ × E => (β w.2 w.1,A w.2 w.1))
      (Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) := by
    apply hn (E × (E →L[ℝ] E)) E Fc T Lc (ball (g z.2) (1/2 : ℝ))
      (fun x => (x,ContinuousLinearMap.id ℝ E)) (fun x t => (β x t,A x t))
      hT hLc hFc hFcb isOpen_ball (contDiff_id.prodMk contDiff_const).contDiffOn
    · intro x hx
      exact Prod.ext (hsol x (ball_subset_closedBall hx)).1
        (hsol x (ball_subset_closedBall hx)).2.1
    · intro x hx t ht
      rw [heq x (ball_subset_closedBall hx) t ht]
      exact ((hsol x (ball_subset_closedBall hx)).2.2.1 t ht).prodMk
        ((hsol x (ball_subset_closedBall hx)).2.2.2.1 t ht)
  have hβn : ContDiffOn ℝ n (fun w : ℝ × E => β w.2 w.1)
      (Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) := contDiff_fst.comp_contDiffOn hlift
  have hAn : ContDiffOn ℝ n (fun w : ℝ × E => A w.2 w.1)
      (Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) := contDiff_snd.comp_contDiffOn hlift
  let D : ℝ × E → (ℝ × E →L[ℝ] E) := fun w =>
    (ContinuousLinearMap.toSpanSingleton ℝ (f (w.1,β w.2 w.1))).coprod (A w.2 w.1)
  have hDn : ContDiffOn ℝ n D (Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) := by
    have hfn := (contDiff_infty.mp hf n).comp_contDiffOn
      (contDiffOn_fst.prodMk hβn)
    have hcol := (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).contDiff.comp_contDiffOn hfn
    exact (hcol.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ ℝ E))).add
      (hAn.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ ℝ E)))
  have hβd (w : ℝ × E) (hw : w ∈ Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) :
      HasFDerivAt (fun v : ℝ × E => β v.2 v.1) (D w) w := by
    exact (hasStrictFDerivAt_time_flow hf.continuous.continuousOn
      (hβc.mono (prod_mono Subset.rfl ball_subset_closedBall))
      (hAc.mono (prod_mono Subset.rfl ball_subset_closedBall))
      (fun x hx => (hsol x (ball_subset_closedBall hx)).2.2.1)
      (fun t ht x hx => hasFDerivAt_within_variational_flow hT
        (contDiff_infty.mp hf 2).contDiffOn hsol (fun t ht => (hLip t ht).1) hx ht)
      hw.1 hw.2).hasFDerivAt
  have hreg : ContDiffOn ℝ (n+1) (fun w : ℝ × E => β w.2 w.1)
      (Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ)) := by
    intro w hw
    have hnh := (isOpen_Ioo.prod isOpen_ball).mem_nhds hw
    exact (contDiffAt_succ_iff_hasFDerivAt.mpr
      ⟨D,⟨Ioo 0 T ×ˢ ball (g z.2) (1/2 : ℝ),hnh,hβd⟩,hDn.contDiffAt hnh⟩).contDiffWithinAt
  exact (contDiffAt_flow_transfer (contDiff_infty.mp hf 1) hU isOpen_ball (contDiffOn_infty.mp hg (n+1))
    hα0 hαd (fun y hy => (hsol y (ball_subset_closedBall hy)).1)
    (fun y hy => (hsol y (ball_subset_closedBall hy)).2.2.1)
    hreg hz.1 hz.2 (by simp)).contDiffWithinAt

lemma boundedFlowRegularity_all (n : ℕ) : BoundedFlowRegularity.{u} n := by
  induction n with
  | zero => exact boundedFlowRegularity_zero
  | succ n hn => exact boundedFlowRegularity_succ hn

lemma contDiffOn_bounded_flow {E Z : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : ℝ × E → E} {T L : ℝ} {U : Set Z} {g : Z → E} {α : Z → ℝ → E}
    (hT : 0 < T) (hL : 0 ≤ L) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L)
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hα0 : ∀ x ∈ U, α x 0 = g x)
    (hαd : ∀ x ∈ U, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Z => α z.2 z.1) (Ioo 0 T ×ˢ U) := by
  rw [contDiffOn_infty]
  intro n
  exact boundedFlowRegularity_all n E Z f T L U g α hT hL hf hb hU hg hα0 hαd

lemma PhaseFlowOn.contDiffOn_joint {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0 < T)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    ContDiffOn ℝ ∞ (fun w : ℝ × Phase => F.flow w.2 w.1)
      (Ioo 0 T ×ˢ (univ : Set Phase)) := by
  have hc := F.continuousOn_joint hT.le hE.continuous.continuousOn hB.continuous.continuousOn
  have hf := contDiff_lorentzField hE hB
  intro z hz
  obtain ⟨R,hR⟩ := (isCompact_Icc.prod (isCompact_closedBall z.2 (1 : ℝ))).bddAbove_image
    (hc.mono (prod_mono Subset.rfl (subset_univ _))).norm
  obtain ⟨f,L,hL,hf,hb,heq⟩ := bounded_cutoff_vector_field hf T R
  have hreg : ContDiffOn ℝ ∞ (fun w : ℝ × Phase => F.flow w.2 w.1)
      (Ioo 0 T ×ˢ ball z.2 1) := by
    apply contDiffOn_bounded_flow hT hL hf hb isOpen_ball contDiffOn_id
      (fun x _ => F.initial x)
    intro x hx t ht
    rw [heq t (F.flow x t) (by
      simpa only [mem_closedBall,dist_zero_right] using
        hR ⟨(t,x),⟨ht,ball_subset_closedBall hx⟩,rfl⟩)]
    exact F.ode x t ht
  exact (hreg.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds
    ⟨hz.1,mem_ball_self zero_lt_one⟩)).contDiffWithinAt

lemma contDiffAt_inversePhase {Q : Type u}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {α : Q → ℝ → Q} {v x : Q} {A : Q →L[ℝ] Q} {T t : ℝ}
    (hbij : ∀ s ∈ Ioo 0 T, Function.Bijective (α · s)) (ht : t ∈ Ioo 0 T)
    (hA : A.det = 1)
    (hα : HasFDerivAt (fun z : ℝ × Q => α z.2 z.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ v).coprod A) (t,x))
    (hreg : ContDiffAt ℝ ∞ (fun z : ℝ × Q => α z.2 z.1) (t,x)) :
    ContDiffAt ℝ ∞ (inversePhase α) (t,α x t) := by
  obtain ⟨e,D,he,hD,hder⟩ := inverse_timeFlowDerivative hA
  let Φ : ℝ × Q → ℝ × Q := fun z => (z.1,α z.2 z.1)
  have hΦd : HasFDerivAt Φ (e : (ℝ × Q) →L[ℝ] (ℝ × Q)) (t,x) := by
    rw [he]
    exact hasFDerivAt_fst.prodMk hα
  have hΦc : ContDiffAt ℝ ∞ Φ (t,x) := contDiffAt_fst.prodMk hreg
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let Z := hΦc.localInverse hΦd hn
  have hZ : ContDiffAt ℝ ∞ Z (t,α x t) := hΦc.to_localInverse hΦd hn
  have hr := (hΦc.hasStrictFDerivAt' hΦd hn).eventually_right_inverse
  have heq : inversePhase α =ᶠ[𝓝 (t,α x t)] (fun z => (Z z).2) := by
    have htime : ∀ᶠ z : ℝ × Q in 𝓝 (t,α x t), z.1 ∈ Ioo 0 T :=
      continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds ht)
    filter_upwards [hr,htime] with z hz hzt
    have hx : (Z z).1 = z.1 := by
      have hh := congrArg Prod.fst hz
      exact hh
    have hy : α (Z z).2 z.1 = z.2 := by
      have hh := congrArg Prod.snd hz
      change α (Z z).2 (Z z).1 = z.2 at hh
      rwa [hx] at hh
    apply (hbij z.1 hzt).1
    exact (Function.invFun_eq ((hbij z.1 hzt).2 z.2)).trans hy.symm
  exact hZ.snd.congr_of_eventuallyEq heq

lemma PhaseFlowOn.contDiffOn_inverse {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0 < T)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    ContDiffOn ℝ ∞ (inversePhase F.flow) (Ioo 0 T ×ˢ (univ : Set Phase)) := by
  intro z hz
  let y := inversePhase F.flow z
  have hy : F.flow y z.1 = z.2 := F.flow_inversePhase (Ioo_subset_Icc_self hz.1) z.2
  have hh := contDiffAt_inversePhase
    (fun s hs => F.bijective s (Ioo_subset_Icc_self hs)) hz.1
    (F.det_one y z.1 (Ioo_subset_Icc_self hz.1))
    (F.joint y z.1 hz.1).hasFDerivAt
    ((F.contDiffOn_joint hT hE hB).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hz.1,mem_univ y⟩))
  simpa only [hy] using hh.contDiffWithinAt

structure SymmetricLorentzFlow (E B : Field) (R : ℝ) where
  forward : Phase → ℝ → Phase
  backward : ℝ × Phase → Phase
  initial : ∀ z, forward z 0 = z
  ode : ∀ z t, t ∈ Ioo (-R) R →
    HasDerivAt (forward z) (lorentzField E B (t,forward z t)) t
  smooth_forward : ContDiffOn ℝ ∞ (fun w : ℝ × Phase => forward w.2 w.1)
    (Ioo (-R) R ×ˢ (univ : Set Phase))
  smooth_backward : ContDiffOn ℝ ∞ backward (Ioo (-R) R ×ˢ (univ : Set Phase))
  left_inverse : ∀ t ∈ Ioo (-R) R, ∀ z, backward (t,forward z t) = z
  right_inverse : ∀ t ∈ Ioo (-R) R, ∀ z, forward (backward (t,z)) t = z

lemma exists_symmetricLorentzFlow {E B : Field} {R : ℝ} (hR : 0 < R)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    Nonempty (SymmetricLorentzFlow E B R) := by
  let E' : Field := fun z => E (z.1-R,z.2)
  let B' : Field := fun z => B (z.1-R,z.2)
  have hs : ContDiff ℝ ∞ (fun z : ℝ × Vec => (z.1-R,z.2)) :=
    (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  have hE' : ContDiff ℝ ∞ E' := hE.comp hs
  have hB' : ContDiff ℝ ∞ B' := hB.comp hs
  obtain ⟨F⟩ := exists_phaseFlowOn (show 0 < 2*R by positivity)
    (contDiff_infty.mp hE' 2).contDiffOn (contDiff_infty.mp hB' 2).contDiffOn
  have hmid : R ∈ Ioo 0 (2*R) := ⟨hR,by linarith⟩
  have htime {t : ℝ} (ht : t ∈ Ioo (-R) R) : t+R ∈ Ioo 0 (2*R) :=
    ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hfc := F.contDiffOn_joint (by positivity) hE' hB'
  have hic := F.contDiffOn_inverse (by positivity) hE' hB'
  have hfmid : ContDiff ℝ ∞ (fun z => F.flow z R) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (hfc.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hmid,mem_univ z⟩)).comp z (contDiffAt_const.prodMk contDiffAt_id)
  have himid : ContDiff ℝ ∞ (fun z => inversePhase F.flow (R,z)) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (hic.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hmid,mem_univ z⟩)).comp z (contDiffAt_const.prodMk contDiffAt_id)
  let fw : Phase → ℝ → Phase := fun z t => F.flow (inversePhase F.flow (R,z)) (t+R)
  let bw : ℝ × Phase → Phase := fun w => F.flow (inversePhase F.flow (w.1+R,w.2)) R
  refine ⟨⟨fw,bw,?_,?_,?_,?_,?_,?_⟩⟩
  · intro z
    simpa only [fw,zero_add] using F.flow_inversePhase (Ioo_subset_Icc_self hmid) z
  · intro z t ht
    have hd := (F.ode (inversePhase F.flow (R,z)) (t+R) (Ioo_subset_Icc_self (htime ht))).hasDerivAt
      (Icc_mem_nhds (htime ht).1 (htime ht).2)
    simpa [fw,E',B',lorentzField,lorentzPhase,Function.comp_def] using
      hd.scomp t ((hasDerivAt_id t).add_const R)
  · exact hfc.comp ((contDiff_fst.add contDiff_const).prodMk
        (himid.comp contDiff_snd)).contDiffOn (fun _ hw => ⟨htime hw.1,mem_univ _⟩)
  · exact hfmid.comp_contDiffOn
      (hic.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
        (fun _ hw => ⟨htime hw.1,mem_univ _⟩))
  · intro t ht z
    change F.flow (inversePhase F.flow
      (t+R,F.flow (inversePhase F.flow (R,z)) (t+R))) R = z
    rw [F.inversePhase_flow (Ioo_subset_Icc_self (htime ht))]
    exact F.flow_inversePhase (Ioo_subset_Icc_self hmid) z
  · intro t ht z
    change F.flow (inversePhase F.flow
      (R,F.flow (inversePhase F.flow (t+R,z)) R)) (t+R) = z
    rw [F.inversePhase_flow (Ioo_subset_Icc_self hmid)]
    exact F.flow_inversePhase (Ioo_subset_Icc_self (htime ht)) z

lemma smooth_ode_unique_Icc {Q : Type u}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {f : ℝ × Q → Q} {a b t₀ : ℝ} (hf : ContDiff ℝ 1 f) {α β : ℝ → Q}
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (f (t,α t)) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivAt β (f (t,β t)) t)
    (ht₀ : t₀ ∈ Ioo a b) (h0 : α t₀ = β t₀) : EqOn α β (Icc a b) := by
  have hαc : ContinuousOn α (Icc a b) := fun _ ht => (hα _ ht).continuousAt.continuousWithinAt
  have hβc : ContinuousOn β (Icc a b) := fun _ ht => (hβ _ ht).continuousAt.continuousWithinAt
  obtain ⟨R,hR⟩ := ((isCompact_Icc.image_of_continuousOn hαc).union
    (isCompact_Icc.image_of_continuousOn hβc)).isBounded.subset_closedBall (0 : Q)
  obtain ⟨K,hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    ((convex_Icc a b).prod (convex_closedBall (0 : Q) R))
    (isCompact_Icc.prod (isCompact_closedBall (0 : Q) R))
  apply ODE_solution_unique_of_mem_Icc (v := fun t x => f (t,x))
    (s := fun _ => closedBall (0 : Q) R) (K := K) _ ht₀ hαc _ _ hβc _ _ h0
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist x y)]
      using hK.dist_le_mul (t,x) ⟨Ioo_subset_Icc_self ht,hx⟩
        (t,y) ⟨Ioo_subset_Icc_self ht,hy⟩
  · intro t ht
    exact hα t (Ioo_subset_Icc_self ht)
  · intro t ht
    exact hR (Or.inl ⟨t,Ioo_subset_Icc_self ht,rfl⟩)
  · intro t ht
    exact hβ t (Ioo_subset_Icc_self ht)
  · intro t ht
    exact hR (Or.inr ⟨t,Ioo_subset_Icc_self ht,rfl⟩)

lemma SymmetricLorentzFlow.agree {E B : Field} {R S t : ℝ}
    (F : SymmetricLorentzFlow E B R) (G : SymmetricLorentzFlow E B S)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (htR : |t| < R) (htS : |t| < S) (z : Phase) : F.forward z t = G.forward z t := by
  let r := (|t|+min R S)/2
  have hr : |t| < r := by dsimp [r]; have := lt_min htR htS; linarith
  have hrR : r < R := by dsimp [r]; linarith [min_le_left R S]
  have hrS : r < S := by dsimp [r]; linarith [min_le_right R S]
  have hr0 : 0 < r := (abs_nonneg t).trans_lt hr
  have hsubR : Icc (-r) r ⊆ Ioo (-R) R := by
    intro u hu; exact ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hsubS : Icc (-r) r ⊆ Ioo (-S) S := by
    intro u hu; exact ⟨by linarith [hu.1],by linarith [hu.2]⟩
  exact smooth_ode_unique_Icc (contDiff_infty.mp (contDiff_lorentzField hE hB) 1)
    (fun u hu => F.ode z u (hsubR hu)) (fun u hu => G.ode z u (hsubS hu))
    ⟨by linarith,hr0⟩ ((F.initial z).trans (G.initial z).symm)
    ⟨by linarith [(neg_le_abs t)],by linarith [le_abs_self t]⟩

lemma SymmetricLorentzFlow.backward_agree {E B : Field} {R S t : ℝ}
    (F : SymmetricLorentzFlow E B R) (G : SymmetricLorentzFlow E B S)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (htR : |t| < R) (htS : |t| < S) (z : Phase) : F.backward (t,z) = G.backward (t,z) := by
  have hR : t ∈ Ioo (-R) R := abs_lt.mp htR
  have hS : t ∈ Ioo (-S) S := abs_lt.mp htS
  calc
    F.backward (t,z) = F.backward (t,G.forward (G.backward (t,z)) t) := by
      rw [G.right_inverse t hS z]
    _ = F.backward (t,F.forward (G.backward (t,z)) t) := by
      rw [F.agree G hE hB htR htS]
    _ = G.backward (t,z) := F.left_inverse t hR _

structure SmoothLorentzFlow (E B : Field) where
  forward : Phase → ℝ → Phase
  backward : ℝ × Phase → Phase
  initial : ∀ z, forward z 0 = z
  ode : ∀ z t, HasDerivAt (forward z) (lorentzField E B (t,forward z t)) t
  smooth_forward : ContDiff ℝ ∞ (fun w : ℝ × Phase => forward w.2 w.1)
  smooth_backward : ContDiff ℝ ∞ backward
  left_inverse : ∀ t z, backward (t,forward z t) = z
  right_inverse : ∀ t z, forward (backward (t,z)) t = z

lemma exists_smoothLorentzFlow {E B : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) : Nonempty (SmoothLorentzFlow E B) := by
  let F : (R : ℝ) → 0 < R → SymmetricLorentzFlow E B R :=
    fun R hR => Classical.choice (exists_symmetricLorentzFlow hR hE hB)
  let rad : ℝ → ℝ := fun t => |t|+1
  have hrad0 : ∀ t, |t| < rad t := fun t => by dsimp [rad]; linarith
  have hrad : ∀ t, |t| < rad t := hrad0
  have hpos : ∀ t, 0 < rad t := fun t => (abs_nonneg t).trans_lt (hrad t)
  let fw : Phase → ℝ → Phase := fun z t => (F (rad t) (hpos t)).forward z t
  let bw : ℝ × Phase → Phase := fun w => (F (rad w.1) (hpos w.1)).backward w
  have hfw {R : ℝ} (hR : 0 < R) {t : ℝ} (ht : |t| < R) (z : Phase) :
      fw z t = (F R hR).forward z t :=
    (F (rad t) (hpos t)).agree (F R hR) hE hB (hrad t) ht z
  have hbw {R : ℝ} (hR : 0 < R) {t : ℝ} (ht : |t| < R) (z : Phase) :
      bw (t,z) = (F R hR).backward (t,z) :=
    (F (rad t) (hpos t)).backward_agree (F R hR) hE hB (hrad t) ht z
  have hlocal (t : ℝ) : ∀ᶠ u : ℝ in 𝓝 t, |u| < rad t :=
    continuous_abs.continuousAt.eventually_lt_const (hrad t)
  refine ⟨⟨fw,bw,?_,?_,?_,?_,?_,?_⟩⟩
  · intro z
    exact (F (rad 0) (hpos 0)).initial z
  · intro z t
    have heq : fw z =ᶠ[𝓝 t] (F (rad t) (hpos t)).forward z := by
      filter_upwards [hlocal t] with u hu
      exact hfw (hpos t) hu z
    exact ((F (rad t) (hpos t)).ode z t (abs_lt.mp (hrad t))).congr_of_eventuallyEq heq
  · rw [contDiff_iff_contDiffAt]
    intro w
    have heq : (fun w : ℝ × Phase => fw w.2 w.1) =ᶠ[𝓝 w]
        (fun v : ℝ × Phase => (F (rad w.1) (hpos w.1)).forward v.2 v.1) := by
      filter_upwards [continuous_fst.continuousAt.tendsto.eventually (hlocal w.1)] with v hv
      exact hfw (hpos w.1) hv v.2
    exact ((F (rad w.1) (hpos w.1)).smooth_forward.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨abs_lt.mp (hrad w.1),mem_univ w.2⟩)).congr_of_eventuallyEq heq
  · rw [contDiff_iff_contDiffAt]
    intro w
    have heq : bw =ᶠ[𝓝 w] (F (rad w.1) (hpos w.1)).backward := by
      filter_upwards [continuous_fst.continuousAt.tendsto.eventually (hlocal w.1)] with v hv
      exact hbw (hpos w.1) hv v.2
    exact ((F (rad w.1) (hpos w.1)).smooth_backward.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨abs_lt.mp (hrad w.1),mem_univ w.2⟩)).congr_of_eventuallyEq heq
  · intro t z
    exact (F (rad t) (hpos t)).left_inverse t (abs_lt.mp (hrad t)) z
  · intro t z
    exact (F (rad t) (hpos t)).right_inverse t (abs_lt.mp (hrad t)) z

namespace SmoothLorentzFlow

variable {E B : Field} (F : SmoothLorentzFlow E B)

def particle (f₀ : Phase → ℝ) : Particle := fun w => f₀ (F.backward w)

lemma contDiff_particle {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀) :
    ContDiff ℝ ∞ (F.particle f₀) := hf.comp F.smooth_backward

lemma particle_along (f₀ : Phase → ℝ) (t : ℝ) (z : Phase) :
    F.particle f₀ (t,F.forward z t) = f₀ z := by
  simp only [particle,F.left_inverse]

lemma backward_initial (z : Phase) : F.backward (0,z) = z := by
  simpa only [F.initial] using F.left_inverse 0 z

lemma particle_initial (f₀ : Phase → ℝ) (z : Phase) : F.particle f₀ (0,z) = f₀ z := by
  simp only [particle,F.backward_initial]

lemma particle_nonneg {f₀ : Phase → ℝ} (hf : ∀ z, 0 ≤ f₀ z) (w : ℝ × Phase) :
    0 ≤ F.particle f₀ w := hf _

lemma particle_compact {f₀ : Phase → ℝ} (hf : HasCompactSupport f₀) (a b : ℝ) :
    ∃ K : Set Phase, IsCompact K ∧
      ∀ t ∈ Icc a b, tsupport (fun z => F.particle f₀ (t,z)) ⊆ K := by
  let K := (fun w : ℝ × Phase => F.forward w.2 w.1) '' (Icc a b ×ˢ tsupport f₀)
  have hK : IsCompact K := (isCompact_Icc.prod hf).image F.smooth_forward.continuous
  refine ⟨K,hK,?_⟩
  intro t ht
  apply closure_minimal _ hK.isClosed
  intro z hz
  exact ⟨(t,F.backward (t,z)),⟨ht,subset_tsupport _ hz⟩,F.right_inverse t z⟩

lemma particle_vlasov_direction {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (t : ℝ) (z : Phase) :
    fderiv ℝ (F.particle f₀) (t,z) (1,lorentzField E B (t,z)) = 0 := by
  let y := F.backward (t,z)
  have hy : F.forward y t = z := F.right_inverse t z
  have hd := ((F.contDiff_particle hf).differentiable (by simp) (t,F.forward y t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (F.ode y t))
  have heq : (fun r => F.particle f₀ (r,F.forward y r)) = fun _ => f₀ y := by
    funext r
    exact F.particle_along f₀ r y
  change HasDerivAt (fun r => F.particle f₀ (r,F.forward y r)) _ t at hd
  rw [heq] at hd
  have hh := hd.unique (hasDerivAt_const t (f₀ y))
  simpa only [hy] using hh

lemma particle_vlasov {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (t : ℝ) (x v : Vec) :
    deriv (fun r => F.particle f₀ (r,x,v)) t +
    (∑ i : Fin 3, velocity v i * spatialPartial (fun y => F.particle f₀ (t,y,v)) x i) +
    (∑ i : Fin 3, (E (t,x)+cross (velocity v) (B (t,x))) i *
      spatialPartial (fun w => F.particle f₀ (t,x,w)) v i) = 0 := by
  have hh := F.particle_vlasov_direction hf t (x,v)
  rw [full_directional_derivative ((F.contDiff_particle hf).differentiable (by simp) _)] at hh
  exact hh

lemma particle_vlasov_within {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀)
    {t : ℝ} (ht : 0 ≤ t) (x v : Vec) :
    derivWithin (fun r => F.particle f₀ (r,x,v)) (Ici 0) t +
    (∑ i : Fin 3, velocity v i * spatialPartial (fun y => F.particle f₀ (t,y,v)) x i) +
    (∑ i : Fin 3, (E (t,x)+cross (velocity v) (B (t,x))) i *
      spatialPartial (fun w => F.particle f₀ (t,x,w)) v i) = 0 := by
  have hd : DifferentiableAt ℝ (fun r => F.particle f₀ (r,x,v)) t :=
    ((F.contDiff_particle hf).differentiable (by simp) _).comp t
      (differentiableAt_id.prodMk (differentiableAt_const (x,v)))
  rw [hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)]
  exact F.particle_vlasov hf t x v

lemma particle_local_data {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (hc : HasCompactSupport f₀) (t : ℝ) (x : Vec) :
    ∃ (U : Set (ℝ × Vec)) (K : Set Vec),
      IsOpen U ∧ IsCompact K ∧ (t,x) ∈ U ∧
      ContDiffOn ℝ ∞ (particleBySpacetime (F.particle f₀)) (U ×ˢ univ) ∧
      ∀ p ∈ U, ∀ v ∉ K, particleBySpacetime (F.particle f₀) (p,v) = 0 := by
  obtain ⟨K,hK,hzero⟩ := F.particle_compact hc (t-1) (t+1)
  let U : Set (ℝ × Vec) := {p | p.1 ∈ Ioo (t-1) (t+1)}
  refine ⟨U,Prod.snd '' K,isOpen_Ioo.preimage continuous_fst,hK.image continuous_snd,
    ⟨by linarith,by linarith⟩,((F.contDiff_particle hf).comp contDiff_reassociate).contDiffOn,?_⟩
  intro p hp v hv
  by_contra hn
  exact hv ⟨(p.2,v),hzero p.1 (Ioo_subset_Icc_self hp) (subset_tsupport _ hn),rfl⟩

lemma moment_smooth {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀) (hc : HasCompactSupport f₀)
    {w : Vec → W} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (particleMoment (F.particle f₀) w) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  obtain ⟨U,K,hU,hK,hp,hf',hz⟩ := F.particle_local_data hf hc p.1 p.2
  have hs := contDiffOn_integral_uniform_support (n:=⊤) hU hK
    (hf'.smul (hw.comp contDiff_snd).contDiffOn)
    (fun p hp v hv => by
      change particleBySpacetime (F.particle f₀) (p,v) • w v = 0
      rw [hz p hp v hv,zero_smul])
  exact hs.contDiffAt (hU.mem_nhds hp)

lemma rho_smooth {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀) (hc : HasCompactSupport f₀) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun z => F.particle f₀ (p.1,z)) p.2) := by
  convert F.moment_smooth hf hc (contDiff_const (c:=(1:ℝ))) using 1
  ext p
  simp [particleMoment,rho]

lemma current_smooth {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀) (hc : HasCompactSupport f₀) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun z => F.particle f₀ (p.1,z)) p.2) :=
  F.moment_smooth hf hc contDiff_velocity

lemma particle_moment_integrable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀) (hc : HasCompactSupport f₀)
    {w : Vec → W} (hw : Continuous w) (p : ℝ × Vec) :
    Integrable (fun v => F.particle f₀ (p.1,p.2,v) • w v) := by
  obtain ⟨U,K,hU,hK,hp,hs,hz⟩ := F.particle_local_data hf hc p.1 p.2
  have hcont : Continuous (fun v : Vec => F.particle f₀ (p.1,p.2,v)) :=
    (F.contDiff_particle hf).continuous.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  exact (hcont.smul hw).integrable_of_hasCompactSupport
    (compactSupport_of_zero_off hK (hz p hp)).smul_right

lemma current_component {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (hc : HasCompactSupport f₀) (p : ℝ × Vec) (i : Fin 3) :
    current (fun z => F.particle f₀ (p.1,z)) p.2 i =
      ∫ v : Vec, velocity v i * F.particle f₀ (p.1,p.2,v) := by
  rw [current,integral_vec_apply (F.particle_moment_integrable hf hc
    (contDiff_velocity (k:=1)).continuous p)]
  simp only [PiLp.smul_apply,smul_eq_mul,mul_comm]

lemma source_conservation {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (hc : HasCompactSupport f₀) (t : ℝ) (x : Vec) :
    dirD (fun p : ℝ × Vec => rho (fun z => F.particle f₀ (p.1,z)) p.2) (1,0) (t,x) +
      divergence (fun y => current (fun z => F.particle f₀ (t,z)) y) x = 0 := by
  obtain ⟨U,K,hU,hK,hp,hs,hz⟩ := F.particle_local_data hf hc t x
  have he := particle_number_balance_param (E (t,x)) (B (t,x)) hU hK hp
    (hs.of_le (by simp)) hz
  have hv (v : Vec) : fderiv ℝ (particleBySpacetime (F.particle f₀)) ((t,x),v)
      ((1,velocity v),E (t,x)+cross (velocity v) (B (t,x))) = 0 := by
    rw [fderiv_particleBySpacetime ((F.contDiff_particle hf).differentiable (by simp) _)]
    exact F.particle_vlasov_direction hf t (x,v)
  simp only [hv,integral_zero] at he
  apply Eq.trans _ he
  congr 1
  unfold divergence
  apply Finset.sum_congr rfl
  intro i _
  have hj : DifferentiableAt ℝ (fun p : ℝ × Vec =>
      current (fun z => F.particle f₀ (p.1,z)) p.2 i) (t,x) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp (t,x)
      ((F.current_smooth hf hc).differentiable (by simp) _)
  rw [spatialPartial_time_slice hj]
  have heq : (fun p : ℝ × Vec => current (fun z => F.particle f₀ (p.1,z)) p.2 i) =
      (fun p => ∫ v : Vec, velocity v i * particleBySpacetime (F.particle f₀) (p,v)) :=
    funext (fun p => F.current_component hf hc p i)
  rw [heq]

end SmoothLorentzFlow

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma waveK_congr_sphere {g h : Vec → ℝ} (t : ℝ) (x : Vec)
    (he : ∀ n : Sphere, g (x+t • n.1)=h (x+t • n.1)) :
    waveK g (t,x)=waveK h (t,x) := by
  simp only [waveK,sphereSum]
  congr 2
  exact integral_congr_ae (ae_of_all _ he)

lemma waveK_zero_of_sphere {g : Vec → ℝ} (t : ℝ) (x : Vec)
    (hz : ∀ n : Sphere, g (x+t • n.1)=0) : waveK g (t,x)=0 := by
  rw [waveK_congr_sphere (h:=fun _ => 0) t x hz]
  simp [waveK,sphereSum]

lemma norm_sub_radius_le (x : Vec) (r : ℝ) (n : Sphere) :
    ‖x‖-|r| ≤ ‖x+r • n.1‖ := by
  have hh := norm_sub_le (x+r • n.1) (r • n.1)
  rw [add_sub_cancel_right,norm_smul,Real.norm_eq_abs,sphere_norm,mul_one] at hh
  linarith

lemma waveK_zero_outside {g : Vec → ℝ} {R t : ℝ} {x : Vec}
    (hz : ∀ y : Vec, R < ‖y‖ → g y=0) (hx : R+|t|<‖x‖) :
    waveK g (t,x)=0 :=
  waveK_zero_of_sphere t x (fun n => hz _ (by linarith [norm_sub_radius_le x t n]))

lemma sourceWave_zero_outside {ρ : ℝ × Vec → ℝ} {R T t : ℝ} {x : Vec}
    (ht : t∈Icc 0 T) (hz : ∀ s∈Icc 0 T, ∀ y : Vec, R<‖y‖ → ρ (s,y)=0)
    (hx : R+T<‖x‖) : sourceWave ρ (t,x)=0 := by
  unfold sourceWave volterra
  rw [intervalIntegral.integral_of_le ht.1]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hs' : s∈Icc 0 t := ⟨hs.1.le,hs.2⟩
  apply waveK_zero_outside (hz s ⟨hs'.1,hs'.2.trans ht.2⟩)
  rw [abs_of_nonneg (sub_nonneg.mpr hs'.2)]
  change R+(t-s)<‖x‖
  linarith [ht.2,hs'.1]

lemma sourceField_zero_outside {J : Field} {R T t : ℝ} {x : Vec}
    (ht : t∈Icc 0 T) (hz : ∀ s∈Icc 0 T, ∀ y : Vec, R<‖y‖ → J (s,y)=0)
    (hx : R+T<‖x‖) : sourceField J (t,x)=0 := by
  ext i
  apply sourceWave_zero_outside ht (fun s hs y hy => ?_) hx
  simp only [hz s hs y hy,PiLp.zero_apply]

lemma sourceField_zero (p : ℝ × Vec) : sourceField (0:Field) p=0 := by
  ext i
  simp [sourceField,sourceWave,volterra,sourceWaveKernel,waveK,sphereSum]

lemma freeField_velocity_congr {G H H' : Vec → Vec} (t : ℝ) (x : Vec)
    (he : ∀ n : Sphere, H (x+t • n.1)=H' (x+t • n.1)) :
    freeField G H (t,x)=freeField G H' (t,x) := by
  ext i
  change freeWave (fun y => G y i) (fun y => H y i) (t,x)=
    freeWave (fun y => G y i) (fun y => H' y i) (t,x)
  unfold freeWave
  rw [waveK_congr_sphere (h:=fun y => H' y i) t x (fun n => congrArg (fun v : Vec => v i) (he n))]

lemma fderiv_zero_outside_spatial {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × Vec → W} {a b R t : ℝ} {x : Vec}
    (hz : ∀ s∈Icc a b, ∀ y : Vec, R<‖y‖ → F (s,y)=0)
    (ht : t∈Ioo a b) (hx : R<‖x‖) : fderiv ℝ F (t,x)=0 := by
  have he : F =ᶠ[𝓝 (t,x)] fun _ => (0:W) := by
    have hu : IsOpen {p : ℝ × Vec | p.1∈Ioo a b ∧ R<‖p.2‖} :=
      (isOpen_Ioo.preimage continuous_fst).inter (isOpen_lt continuous_const continuous_snd.norm)
    filter_upwards [hu.mem_nhds ⟨ht,hx⟩] with p hp
    exact hz p.1 (Ioo_subset_Icc_self hp.1) p.2 hp.2
  rw [he.fderiv_eq]
  exact fderiv_const_apply (0:W)

lemma waveGradient_zero_outside {ρ : ℝ × Vec → ℝ} {a b R t : ℝ} {x : Vec}
    (hz : ∀ s∈Icc a b, ∀ y : Vec, R<‖y‖ → ρ (s,y)=0)
    (ht : t∈Ioo a b) (hx : R<‖x‖) : waveGradient ρ (t,x)=0 := by
  ext i
  change dirD ρ (0,basis i) (t,x)=0
  simp [dirD,fderiv_zero_outside_spatial hz ht hx]

lemma spaceCurl_zero_outside {J : Field} {a b R t : ℝ} {x : Vec}
    (hz : ∀ s∈Icc a b, ∀ y : Vec, R<‖y‖ → J (s,y)=0)
    (ht : t∈Ioo a b) (hx : R<‖x‖) : spaceCurl J (t,x)=0 := by
  ext i
  simp [spaceCurl,dirD,fderiv_zero_outside_spatial hz ht hx]

namespace SmoothLorentzFlow

lemma source_spatial_support {E B : Field} (F : SmoothLorentzFlow E B)
    {f₀ : Phase → ℝ} (hc : HasCompactSupport f₀) (a b : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t∈Icc a b, ∀ x : Vec, R<‖x‖ →
      rho (fun z => F.particle f₀ (t,z)) x=0 ∧
      current (fun z => F.particle f₀ (t,z)) x=0 := by
  obtain ⟨K,hK,hz⟩ := F.particle_compact hc a b
  obtain ⟨R,hR⟩ := (hK.image continuous_fst).isBounded.exists_norm_le
  refine ⟨max R 0,le_max_right _ _,?_⟩
  intro t ht x hx
  have he (v : Vec) : F.particle f₀ (t,x,v)=0 := by
    by_contra hn
    have hh := hR x ⟨(x,v),hz t ht (subset_tsupport _ hn),rfl⟩
    exact (not_lt_of_ge (hh.trans (le_max_left _ _))) hx
  simp [rho,current,he]

end SmoothLorentzFlow

lemma maxwell_perturbation_zero_outside {E₀ B₀ : Vec → Vec}
    {ρ : ℝ × Vec → ℝ} {j : Field} {R T t : ℝ} {x : Vec}
    (hDE : ∀ y, divergence E₀ y=ρ (0,y))
    (hz : ∀ s∈Icc (-1) (T+1), ∀ y : Vec, R<‖y‖ → ρ (s,y)=0 ∧ j (s,y)=0)
    (ht : t∈Icc 0 T) (hx : R+T<‖x‖) :
    maxwellElectric E₀ B₀ ρ j (t,x)=freeMaxwellElectric E₀ B₀ (t,x) ∧
    maxwellMagnetic E₀ B₀ j (t,x)=freeMaxwellMagnetic E₀ B₀ (t,x) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0 : (0:ℝ)∈Icc (-1) (T+1) := ⟨by norm_num,by linarith⟩
  have hρz := fun s hs y hy => (hz s hs y hy).1
  have hjz := fun s hs y hy => (hz s hs y hy).2
  have hEz : sourceField (fun q => -waveGradient ρ q-dirD j (1,0) q) (t,x)=0 := by
    apply sourceField_zero_outside ht _ hx
    intro s hs y hy
    have hi : s∈Ioo (-1) (T+1) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
    simp only [waveGradient_zero_outside hρz hi hy,neg_zero,dirD,
      fderiv_zero_outside_spatial hjz hi hy,zero_apply,sub_self]
  have hEz' : sourceField (fun q =>
      -waveGradient (fun p : ℝ × Vec => divergence E₀ p.2) q-dirD (0:Field) (1,0) q) (t,x)=0 := by
    apply sourceField_zero_outside ht _ hx
    intro s hs y hy
    have hi : s∈Ioo (-1) (T+1) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have hstat : ∀ r∈Icc (-1) (T+1), ∀ z : Vec, R<‖z‖ →
        (fun p : ℝ × Vec => divergence E₀ p.2) (r,z)=0 := by
      intro r hr z hz'
      exact (hDE z).trans (hρz 0 h0 z hz')
    rw [waveGradient_zero_outside hstat hi hy]
    simp [dirD]
  have hBz : sourceField (spaceCurl j) (t,x)=0 := by
    apply sourceField_zero_outside ht _ hx
    intro s hs y hy
    exact spaceCurl_zero_outside hjz ⟨by linarith [hs.1],by linarith [hs.2]⟩ hy
  have hBz' : sourceField (spaceCurl (0:Field)) (t,x)=0 := by
    apply sourceField_zero_outside ht _ hx
    intro s hs y hy
    exact spaceCurl_zero_outside (a:=(-1)) (b:=T+1) (R:=R)
      (fun _ _ _ _ => rfl) ⟨by linarith [hs.1],by linarith [hs.2]⟩ hy
  constructor
  · simp only [maxwellElectric,freeMaxwellElectric,hEz,hEz',add_zero]
    apply freeField_velocity_congr
    intro n
    have hn : R<‖x+t • n.1‖ := by
      have hh := norm_sub_radius_le x t n
      rw [abs_of_nonneg ht.1] at hh
      linarith [ht.2]
    simp only [hjz 0 h0 _ hn,Pi.zero_apply,sub_zero]
  · simp only [maxwellMagnetic,freeMaxwellMagnetic,hBz,hBz',add_zero]

lemma TimeContinuousL2.add {F G : Field} (hF : TimeContinuousL2 F) (hG : TimeContinuousL2 G) :
    TimeContinuousL2 (fun p => F p+G p) := by
  obtain ⟨F₂,hFc,hFe⟩ := hF
  obtain ⟨G₂,hGc,hGe⟩ := hG
  refine ⟨fun t => F₂ t+G₂ t,hFc.add hGc,?_⟩
  intro t ht
  filter_upwards [Lp.coeFn_add (F₂ t) (G₂ t),hFe t ht,hGe t ht] with x he hf hg
  simpa only [Pi.add_apply,hf,hg] using he

lemma timeContinuousL2_congr {F G : Field} (hF : TimeContinuousL2 F)
    (he : ∀ t, 0 ≤ t → ∀ x, F (t,x)=G (t,x)) : TimeContinuousL2 G := by
  obtain ⟨F₂,hFc,hFe⟩ := hF
  refine ⟨F₂,hFc,fun t ht => (hFe t ht).trans ?_⟩
  exact ae_of_all _ (he t ht)

lemma timeContinuousL2_compact {F : Field} (hF : Continuous F)
    (hK : ∀ T, 0 ≤ T → ∃ K : Set Vec, IsCompact K ∧
      ∀ t∈Icc 0 T, ∀ x∉K, F (t,x)=0) : TimeContinuousL2 F := by
  have hLp (t : ℝ) (ht : 0 ≤ t) : MemLp (fun x => F (t,x)) 2 volume := by
    obtain ⟨K,hK,hz⟩ := hK t ht
    exact (hF.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
      (compactSupport_of_zero_off hK (hz t ⟨ht,le_rfl⟩))
  have he : ContinuousOn (fun t => ∫ x : Vec, ‖F (t,x)‖^2) (Ici 0) := by
    intro s hs
    change 0 ≤ s at hs
    obtain ⟨K,hK,hz⟩ := hK (s+1) (by linarith : 0 ≤ s+1)
    have hc : ContinuousOn (fun t => ∫ x : Vec, ‖F (t,x)‖^2) (Icc 0 (s+1)) :=
      continuousOn_integral_uniform_support hK (hF.norm.pow 2).continuousOn
        (fun t ht x hx => by change ‖F (t,x)‖^2=0; rw [hz t ht x hx]; simp)
    apply (hc s ⟨hs,by linarith⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_add_one s))] with t ht ht'
    exact ⟨ht,ht'.le⟩
  have hh := timeContinuousL2_of_continuous_energy (B:=0) hF continuous_const
    (fun t ht => ⟨hLp t ht,MemLp.zero⟩) (by simpa using he)
  exact hh.1

lemma maxwell_timeContinuousL2 {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j)
    (hE0 : MemLp E₀ 2 volume) (hB0 : MemLp B₀ 2 volume)
    (hDE : ∀ x, divergence E₀ x=ρ (0,x)) (hDB : ∀ x, divergence B₀ x=0)
    (hK : ∀ T, 0 ≤ T → ∃ R : ℝ, ∀ s∈Icc (-1) (T+1), ∀ y : Vec,
      R<‖y‖ → ρ (s,y)=0 ∧ j (s,y)=0) :
    TimeContinuousL2 (maxwellElectric E₀ B₀ ρ j) ∧
    TimeContinuousL2 (maxwellMagnetic E₀ B₀ j) := by
  have hh := freeMaxwell_evolution hE hB hE0 hB0 hDB
  have hEc := contDiff_maxwellElectric hE hB hρ hj
  have hBc := contDiff_maxwellMagnetic hE hB hj
  have hδEc := hEc.continuous.sub hh.1.continuous
  have hδBc := hBc.continuous.sub hh.2.1.continuous
  have hδK (T : ℝ) (hT : 0 ≤ T) : ∃ K : Set Vec, IsCompact K ∧
      ∀ t∈Icc 0 T, ∀ x∉K,
      (maxwellElectric E₀ B₀ ρ j (t,x)-freeMaxwellElectric E₀ B₀ (t,x)=0) ∧
      (maxwellMagnetic E₀ B₀ j (t,x)-freeMaxwellMagnetic E₀ B₀ (t,x)=0) := by
    obtain ⟨R,hR⟩ := hK T hT
    refine ⟨closedBall (0:Vec) (R+T),isCompact_closedBall _ _,?_⟩
    intro t ht x hx
    have hn : R+T<‖x‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hx
    obtain ⟨he,hb⟩ := maxwell_perturbation_zero_outside hDE hR ht hn
    exact ⟨sub_eq_zero.mpr he,sub_eq_zero.mpr hb⟩
  have hδE := timeContinuousL2_compact hδEc (fun T hT => by
    obtain ⟨K,hK,hz⟩ := hδK T hT
    exact ⟨K,hK,fun t ht x hx => (hz t ht x hx).1⟩)
  have hδB := timeContinuousL2_compact hδBc (fun T hT => by
    obtain ⟨K,hK,hz⟩ := hδK T hT
    exact ⟨K,hK,fun t ht x hx => (hz t ht x hx).2⟩)
  constructor
  · exact timeContinuousL2_congr (hh.2.2.2.1.add hδE) (fun _ _ _ => add_sub_cancel _ _)
  · exact timeContinuousL2_congr (hh.2.2.2.2.1.add hδB) (fun _ _ _ => add_sub_cancel _ _)

def MaxwellFor (s : Solution) : Prop := ∀ t, 0 ≤ t → ∀ x,
  dirD s.E (1,0) (t,x)=spaceCurl s.B (t,x)-current (fun z => s.f (t,z)) x ∧
  dirD s.B (1,0) (t,x)= -spaceCurl s.E (t,x) ∧
  spaceDiv s.E (t,x)=rho (fun z => s.f (t,z)) x ∧ spaceDiv s.B (t,x)=0

def TransportFor (s : Solution) (E B : Field) : Prop := ∀ t (z : Phase),
  fderiv ℝ s.f (t,z) (1,lorentzField E B (t,z))=0

theorem exists_picard_step {d : Datum} (hd : Admissible d) {E B : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    ∃ s : Solution,
      ContDiff ℝ ∞ s.f ∧ ContDiff ℝ ∞ s.E ∧ ContDiff ℝ ∞ s.B ∧
      (∀ p, 0 ≤ s.f p) ∧ CompactOnFiniteHorizons s ∧
      TimeContinuousL2 s.E ∧ TimeContinuousL2 s.B ∧
      (∀ z, s.f (0,z)=d.f₀ z) ∧ (∀ x, s.E (0,x)=d.E₀ x) ∧
      (∀ x, s.B (0,x)=d.B₀ x) ∧ MaxwellFor s ∧ TransportFor s E B := by
  obtain ⟨hf,hc,hn,hE0,hB0,hEL,hBL,hDE,hDB⟩ := hd
  obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
  let f := F.particle d.f₀
  let ρ : ℝ × Vec → ℝ := fun p => rho (fun z => f (p.1,z)) p.2
  let j : Field := fun p => current (fun z => f (p.1,z)) p.2
  have hρ : ContDiff ℝ ∞ ρ := F.rho_smooth hf hc
  have hj : ContDiff ℝ ∞ j := F.current_smooth hf hc
  have hρ0 (x : Vec) : divergence d.E₀ x=ρ (0,x) := by
    simpa only [ρ,f,F.particle_initial] using hDE x
  let s : Solution := ⟨f,maxwellElectric d.E₀ d.B₀ ρ j,maxwellMagnetic d.E₀ d.B₀ j⟩
  have hsc : ∀ t, 0<t → ∀ x, dirD ρ (1,0) (t,x)+spaceDiv j (t,x)=0 := by
    intro t ht x
    rw [spaceDiv_slice (hj.differentiable (by simp))]
    exact F.source_conservation hf hc t x
  obtain ⟨hLe,hLb⟩ := maxwell_timeContinuousL2 hE0.1 hB0.1 hρ hj hEL hBL hρ0 hDB (by
    intro T hT
    obtain ⟨R,hR,hz⟩ := F.source_spatial_support hc (-1) (T+1)
    exact ⟨R,hz⟩)
  refine ⟨s,F.contDiff_particle hf,contDiff_maxwellElectric hE0.1 hB0.1 hρ hj,
    contDiff_maxwellMagnetic hE0.1 hB0.1 hj,F.particle_nonneg hn,?_,hLe,hLb,
    F.particle_initial d.f₀,maxwellElectric_initial hE0.1,maxwellMagnetic_initial hB0.1,?_,?_⟩
  · intro T hT
    exact F.particle_compact hc 0 T
  · intro t ht x
    exact constructed_maxwell_equations hE0.1 hB0.1 hρ hj hsc hρ0 hDB ht x
  · exact F.particle_vlasov_direction hf

lemma equations_of_maxwell_transport {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hE : ContDiff ℝ ∞ s.E) (hB : ContDiff ℝ ∞ s.B)
    (hM : MaxwellFor s) (hV : TransportFor s s.E s.B) : Equations s := by
  intro t ht
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x v
    have hv := hV t (x,v)
    rw [full_directional_derivative (hf.differentiable (by simp) _)] at hv
    have hd : DifferentiableAt ℝ (fun r => s.f (r,x,v)) t :=
      (hf.differentiable (by simp) _).comp t
        (differentiableAt_id.prodMk (differentiableAt_const (x,v)))
    rw [hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)]
    exact hv
  · intro x
    rw [derivWithin_slice_eq_dirD (hE.differentiable (by simp)) ht,
      (hM t ht x).1,spaceCurl_slice (hB.differentiable (by simp))]
    module
  · intro x
    rw [derivWithin_slice_eq_dirD (hB.differentiable (by simp)) ht,
      (hM t ht x).2.1,spaceCurl_slice (hE.differentiable (by simp))]
    module
  · intro x
    rw [←spaceDiv_slice (hE.differentiable (by simp))]
    exact (hM t ht x).2.2.1
  · intro x
    rw [←spaceDiv_slice (hB.differentiable (by simp))]
    exact (hM t ht x).2.2.2

end RVM

end

end OAI
