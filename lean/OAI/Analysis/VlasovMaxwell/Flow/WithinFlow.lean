import Mathlib
import OAI.Analysis.VlasovMaxwell.Maxwell.ExtendedField
import OAI.Analysis.VlasovMaxwell.Maxwell.FiniteFlow

namespace OAI

noncomputable section

namespace RVM

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

section WithinFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def spaceDerivative (f : ℝ × E → E) (z : ℝ × E) : E →L[ℝ] E :=
  fderiv ℝ (fun x => f (z.1,x)) z.2

lemma hasFDerivAt_time_slice {f : ℝ × E → E} {T : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set E))) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    HasFDerivAt (fun y => f (t,y))
      ((fderivWithin ℝ f (Icc 0 T ×ˢ (univ : Set E)) (t,x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
  have hh := (hf.differentiableOn (by norm_num) (t,x) ⟨ht,mem_univ x⟩).hasFDerivWithinAt
  exact hh.comp_hasFDerivAt x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    (Filter.Eventually.of_forall (fun _ => ⟨ht,mem_univ _⟩))

lemma contDiffOn_spaceDerivative {f : ℝ × E → E} {T : ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E))) :
    ContDiffOn ℝ 1 (spaceDerivative f) (Icc 0 T ×ˢ (univ : Set E)) := by
  have hu : UniqueDiffOn ℝ (Icc 0 T ×ˢ (univ : Set E)) :=
    (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hh := (hf.fderivWithin hu (m := 1) (by norm_num)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ E))
  apply hh.congr
  intro z hz
  exact (hasFDerivAt_time_slice (hf.of_le (by norm_num)) hz.1 z.2).fderiv

def withinVariationalField (f : ℝ × E → E) (χ : (E →L[ℝ] E) → ℝ)
    (z : ℝ × (E × (E →L[ℝ] E))) : E × (E →L[ℝ] E) :=
  (f (z.1,z.2.1),χ z.2.2 • (spaceDerivative f (z.1,z.2.1)).comp z.2.2)

lemma contDiffOn_withinVariationalField {f : ℝ × E → E} {χ : (E →L[ℝ] E) → ℝ}
    {T : ℝ} (hT : 0 < T) (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E)))
    (hχ : ContDiff ℝ 1 χ) :
    ContDiffOn ℝ 1 (withinVariationalField f χ)
      (Icc 0 T ×ˢ (univ : Set (E × (E →L[ℝ] E)))) := by
  have hp : ContDiff ℝ 1 (fun z : ℝ × (E × (E →L[ℝ] E)) => (z.1,z.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hm : MapsTo (fun z : ℝ × (E × (E →L[ℝ] E)) => (z.1,z.2.1))
      (Icc 0 T ×ˢ (univ : Set (E × (E →L[ℝ] E)))) (Icc 0 T ×ˢ (univ : Set E)) :=
    fun _ h => ⟨h.1,mem_univ _⟩
  exact ((hf.of_le (by norm_num)).comp hp.contDiffOn hm).prodMk
    (((hχ.comp (contDiff_snd.comp contDiff_snd)).contDiffOn).smul
      (((contDiffOn_spaceDerivative hT hf).comp hp.contDiffOn hm).clm_comp
        (contDiff_snd.comp contDiff_snd).contDiffOn))

omit [NormedSpace ℝ E] in

lemma continuousOn_time_label_of_lipschitz {F : Type*} [PseudoMetricSpace F]
    {α : E → ℝ → F} {J : Set ℝ} {S : Set E} {L : ℝ≥0}
    (hc : ∀ x ∈ S, ContinuousOn (α x) J)
    (hl : ∀ t ∈ J, LipschitzOnWith L (α · t) S) :
    ContinuousOn (fun z : ℝ × E => α z.2 z.1) (J ×ˢ S) := by
  intro z hz
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,htime⟩ := Metric.continuousWithinAt_iff.mp (hc z.2 hz.2 z.1 hz.1) (ε/2) (by positivity)
  refine ⟨min δ (ε/(2*((L:ℝ)+1))),lt_min hδ (by positivity),?_⟩
  intro y hy hdist
  have hd₁ : dist y.1 z.1 < δ :=
    (le_max_left _ _).trans_lt ((show max (dist y.1 z.1) (dist y.2 z.2) < _ from hdist).trans_le (min_le_left _ _))
  have hd₂ : dist y.2 z.2 < ε/(2*((L:ℝ)+1)) :=
    (le_max_right _ _).trans_lt ((show max (dist y.1 z.1) (dist y.2 z.2) < _ from hdist).trans_le (min_le_right _ _))
  have hx : (L:ℝ)*dist y.2 z.2 < ε/2 := by
    have hh := (lt_div_iff₀ (show 0 < 2*((L:ℝ)+1) by positivity)).mp hd₂
    nlinarith [dist_nonneg (x := y.2) (y := z.2)]
  exact (dist_triangle _ (α z.2 y.1) _).trans_lt
    (add_lt_add_of_le_of_lt ((hl y.1 hy.1).dist_le_mul y.2 hy.2 z.2 hz.2)
      (htime hy.1 hd₁) |>.trans_le (by linarith))

lemma hasStrictFDerivAt_time_flow {f : ℝ × E → E} {α : E → ℝ → E}
    {A : E → ℝ → (E →L[ℝ] E)} {T r : ℝ} {x₀ x : E} {t : ℝ}
    (hf : ContinuousOn f (Icc 0 T ×ˢ (univ : Set E)))
    (hαc : ContinuousOn (fun z : ℝ × E => α z.2 z.1) (Icc 0 T ×ˢ ball x₀ r))
    (hAc : ContinuousOn (fun z : ℝ × E => A z.2 z.1) (Icc 0 T ×ˢ ball x₀ r))
    (hαd : ∀ y ∈ ball x₀ r, ∀ s ∈ Icc 0 T,
      HasDerivWithinAt (α y) (f (s,α y s)) (Icc 0 T) s)
    (hAd : ∀ s ∈ Icc 0 T, ∀ y ∈ ball x₀ r, HasFDerivAt (α · s) (A y s) y)
    (ht : t ∈ Ioo 0 T) (hx : x ∈ ball x₀ r) :
    HasStrictFDerivAt (fun z : ℝ × E => α z.2 z.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (f (t,α x t))).coprod (A x t)) (t,x) := by
  have hn : Icc 0 T ×ˢ ball x₀ r ∈ 𝓝 (t,x) :=
    prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) (isOpen_ball.mem_nhds hx)
  have hni : Ioo 0 T ×ˢ ball x₀ r ∈ 𝓝 (t,x) :=
    (isOpen_Ioo.prod isOpen_ball).mem_nhds ⟨ht,hx⟩
  have hfc : ContinuousAt (fun z : ℝ × E => f (z.1,α z.2 z.1)) (t,x) := by
    apply (hf.comp (continuousOn_fst.prodMk hαc) (fun z hz => ⟨hz.1,mem_univ _⟩)).continuousAt hn
  apply hasStrictFDerivAt_uncurry_coprod (f := fun s y => α y s) (u := (t,x))
    (f₁ := fun s y => ContinuousLinearMap.toSpanSingleton ℝ (f (s,α y s)))
    (f₂ := fun s y => A y s)
  · filter_upwards [hni] with z hz
    exact ((hαd z.2 hz.2 z.1 (Ioo_subset_Icc_self hz.1)).hasDerivAt
      (Icc_mem_nhds hz.1.1 hz.1.2)).hasFDerivAt
  · filter_upwards [hn] with z hz
    exact hAd z.1 hz.1 z.2 hz.2
  · exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).continuous.continuousAt.comp hfc
  · exact hAc.continuousAt hn

variable [FiniteDimensional ℝ E]

lemma withinVariationalField_bounded {f : ℝ × E → E} {T L K : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hb : ∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L)
    (hd : ∀ t ∈ Icc 0 T, ∀ x, ‖spaceDerivative f (t,x)‖ ≤ K)
    (χ : ContDiffBump (0 : E →L[ℝ] E)) {t : ℝ} (ht : t ∈ Icc 0 T) (z : E × (E →L[ℝ] E)) :
    ‖withinVariationalField f χ (t,z)‖ ≤ max L (K*χ.rOut) := by
  change max ‖f (t,z.1)‖ ‖χ z.2 • (spaceDerivative f (t,z.1)).comp z.2‖ ≤ _
  refine max_le ((hb t ht _).trans (le_max_left _ _)) ?_
  by_cases hz : χ z.2 = 0
  · simp only [hz,zero_smul,norm_zero]
    exact hL.trans (le_max_left _ _)
  have hnorm : ‖z.2‖ ≤ χ.rOut := by
    have hh : z.2 ∈ Metric.ball 0 χ.rOut := by rwa [← χ.support_eq]
    exact (show ‖z.2‖ < χ.rOut by simpa only [Metric.mem_ball,dist_zero_right] using hh).le
  calc
    _ = χ z.2 * ‖(spaceDerivative f (t,z.1)).comp z.2‖ := by rw [norm_smul,Real.norm_of_nonneg χ.nonneg]
    _ ≤ ‖(spaceDerivative f (t,z.1)).comp z.2‖ := mul_le_of_le_one_left (norm_nonneg _) χ.le_one
    _ ≤ ‖spaceDerivative f (t,z.1)‖ * ‖z.2‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K*χ.rOut := mul_le_mul (hd t ht _) hnorm (norm_nonneg _) hK
    _ ≤ _ := le_max_right _ _
lemma exists_within_variational_flow {f : ℝ × E → E} {T L K : ℝ}
    (hT : 0 < T) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E)))
    (hb : ∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L)
    (hd : ∀ t ∈ Icc 0 T, ∀ x, ‖spaceDerivative f (t,x)‖ ≤ K) (x₀ : E) :
    ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E), ∃ L' : ℝ≥0,
      (∀ x ∈ closedBall x₀ (1/2 : ℝ), α x 0 = x ∧ A x 0 = ContinuousLinearMap.id ℝ E ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (A x)
          ((spaceDerivative f (t,α x t)).comp (A x t)) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, α x t ∈ closedBall x₀ (L*T+1/2)) ∧
      ∀ t ∈ Icc 0 T, LipschitzOnWith L' (α · t) (closedBall x₀ (1/2 : ℝ)) ∧
        LipschitzOnWith L' (A · t) (closedBall x₀ (1/2 : ℝ)) := by
  let χ : ContDiffBump (0 : E →L[ℝ] E) :=
    ⟨Real.exp (K*T)+1,Real.exp (K*T)+2,by positivity,by linarith⟩
  let M := max L (K*χ.rOut)
  let z₀ : E × (E →L[ℝ] E) := (x₀,ContinuousLinearMap.id ℝ E)
  obtain ⟨β,L',hβ,hLip⟩ := exists_bounded_picard_flow hT.le
    (hL.trans (le_max_left L (K*χ.rOut)))
    (contDiffOn_withinVariationalField hT hf χ.contDiff)
    (fun _ ht z => withinVariationalField_bounded hL hK hb hd χ ht z) z₀
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
      HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t :=
    ((hβ _ (hmem hx)).2 t ht).fst
  have hAd {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (A x) (χ (A x t) • (spaceDerivative f (t,α x t)).comp (A x t)) (Icc 0 T) t :=
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
          _ ≤ ‖(spaceDerivative f (t,α x t)).comp (A x t)‖ := mul_le_of_le_one_left (norm_nonneg _) χ.le_one
          _ ≤ ‖spaceDerivative f (t,α x t)‖ * ‖A x t‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ K*‖A x t‖ := mul_le_mul_of_nonneg_right (hd t (Ico_subset_Icc_self ht) _) (norm_nonneg _)) t ht
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
          (fun s hs => hαd hx hs) (fun s _ => by exact_mod_cast hb s (by assumption) (α x s))
      have hh := hl.dist_le_mul t ht 0 (show 0 ∈ Icc 0 T from ⟨le_rfl,hT.le⟩)
      rw [hα₀ hx,Real.dist_eq,sub_zero,abs_of_nonneg ht.1] at hh
      change dist (α x t) x₀ ≤ L*T+1/2
      exact (dist_triangle _ x _).trans (add_le_add
        (hh.trans (mul_le_mul_of_nonneg_left ht.2 hL)) hx)
  · intro t ht
    constructor
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      exact (le_max_left _ _).trans (by
        simpa [Prod.dist_eq] using (hLip t ht).dist_le_mul _ (hmem hx) _ (hmem hy))
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      exact (le_max_right _ _).trans (by
        simpa [Prod.dist_eq] using (hLip t ht).dist_le_mul _ (hmem hx) _ (hmem hy))

lemma hasFDerivAt_within_variational_flow {f : ℝ × E → E}
    {x₀ : E} {r R T : ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E)))
    {α : E → ℝ → E} {A : E → ℝ → (E →L[ℝ] E)} {L : ℝ≥0}
    (hsol : ∀ x ∈ closedBall x₀ r, α x 0 = x ∧ A x 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt (A x)
        ((spaceDerivative f (t,α x t)).comp (A x t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, α x t ∈ closedBall x₀ R)
    (hLip : ∀ t ∈ Icc 0 T, LipschitzOnWith L (α · t) (closedBall x₀ r))
    {x : E} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasFDerivAt (fun y => α y t) (A x t) x := by
  have hx' := ball_subset_closedBall hx
  have hdf := contDiffOn_spaceDerivative hT hf
  have hsub : Icc 0 T ×ˢ closedBall x₀ R ⊆ Icc 0 T ×ˢ (univ : Set E) :=
    prod_mono Subset.rfl (subset_univ _)
  obtain ⟨LD,hLD⟩ := (hdf.mono hsub).exists_lipschitzOnWith (by norm_num)
    ((convex_Icc 0 T).prod (convex_closedBall x₀ R)) (isCompact_Icc.prod (isCompact_closedBall x₀ R))
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ R)).bddAbove_image
    (hdf.continuousOn.mono hsub).norm
  have hLDslice (s : ℝ) (hs : s ∈ Icc 0 T) :
      LipschitzOnWith LD (spaceDerivative f ∘ (fun x => (s,x))) (closedBall x₀ R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Function.comp_apply,Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist x y)]
      using hLD.dist_le_mul (s,x) ⟨hs,hx⟩ (s,y) ⟨hs,hy⟩
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
      HasDerivWithinAt (α z) (f (s,α z s)) (Ici s) s :=
    ((hsol z hz).2.2.1 s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hdA (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasDerivWithinAt (A x) ((spaceDerivative f (s,α x s)).comp (A x s)) (Ici s) s :=
    (hxs.2.2.2.1 s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hb := variational_remainder_bound (f := fun t x => f (t,x))
    (D := fun s => spaceDerivative f (s,α x s))
    (HasDerivWithinAt.continuousOn hxs.2.2.1)
    (HasDerivWithinAt.continuousOn hys.2.2.1)
    (HasDerivWithinAt.continuousOn hxs.2.2.2.1)
    (hdα x hx') (hdα y hy) hdA
    (v := y-x) (K := K) (ε := (LD : ℝ)*(L : ℝ)^2*‖y-x‖^2)
    (by simp [hxs.1,hys.1,hxs.2.1])
    (fun s hs => (hM ⟨(s,α x s),⟨Ico_subset_Icc_self hs,hxs.2.2.2.2 s (Ico_subset_Icc_self hs)⟩,rfl⟩).trans (le_max_right _ _))
    (fun s hs => ?_)
  · have hb' := hb t ht
    apply hb'.trans_eq
    rw [gronwallBound_of_K_ne_0 hK.ne']
    dsimp [C]
    ring_nf
  · have hTaylor := taylor_bound_lipschitz_derivative
      (convex_closedBall x₀ R)
      (fun z _ => (hasFDerivAt_time_slice (hf.of_le (by norm_num)) (Ico_subset_Icc_self hs) z).differentiableAt)
      (hLDslice s (Ico_subset_Icc_self hs)) (hxs.2.2.2.2 s (Ico_subset_Icc_self hs)) (hys.2.2.2.2 s (Ico_subset_Icc_self hs))
    apply hTaylor.trans
    have hn := (hLip s (Ico_subset_Icc_self hs)).norm_sub_le hy hx'
    have hsq : ‖α y s-α x s‖^2 ≤ ((L : ℝ)*‖y-x‖)^2 :=
      sq_le_sq₀ (norm_nonneg _) (mul_nonneg L.2 (norm_nonneg _)) |>.mpr hn
    calc
      _ ≤ (LD : ℝ)*((L : ℝ)*‖y-x‖)^2 := mul_le_mul_of_nonneg_left hsq LD.2
      _ = _ := by ring

lemma flow_injOn_of_within_ode {f : ℝ × E → E}
    {x₀ : E} {r R T : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set E))) {α : E → ℝ → E}
    (hinit : ∀ x ∈ closedBall x₀ r, α x 0 = x)
    (hder : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t)
    (hrange : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc 0 T, α x t ∈ closedBall x₀ R)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Set.InjOn (fun x => α x t) (closedBall x₀ r) := by
  obtain ⟨K,hK⟩ := (hf.mono (prod_mono Subset.rfl (subset_univ (closedBall x₀ R)))).exists_lipschitzOnWith
    (by norm_num) ((convex_Icc 0 T).prod (convex_closedBall x₀ R))
    (isCompact_Icc.prod (isCompact_closedBall x₀ R))
  have hKslice (s : ℝ) (hs : s ∈ Icc 0 T) :
      LipschitzOnWith K (fun x => f (s,x)) (closedBall x₀ R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist x y)]
      using hK.dist_le_mul (s,x) ⟨hs,hx⟩ (s,y) ⟨hs,hy⟩
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hd (x : E) (hx : x ∈ closedBall x₀ r) (s : ℝ) (hs : s ∈ Ioc 0 t) :
      HasDerivWithinAt (α x) (f (s,α x s)) (Iic s) s :=
    ((hder x hx s (hsub (Ioc_subset_Icc_self hs))).mono hsub).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem hs)
  intro x hx y hy heq
  have hu := ODE_solution_unique_of_mem_Icc_left
    (v := fun s x => f (s,x)) (s := fun _ => closedBall x₀ R)
    (fun s hs => hKslice s (hsub (Ioc_subset_Icc_self hs)))
    ((HasDerivWithinAt.continuousOn (hder x hx)).mono hsub) (hd x hx)
    (fun s hs => hrange x hx s (hsub (Ioc_subset_Icc_self hs)))
    ((HasDerivWithinAt.continuousOn (hder y hy)).mono hsub) (hd y hy)
    (fun s hs => hrange y hy s (hsub (Ioc_subset_Icc_self hs))) heq (show 0 ∈ Icc 0 t from ⟨le_rfl,ht.1⟩)
  simpa [hinit x hx,hinit y hy] using hu

lemma exists_bounded_within_variational_flow {f : ℝ × E → E} {T L : ℝ}
    (hT : 0 < T) (hL : 0 ≤ L)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E)))
    (hb : ∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L) (x₀ : E) :
    ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E), ∃ L' : ℝ≥0,
      (∀ x ∈ closedBall x₀ (1/2 : ℝ), α x 0 = x ∧ A x 0 = ContinuousLinearMap.id ℝ E ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (A x)
          ((spaceDerivative f (t,α x t)).comp (A x t)) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, α x t ∈ closedBall x₀ (L*T+1/2)) ∧
      ∀ t ∈ Icc 0 T, LipschitzOnWith L' (α · t) (closedBall x₀ (1/2 : ℝ)) ∧
        LipschitzOnWith L' (A · t) (closedBall x₀ (1/2 : ℝ)) := by
  let χ : ContDiffBump x₀ := ⟨L*T+1,L*T+2,by positivity,by linarith⟩
  let g : ℝ × E → E := fun z => χ z.2 • f z
  have hg : ContDiffOn ℝ 2 g (Icc 0 T ×ˢ (univ : Set E)) :=
    (χ.contDiff.comp contDiff_snd).contDiffOn.smul hf
  have hgb (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) : ‖g (t,x)‖ ≤ L := by
    change ‖χ x • f (t,x)‖ ≤ L
    rw [norm_smul,Real.norm_of_nonneg χ.nonneg]
    exact (mul_le_of_le_one_left (norm_nonneg _) χ.le_one).trans (hb t ht x)
  obtain ⟨K,hK⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ χ.rOut)).bddAbove_image
    ((contDiffOn_spaceDerivative hT hg).continuousOn.mono
      (prod_mono Subset.rfl (subset_univ _))).norm
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) : ‖spaceDerivative g (t,x)‖ ≤ max 0 K := by
    by_cases hx : x ∈ closedBall x₀ χ.rOut
    · exact (hK ⟨(t,x),⟨ht,hx⟩,rfl⟩).trans (le_max_right _ _)
    have he : (fun y => g (t,y)) =ᶠ[𝓝 x] 0 := by
      have hn : x ∉ tsupport (χ : E → ℝ) := by rwa [χ.tsupport_eq]
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      change χ y • f (t,y) = 0
      simp only [hy,Pi.zero_apply,zero_smul]
    have hzero : spaceDerivative g (t,x) = 0 := by
      change fderiv ℝ (fun y => g (t,y)) x = 0
      rw [he.fderiv_eq]
      simp
    rw [hzero,norm_zero]
    exact le_max_left _ _
  obtain ⟨α,A,L',hsol,hLip⟩ := exists_within_variational_flow hT hL
    (le_max_left 0 K) hg hgb hd x₀
  have hlocal {x : E} (hx : x ∈ closedBall x₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      (fun y => g (t,y)) =ᶠ[𝓝 (α x t)] (fun y => f (t,y)) := by
    have hm : α x t ∈ ball x₀ χ.rIn := by
      have hh := (hsol x hx).2.2.2.2 t ht
      change dist (α x t) x₀ < L*T+1
      change dist (α x t) x₀ ≤ L*T+1/2 at hh
      linarith
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hm] with y hy
    change χ y • f (t,y) = f (t,y)
    rw [hy]
    exact one_smul ℝ (f (t,y))
  refine ⟨α,A,L',?_,hLip⟩
  intro x hx
  have hh := hsol x hx
  refine ⟨hh.1,hh.2.1,?_,?_,hh.2.2.2.2⟩
  · intro t ht
    simpa only [(hlocal hx ht).eq_of_nhds] using hh.2.2.1 t ht
  · intro t ht
    have he : spaceDerivative g (t,α x t) = spaceDerivative f (t,α x t) :=
      (hlocal hx ht).fderiv_eq
    simpa only [he] using hh.2.2.2.1 t ht

lemma exists_bounded_within_volume_flow {f : ℝ × E → E} {T L : ℝ}
    (hT : 0 < T) (hL : 0 ≤ L)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E)))
    (hb : ∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L)
    (hdiv : ∀ t ∈ Icc 0 T, ∀ x, LinearMap.trace ℝ E (spaceDerivative f (t,x)).toLinearMap = 0)
    (x₀ : E) :
    ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E),
      (∀ x ∈ ball x₀ (1/2 : ℝ), α x 0 = x ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasFDerivAt (fun y => α y t) (A x t) x) ∧
        ∀ t ∈ Icc 0 T, (A x t).det = 1) ∧
      ∀ t ∈ Icc 0 T, Set.InjOn (fun x => α x t) (ball x₀ (1/2 : ℝ)) := by
  obtain ⟨α,A,L',hsol,hLip⟩ := exists_bounded_within_variational_flow hT hL hf hb x₀
  refine ⟨α,A,?_,?_⟩
  · intro x hx
    have hh := hsol x (ball_subset_closedBall hx)
    refine ⟨hh.1,hh.2.2.1,(fun _ ht => hasFDerivAt_within_variational_flow hT hf hsol
      (fun t ht => (hLip t ht).1) hx ht),?_⟩
    exact determinant_clm_eq_one_of_trace_zero hT.le
      (HasDerivWithinAt.continuousOn hh.2.2.2.1) hh.2.1
      (fun t ht => (hh.2.2.2.1 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      (fun t ht => hdiv t (Ioo_subset_Icc_self ht) _)
  · intro t ht
    exact (flow_injOn_of_within_ode (hf.of_le (by norm_num))
      (fun x hx => (hsol x hx).1) (fun x hx => (hsol x hx).2.2.1)
      (fun x hx => (hsol x hx).2.2.2.2) ht).mono ball_subset_closedBall

lemma exists_bounded_within_volume_flow_joint {f : ℝ × E → E} {T L : ℝ}
    (hT : 0 < T) (hL : 0 ≤ L)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T ×ˢ (univ : Set E)))
    (hb : ∀ t ∈ Icc 0 T, ∀ x, ‖f (t,x)‖ ≤ L)
    (hdiv : ∀ t ∈ Icc 0 T, ∀ x, LinearMap.trace ℝ E (spaceDerivative f (t,x)).toLinearMap = 0)
    (x₀ : E) :
    ∃ α : E → ℝ → E, ∃ A : E → ℝ → (E →L[ℝ] E),
      (∀ x ∈ ball x₀ (1/2 : ℝ), α x 0 = x ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α x) (f (t,α x t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasFDerivAt (fun y => α y t) (A x t) x) ∧
        (∀ t ∈ Icc 0 T, (A x t).det = 1) ∧
        ∀ t ∈ Ioo 0 T, HasStrictFDerivAt (fun z : ℝ × E => α z.2 z.1)
          ((ContinuousLinearMap.toSpanSingleton ℝ (f (t,α x t))).coprod (A x t)) (t,x)) ∧
      ∀ t ∈ Icc 0 T, Set.InjOn (fun x => α x t) (ball x₀ (1/2 : ℝ)) := by
  obtain ⟨α,A,L',hsol,hLip⟩ := exists_bounded_within_variational_flow hT hL hf hb x₀
  have hαc := continuousOn_time_label_of_lipschitz (fun x hx =>
    HasDerivWithinAt.continuousOn (hsol x hx).2.2.1) (fun t ht => (hLip t ht).1)
  have hAc := continuousOn_time_label_of_lipschitz (fun x hx =>
    HasDerivWithinAt.continuousOn (hsol x hx).2.2.2.1) (fun t ht => (hLip t ht).2)
  have hAd : ∀ t ∈ Icc 0 T, ∀ x ∈ ball x₀ (1/2 : ℝ), HasFDerivAt (α · t) (A x t) x :=
    fun _ ht _ hx => hasFDerivAt_within_variational_flow hT hf hsol (fun t ht => (hLip t ht).1) hx ht
  refine ⟨α,A,?_,?_⟩
  · intro x hx
    have hh := hsol x (ball_subset_closedBall hx)
    refine ⟨hh.1,hh.2.2.1,(fun t ht => hAd t ht x hx),?_,?_⟩
    · exact determinant_clm_eq_one_of_trace_zero hT.le
        (HasDerivWithinAt.continuousOn hh.2.2.2.1) hh.2.1
        (fun t ht => (hh.2.2.2.1 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
        (fun t ht => hdiv t (Ioo_subset_Icc_self ht) _)
    · intro t ht
      exact hasStrictFDerivAt_time_flow hf.continuousOn
        (hαc.mono (Set.prod_mono Subset.rfl ball_subset_closedBall))
        (hAc.mono (Set.prod_mono Subset.rfl ball_subset_closedBall))
        (fun y hy => (hsol y (ball_subset_closedBall hy)).2.2.1) hAd ht hx
  · intro t ht
    exact (flow_injOn_of_within_ode (hf.of_le (by norm_num))
      (fun x hx => (hsol x hx).1) (fun x hx => (hsol x hx).2.2.1)
      (fun x hx => (hsol x hx).2.2.2.2) ht).mono ball_subset_closedBall

end WithinFlow
lemma cutLorentz_regular_slab {E B : Field} {χ : Vec → ℝ} {T : ℝ}
    (hE : ContDiffOn ℝ 2 E (Icc 0 T ×ˢ (univ : Set Vec))) (hB : ContDiffOn ℝ 2 B (Icc 0 T ×ˢ (univ : Set Vec)))
    (hχ : ContDiff ℝ 2 χ) :
    ContDiffOn ℝ 2 (cutLorentz E B χ) (Icc 0 T ×ˢ (univ : Set Phase)) := by
  have hx : ContDiff ℝ 2 (fun p : ℝ × Phase => (p.1,p.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hm : MapsTo (fun p : ℝ × Phase => (p.1,p.2.1))
      (Icc 0 T ×ˢ (univ : Set Phase)) (Icc 0 T ×ˢ (univ : Set Vec)) := fun _ hp => ⟨hp.1,mem_univ _⟩
  have hu : ContDiff ℝ 2 (fun p : ℝ × Phase => velocity p.2.2) :=
    contDiff_velocity.comp (contDiff_snd.comp contDiff_snd)
  exact hu.contDiffOn.prodMk
    ((hχ.comp (contDiff_fst.comp contDiff_snd)).contDiffOn.smul
      ((hE.comp hx.contDiffOn hm).add
        (contDiff_cross.contDiffOn.comp (hu.contDiffOn.prodMk (hB.comp hx.contDiffOn hm))
          (mapsTo_univ _ _))))

lemma cutLorentz_bounded_slab {E B : Field} {T : ℝ} (_hT : 0 ≤ T) {x₀ : Vec}
    (hE : ContinuousOn E (Icc 0 T ×ˢ (univ : Set Vec))) (hB : ContinuousOn B (Icc 0 T ×ˢ (univ : Set Vec)))
    (χ : ContDiffBump x₀) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Icc 0 T, ∀ z, ‖cutLorentz E B χ (t,z)‖ ≤ L := by
  have hsub : Icc 0 T ×ˢ closedBall x₀ χ.rOut ⊆ (Icc 0 T ×ˢ (univ : Set Vec)) := fun _ hp => ⟨hp.1,mem_univ _⟩
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ χ.rOut)).bddAbove_image
    ((hE.norm.add hB.norm).mono hsub)
  refine ⟨max 1 M, (zero_le_one.trans (le_max_left _ _)),?_⟩
  intro t ht z
  rw [Prod.norm_def]
  apply max_le
  · exact (norm_velocity_lt_one z.2).le.trans (le_max_left _ _)
  change ‖χ z.1 • (E (t,z.1)+cross (velocity z.2) (B (t,z.1)))‖ ≤ max 1 M
  by_cases hχ : χ z.1 = 0
  · simp only [hχ,zero_smul,norm_zero]
    exact zero_le_one.trans (le_max_left _ _)
  have hz : z.1 ∈ closedBall x₀ χ.rOut := ball_subset_closedBall (by
    rw [← χ.support_eq]
    exact hχ)
  calc
    _ = χ z.1 * ‖E (t,z.1)+cross (velocity z.2) (B (t,z.1))‖ := by
      rw [norm_smul,Real.norm_of_nonneg χ.nonneg]
    _ ≤ ‖E (t,z.1)+cross (velocity z.2) (B (t,z.1))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) χ.le_one
    _ ≤ ‖E (t,z.1)‖+‖B (t,z.1)‖ := by
      have hc : ‖cross (velocity z.2) (B (t,z.1))‖ ≤ ‖B (t,z.1)‖ :=
        (norm_cross_le (velocity z.2) (B (t,z.1))).trans
          (mul_le_of_le_one_left (norm_nonneg (B (t,z.1))) (norm_velocity_lt_one z.2).le)
      exact (norm_add_le (E (t,z.1)) (cross (velocity z.2) (B (t,z.1)))).trans
        (add_le_add le_rfl hc)
    _ ≤ M := hM ⟨(t,z.1),⟨ht,hz⟩,rfl⟩
    _ ≤ _ := le_max_right _ _

lemma cross_smul_right (a b : Vec) (c : ℝ) : cross a (c • b) = c • cross a b := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma cutLorentz_eq_lorentzPhase (E B : Field) (χ : Vec → ℝ) (t : ℝ) :
    (fun z => cutLorentz E B χ (t,z)) =
      lorentzPhase (fun x => χ x • E (t,x)) (fun x => χ x • B (t,x)) := by
  ext z : 1
  simp only [cutLorentz,lorentzPhase,cross_smul_right,smul_add]

lemma trace_cutLorentz_slab {E B : Field} {χ : Vec → ℝ} {T : ℝ}
    (hE : ContDiffOn ℝ 1 E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContDiffOn ℝ 1 B (Icc 0 T ×ˢ (univ : Set Vec)))
    (hχ : ContDiff ℝ 1 χ) {t : ℝ} (ht : t ∈ Icc 0 T) (z : Phase) :
    LinearMap.trace ℝ Phase (spaceDerivative (cutLorentz E B χ) (t,z)).toLinearMap = 0 := by
  rw [spaceDerivative,cutLorentz_eq_lorentzPhase]
  exact trace_lorentzPhase
    ((hχ.differentiable (by norm_num)).smul (fun x => (hasFDerivAt_time_slice hE ht x).differentiableAt))
    ((hχ.differentiable (by norm_num)).smul (fun x => (hasFDerivAt_time_slice hB ht x).differentiableAt)) z

lemma exists_finite_lorentz_within_volume_flow {E B : Field} {T : ℝ} (hT : 0 < T)
    (hE : ContDiffOn ℝ 2 E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContDiffOn ℝ 2 B (Icc 0 T ×ˢ (univ : Set Vec))) (z₀ : Phase) :
    ∃ α : Phase → ℝ → Phase, ∃ A : Phase → ℝ → (Phase →L[ℝ] Phase),
      (∀ z ∈ ball z₀ (1/2 : ℝ), α z 0 = z ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α z) (lorentzField E B (t,α z t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasFDerivAt (fun y => α y t) (A z t) z) ∧
        (∀ t ∈ Icc 0 T, (A z t).det = 1) ∧
        ∀ t ∈ Ioo 0 T, HasStrictFDerivAt (fun p : ℝ × Phase => α p.2 p.1)
          ((ContinuousLinearMap.toSpanSingleton ℝ (lorentzField E B (t,α z t))).coprod (A z t)) (t,z)) ∧
      ∀ t ∈ Icc 0 T, Set.InjOn (fun z => α z t) (ball z₀ (1/2 : ℝ)) := by
  let χ : ContDiffBump z₀.1 := ⟨T+1,T+2,by linarith,by linarith⟩
  obtain ⟨L,hL,hbound⟩ := cutLorentz_bounded_slab hT.le hE.continuousOn hB.continuousOn χ
  obtain ⟨α,A,hsol,hinj⟩ := exists_bounded_within_volume_flow_joint hT hL
    (cutLorentz_regular_slab hE hB χ.contDiff) hbound
    (fun _ ht z => trace_cutLorentz_slab (hE.of_le (by norm_num)) (hB.of_le (by norm_num)) χ.contDiff ht z) z₀
  have hX {z : Phase} (hz : z ∈ ball z₀ (1/2 : ℝ)) :
      LipschitzOnWith 1 (fun t => (α z t).1) (Icc 0 T) := by
    apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => ((hsol z hz).2.1 t ht).fst)
    intro t _
    exact_mod_cast (norm_velocity_lt_one (α z t).2).le
  have hone {z : Phase} (hz : z ∈ ball z₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      χ (α z t).1 = 1 := by
    apply χ.one_of_mem_closedBall
    have hh := (hX hz).dist_le_mul t ht 0 (show 0 ∈ Icc 0 T from ⟨le_rfl,hT.le⟩)
    simp only [(hsol z hz).1,NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg ht.1] at hh
    have hz' : dist z.1 z₀.1 < (1/2 : ℝ) := (le_max_left _ _).trans_lt hz
    change dist (α z t).1 z₀.1 ≤ T+1
    exact (dist_triangle _ z.1 _).trans (add_le_add hh hz'.le) |>.trans (by linarith [ht.2])
  have heq {z : Phase} (hz : z ∈ ball z₀ (1/2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
      cutLorentz E B χ (t,α z t) = lorentzField E B (t,α z t) := by
    simp only [cutLorentz,lorentzField,lorentzPhase,hone hz ht,one_smul]
  refine ⟨α,A,?_,hinj⟩
  intro z hz
  refine ⟨(hsol z hz).1,?_,(hsol z hz).2.2.1,(hsol z hz).2.2.2.1,?_⟩
  · intro t ht
    simpa only [heq hz ht] using (hsol z hz).2.1 t ht
  · intro t ht
    simpa only [heq hz (Ioo_subset_Icc_self ht)] using (hsol z hz).2.2.2.2 t ht


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
open Set MeasureTheory Filter Metric ODE
open scoped Topology NNReal ContDiff

section SlabUniqueness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma eqOn_of_within_ode {f : ℝ × E → E} {α β : ℝ → E} {T t₀ : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set E)))
    (hα : ∀ t ∈ Icc 0 T, HasDerivWithinAt α (f (t,α t)) (Icc 0 T) t)
    (hβ : ∀ t ∈ Icc 0 T, HasDerivWithinAt β (f (t,β t)) (Icc 0 T) t)
    (ht₀ : t₀ ∈ Icc 0 T) (hinit : α t₀ = β t₀) : EqOn α β (Icc 0 T) := by
  have hαc := HasDerivWithinAt.continuousOn hα
  have hβc := HasDerivWithinAt.continuousOn hβ
  obtain ⟨R,hR⟩ := isCompact_Icc.bddAbove_image (hαc.norm.add hβc.norm)
  have hαR (t : ℝ) (ht : t ∈ Icc 0 T) : α t ∈ closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (le_add_of_nonneg_right (norm_nonneg (β t))).trans (hR ⟨t,ht,rfl⟩)
  have hβR (t : ℝ) (ht : t ∈ Icc 0 T) : β t ∈ closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (le_add_of_nonneg_left (norm_nonneg (α t))).trans (hR ⟨t,ht,rfl⟩)
  obtain ⟨K,hK⟩ := (hf.mono (prod_mono Subset.rfl (subset_univ (closedBall (0 : E) R)))).exists_lipschitzOnWith
    (by norm_num) ((convex_Icc 0 T).prod (convex_closedBall (0 : E) R))
    (isCompact_Icc.prod (isCompact_closedBall (0 : E) R))
  have hKslice (t : ℝ) (ht : t ∈ Icc 0 T) :
      LipschitzOnWith K (fun x => f (t,x)) (closedBall (0 : E) R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist x y)]
      using hK.dist_le_mul (t,x) ⟨ht,hx⟩ (t,y) ⟨ht,hy⟩
  have hl : Icc 0 t₀ ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht₀.2
  have hr : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc ht₀.1 le_rfl
  have hleft : EqOn α β (Icc 0 t₀) :=
    ODE_solution_unique_of_mem_Icc_left (v := fun t x => f (t,x)) (s := fun _ => closedBall (0 : E) R)
      (fun t ht => hKslice t (hl (Ioc_subset_Icc_self ht))) (hαc.mono hl)
      (fun t ht => ((hα t (hl (Ioc_subset_Icc_self ht))).mono hl).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht))
      (fun t ht => hαR t (hl (Ioc_subset_Icc_self ht))) (hβc.mono hl)
      (fun t ht => ((hβ t (hl (Ioc_subset_Icc_self ht))).mono hl).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht))
      (fun t ht => hβR t (hl (Ioc_subset_Icc_self ht))) hinit
  have hright : EqOn α β (Icc t₀ T) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun t x => f (t,x)) (s := fun _ => closedBall (0 : E) R)
      (fun t ht => hKslice t (hr (Ico_subset_Icc_self ht))) (hαc.mono hr)
      (fun t ht => ((hα t (hr (Ico_subset_Icc_self ht))).mono hr).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
      (fun t ht => hαR t (hr (Ico_subset_Icc_self ht))) (hβc.mono hr)
      (fun t ht => ((hβ t (hr (Ico_subset_Icc_self ht))).mono hr).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
      (fun t ht => hβR t (hr (Ico_subset_Icc_self ht))) hinit
  intro t ht
  rcases le_total t t₀ with h | h
  · exact hleft ⟨ht.1,h⟩
  · exact hright ⟨h,ht.2⟩
end SlabUniqueness

lemma contDiffOn_lorentzField_slab {E B : Field} {T : ℝ} {k : ℕ∞ω}
    (hE : ContDiffOn ℝ k E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContDiffOn ℝ k B (Icc 0 T ×ˢ (univ : Set Vec))) :
    ContDiffOn ℝ k (lorentzField E B) (Icc 0 T ×ˢ (univ : Set Phase)) := by
  have hx : ContDiff ℝ k (fun z : ℝ × Phase => (z.1,z.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hm : MapsTo (fun z : ℝ × Phase => (z.1,z.2.1))
      (Icc 0 T ×ˢ (univ : Set Phase)) (Icc 0 T ×ˢ (univ : Set Vec)) := fun _ h => ⟨h.1,mem_univ _⟩
  have hu : ContDiff ℝ k (fun z : ℝ × Phase => velocity z.2.2) :=
    contDiff_velocity.comp (contDiff_snd.comp contDiff_snd)
  exact hu.contDiffOn.prodMk ((hE.comp hx.contDiffOn hm).add
    (contDiff_cross.contDiffOn.comp (hu.contDiffOn.prodMk (hB.comp hx.contDiffOn hm)) (mapsTo_univ _ _)))

lemma exists_lorentz_ode_on_slab {E B : Field} {T t₀ : ℝ} (hT : 0 ≤ T)
    (ht₀ : t₀ ∈ Icc 0 T) (hE : ContDiffOn ℝ 2 E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContDiffOn ℝ 2 B (Icc 0 T ×ˢ (univ : Set Vec))) (z₀ : Phase) :
    ∃ α : ℝ → Phase, α t₀=z₀ ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt α (lorentzField E B (t,α t)) (Icc 0 T) t := by
  let χ : ContDiffBump z₀.1 := ⟨T+1,T+2,by linarith,by linarith⟩
  obtain ⟨L,hL,hbound⟩ := cutLorentz_bounded_slab hT hE.continuousOn hB.continuousOn χ
  obtain ⟨α,hα₀,hα⟩ := exists_bounded_ode_on_Icc hT ht₀ hL
    ((cutLorentz_regular_slab hE hB χ.contDiff).of_le (by norm_num)) hbound z₀
  have hX : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun r => (α r).1)
      (velocity (α t).2) (Icc 0 T) t := fun t ht => (hα t ht).fst
  have hLip : LipschitzOnWith 1 (fun r => (α r).1) (Icc 0 T) :=
    (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hX
      (fun t _ => by exact_mod_cast (norm_velocity_lt_one (α t).2).le)
  have hone : ∀ t ∈ Icc 0 T, χ (α t).1=1 := by
    intro t ht
    apply χ.one_of_mem_closedBall
    have hdist := hLip.dist_le_mul t ht t₀ ht₀
    simp only [hα₀,NNReal.coe_one,one_mul] at hdist
    change dist (α t).1 z₀.1 ≤ T+1
    have hd : dist t t₀ ≤ T := by
      rw [Real.dist_eq,abs_le]
      constructor <;> linarith [ht.1,ht.2,ht₀.1,ht₀.2]
    linarith
  refine ⟨α,hα₀,?_⟩
  intro t ht
  simpa only [cutLorentz,lorentzField,lorentzPhase,hone t ht,one_smul] using hα t ht

lemma exists_global_lorentz_flow_on_slab {E B : Field} {T : ℝ} (hT : 0 < T)
    (hE : ContDiffOn ℝ 2 E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContDiffOn ℝ 2 B (Icc 0 T ×ˢ (univ : Set Vec))) :
    ∃ α : Phase → ℝ → Phase, ∃ A : Phase → ℝ → (Phase →L[ℝ] Phase),
      (∀ z, α z 0 = z ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt (α z) (lorentzField E B (t,α z t)) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, HasFDerivAt (α · t) (A z t) z) ∧
        (∀ t ∈ Icc 0 T, (A z t).det = 1) ∧
        ∀ t ∈ Ioo 0 T, HasStrictFDerivAt (fun p : ℝ × Phase => α p.2 p.1)
          ((ContinuousLinearMap.toSpanSingleton ℝ (lorentzField E B (t,α z t))).coprod (A z t)) (t,z)) ∧
      ∀ t ∈ Icc 0 T, Function.Bijective (α · t) := by
  choose β D hβ _ using fun z₀ => exists_finite_lorentz_within_volume_flow hT hE hB z₀
  let α : Phase → ℝ → Phase := fun z => β z z
  let A : Phase → ℝ → (Phase →L[ℝ] Phase) := fun z => D z z
  have hmem (z : Phase) : z ∈ ball z (1/2 : ℝ) := mem_ball_self (by norm_num)
  have hinit (z : Phase) : α z 0 = z := (hβ z z (hmem z)).1
  have hder (z : Phase) : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (α z) (lorentzField E B (t,α z t)) (Icc 0 T) t := (hβ z z (hmem z)).2.1
  have hf : ContDiffOn ℝ 1 (lorentzField E B) (Icc 0 T ×ˢ (univ : Set Phase)) :=
    contDiffOn_lorentzField_slab (hE.of_le (by norm_num)) (hB.of_le (by norm_num))
  have heq (x y : Phase) (hy : y ∈ ball x (1/2 : ℝ)) : EqOn (α y) (β x y) (Icc 0 T) :=
    eqOn_of_within_ode hf (hder y) (hβ x y hy).2.1 ⟨le_rfl,hT.le⟩
      ((hinit y).trans (hβ x y hy).1.symm)
  refine ⟨α,A,?_,?_⟩
  · intro z
    refine ⟨hinit z,hder z,?_,(hβ z z (hmem z)).2.2.2.1,?_⟩
    · intro t ht
      apply ((hβ z z (hmem z)).2.2.1 t ht).congr_of_eventuallyEq
      filter_upwards [isOpen_ball.mem_nhds (hmem z)] with y hy
      exact heq z y hy ht
    · intro t ht
      have hh := (hβ z z (hmem z)).2.2.2.2 t ht
      change HasStrictFDerivAt (fun p : ℝ × Phase => α p.2 p.1) _ (t,z)
      apply hh.congr_of_eventuallyEq
      filter_upwards [(isOpen_Ioo.prod isOpen_ball).mem_nhds ⟨ht,hmem z⟩] with p hp
      exact (heq z p.2 hp.2 (Ioo_subset_Icc_self hp.1)).symm
  · intro t ht
    constructor
    · intro x y he
      have hh := eqOn_of_within_ode hf (hder x) (hder y) ht he ⟨le_rfl,hT.le⟩
      simpa only [hinit] using hh
    · intro y
      obtain ⟨γ,hγ₀,hγ⟩ := exists_lorentz_ode_on_slab hT.le ht hE hB y
      refine ⟨γ 0,?_⟩
      exact (eqOn_of_within_ode hf (hder (γ 0)) hγ ⟨le_rfl,hT.le⟩ (hinit (γ 0)) ht).trans hγ₀


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
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def timeFlowDerivative (v : E) (A : E →L[ℝ] E) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  (ContinuousLinearMap.fst ℝ ℝ E).prod
    ((ContinuousLinearMap.toSpanSingleton ℝ v).coprod A)

lemma timeFlowDerivative_det (v : E) (A : E →L[ℝ] E) :
    (timeFlowDerivative v A).det = A.det := by
  have hh := det_time_triangular (timeFlowDerivative v A).toLinearMap (by apply LinearMap.ext; intro p; rfl)
  have he : (LinearMap.snd ℝ ℝ E).comp ((timeFlowDerivative v A).toLinearMap.comp (LinearMap.inr ℝ ℝ E)) = A.toLinearMap := by
    ext x
    simp [timeFlowDerivative]
  rwa [he] at hh

lemma inverse_timeFlowDerivative {v : E} {A : E →L[ℝ] E} (hA : A.det = 1) :
    ∃ e : (ℝ × E) ≃L[ℝ] (ℝ × E), ∃ D : E →L[ℝ] E,
      (e : (ℝ × E) →L[ℝ] (ℝ × E)) = timeFlowDerivative v A ∧ D.det = 1 ∧
      (ContinuousLinearMap.snd ℝ ℝ E).comp (e.symm : (ℝ × E) →L[ℝ] (ℝ × E)) =
        (ContinuousLinearMap.toSpanSingleton ℝ (-D v)).coprod D := by
  have hdet : (timeFlowDerivative v A).toLinearMap.det = 1 := (timeFlowDerivative_det v A).trans hA
  have hunit : IsUnit (timeFlowDerivative v A).toLinearMap.det := hdet.symm ▸ isUnit_one
  let e : (ℝ × E) ≃L[ℝ] (ℝ × E) := (LinearMap.equivOfIsUnitDet hunit).toContinuousLinearEquiv
  have he : (e : (ℝ × E) →L[ℝ] (ℝ × E)) = timeFlowDerivative v A := by
    apply ContinuousLinearMap.ext
    intro z
    exact LinearMap.congr_fun (LinearMap.coe_equivOfIsUnitDet hunit) z
  have happ (z : ℝ × E) : e z = (z.1,z.1 • v+A z.2) := by
    rw [← ContinuousLinearEquiv.coe_coe,he]
    rfl
  have hfst (z : ℝ × E) : (e.symm z).1 = z.1 := by
    have hh := congrArg Prod.fst (e.apply_symm_apply z)
    simpa only [happ] using hh
  let D : E →L[ℝ] E := (ContinuousLinearMap.snd ℝ ℝ E).comp
    ((e.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp (ContinuousLinearMap.inr ℝ ℝ E))
  have hD : D.det = 1 := by
    have hh := det_time_triangular (e.symm : (ℝ × E) →L[ℝ] (ℝ × E)).toLinearMap (by apply LinearMap.ext; intro z; exact hfst z)
    change (e.symm : (ℝ × E) →L[ℝ] (ℝ × E)).det = D.det at hh
    rw [ContinuousLinearEquiv.det_coe_symm,he,timeFlowDerivative_det,hA,inv_one] at hh
    exact hh.symm
  have hi : e.symm (1,v) = (1,0) := by
    apply e.injective
    simp only [e.apply_symm_apply,happ,one_smul,map_zero,add_zero]
  refine ⟨e,D,he,hD,?_⟩
  apply ContinuousLinearMap.ext
  intro p
  change (e.symm p).2 = p.1 • (-D v)+D p.2
  have hp : p = p.1 • (1,v)+(0,p.2-p.1 • v) := by
    ext <;> simp
  calc
    (e.symm p).2 = (e.symm (p.1 • (1,v)+(0,p.2-p.1 • v))).2 := congrArg (fun z => (e.symm z).2) hp
    _ = D (p.2-p.1 • v) := by
      rw [map_add,map_smul,hi]
      change p.1 • (0 : E)+(e.symm (0,p.2-p.1 • v)).2 = D (p.2-p.1 • v)
      rw [smul_zero,zero_add]
      rfl
    _ = p.1 • (-D v)+D p.2 := by simp only [map_sub,map_smul,smul_neg]; abel

omit [FiniteDimensional ℝ E] in

def inversePhase (α : E → ℝ → E) (z : ℝ × E) : E := Function.invFun (α · z.1) z.2

lemma hasStrictFDerivAt_inversePhase {α : E → ℝ → E} {v x : E} {A : E →L[ℝ] E} {T t : ℝ}
    (hbij : ∀ s ∈ Ioo 0 T, Function.Bijective (α · s)) (ht : t ∈ Ioo 0 T)
    (hA : A.det = 1)
    (hα : HasStrictFDerivAt (fun z : ℝ × E => α z.2 z.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ v).coprod A) (t,x)) :
    ∃ D : E →L[ℝ] E, D.det = 1 ∧
      HasStrictFDerivAt (inversePhase α)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-D v)).coprod D) (t,α x t) := by
  obtain ⟨e,D,he,hD,hder⟩ := inverse_timeFlowDerivative hA
  let Φ : ℝ × E → ℝ × E := fun z => (z.1,α z.2 z.1)
  have hΦ : HasStrictFDerivAt Φ (e : (ℝ × E) →L[ℝ] (ℝ × E)) (t,x) := by
    rw [he]
    exact hasStrictFDerivAt_fst.prodMk hα
  let Z := hΦ.localInverse Φ e (t,x)
  have hZ : HasStrictFDerivAt Z (e.symm : (ℝ × E) →L[ℝ] (ℝ × E)) (t,α x t) := hΦ.to_localInverse
  have hEq : (fun z => (Z z).2) =ᶠ[𝓝 (t,α x t)] inversePhase α := by
    have htime : ∀ᶠ z : ℝ × E in 𝓝 (t,α x t), z.1 ∈ Ioo 0 T :=
      continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds ht)
    filter_upwards [hΦ.eventually_right_inverse,htime] with z hz hzt
    have hf : (Z z).1 = z.1 := by
      have hh := congrArg Prod.fst hz
      exact hh
    have hy : α (Z z).2 z.1 = z.2 := by
      have hh := congrArg Prod.snd hz
      change α (Z z).2 (Z z).1 = z.2 at hh
      rwa [hf] at hh
    apply (hbij z.1 hzt).1
    exact hy.trans (Function.invFun_eq ((hbij z.1 hzt).2 z.2)).symm
  refine ⟨D,hD,?_⟩
  rw [← hder]
  exact hZ.snd.congr_of_eventuallyEq hEq

lemma determinant_retarded_graph {D : E →L[ℝ] E} (hD : D.det = 1) (v : E) (ℓ : E →L[ℝ] ℝ) :
    (D.comp ((ContinuousLinearMap.id ℝ E) - (ContinuousLinearMap.toSpanSingleton ℝ v).comp ℓ)).det =
      1 - ℓ v := by
  have he : (((ContinuousLinearMap.id ℝ E) - (ContinuousLinearMap.toSpanSingleton ℝ v).comp ℓ) : E →L[ℝ] E).toLinearMap =
      LinearMap.transvection ℓ.toLinearMap (-v) := by
    ext x
    simp [LinearMap.transvection,sub_eq_add_neg]
  change LinearMap.det (D.toLinearMap.comp _) = _
  rw [LinearMap.det_comp,he]
  change D.det * _ = _
  rw [hD,one_mul,LinearMap.transvection.det,map_neg]
  rfl

end

open Set MeasureTheory Filter
open scoped Topology ContDiff


lemma hasStrictFDerivAt_norm_nonzero {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {x : F} (hx : x ≠ 0) :
    HasStrictFDerivAt (fun y : F => ‖y‖) (innerSL ℝ (‖x‖⁻¹ • x)) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hh := (Real.hasStrictDerivAt_sqrt (pow_ne_zero 2 hn)).comp_hasStrictFDerivAt x
    (hasStrictFDerivAt_norm_sq x)
  have hf : (Real.sqrt ∘ fun y : F => ‖y‖^2) = fun y : F => ‖y‖ := by
    funext y
    exact Real.sqrt_sq (norm_nonneg y)
  rw [hf,Real.sqrt_sq (norm_nonneg x)] at hh
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro y
  simp only [smul_apply,innerSL_apply_apply,inner_smul_left,
    starRingEnd_apply,star_trivial,smul_eq_mul,two_smul,add_apply]
  ring

def coneCovector (x y : Vec) : Phase →L[ℝ] ℝ :=
  (innerSL ℝ (‖x-y‖⁻¹ • (x-y))).comp (ContinuousLinearMap.fst ℝ Vec Vec)

lemma coneCovector_apply (x y : Vec) (z : Phase) :
    coneCovector x y z = dot (‖x-y‖⁻¹ • (x-y)) z.1 := by
  rw [dot_eq_inner]
  rfl

lemma hasStrictFDerivAt_retarded_time (t : ℝ) (x : Vec) {z : Phase} (hx : x ≠ z.1) :
    HasStrictFDerivAt (fun y : Phase => t-‖x-y.1‖) (coneCovector x z.1) z := by
  have hn := (hasStrictFDerivAt_norm_nonzero (sub_ne_zero.mpr hx)).comp z
    ((hasStrictFDerivAt_const x z).sub hasStrictFDerivAt_fst)
  have hh := (hasStrictFDerivAt_const t z).sub hn
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro y
  simp [coneCovector]

lemma norm_coneDirection {x y : Vec} (hxy : x ≠ y) : ‖‖x-y‖⁻¹ • (x-y)‖ = 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)

lemma cone_deficit_positive {x y : Vec} (hxy : x ≠ y) (v : Vec) :
    0 < 1 - dot (‖x-y‖⁻¹ • (x-y)) (velocity v) := by
  have hh := real_inner_le_norm (‖x-y‖⁻¹ • (x-y)) (velocity v)
  rw [norm_coneDirection hxy,one_mul,← dot_eq_inner] at hh
  linarith [norm_velocity_lt_one v]


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
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff


section HaarFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurePreserving_of_bijective_det_one {f : E → E} {f' : E → (E →L[ℝ] E)}
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hbij : Function.Bijective f) (hdet : ∀ x, (f' x).det = 1) :
    MeasurePreserving f μ μ := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  refine ⟨hc.measurable,?_⟩
  have hh := map_withDensity_abs_det_fderiv_eq_addHaar μ (s := univ)
    MeasurableSet.univ.nullMeasurableSet (fun x _ => (hf x).hasFDerivWithinAt) hbij.1.injOn
  simp only [Measure.restrict_univ,hdet,abs_one,ENNReal.ofReal_one,
    Set.image_univ,hbij.2.range_eq] at hh
  change Measure.map f (μ.withDensity 1) = μ at hh
  simpa only [withDensity_one] using hh

lemma integral_eq_integral_comp_of_bijective_det_one {f : E → E} {f' : E → (E →L[ℝ] E)}
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hbij : Function.Bijective f) (hdet : ∀ x, (f' x).det = 1)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) :
    ∫ x, g x ∂μ = ∫ x, g (f x) ∂μ := by
  have hh := integral_image_eq_integral_abs_det_fderiv_smul μ (s := univ) MeasurableSet.univ
    (fun x _ => (hf x).hasFDerivWithinAt) hbij.1.injOn g
  simpa only [Set.image_univ,hbij.2.range_eq,setIntegral_univ,hdet,abs_one,one_smul] using hh
end HaarFlow

structure PhaseFlowOn (E B : Field) (T : ℝ) where
  flow : Phase → ℝ → Phase
  differential : Phase → ℝ → (Phase →L[ℝ] Phase)
  initial : ∀ z, flow z 0 = z
  ode : ∀ z t, t ∈ Icc 0 T →
    HasDerivWithinAt (flow z) (lorentzField E B (t,flow z t)) (Icc 0 T) t
  label : ∀ z t, t ∈ Icc 0 T → HasFDerivAt (flow · t) (differential z t) z
  det_one : ∀ z t, t ∈ Icc 0 T → (differential z t).det=1
  joint : ∀ z t, t ∈ Ioo 0 T → HasStrictFDerivAt (fun p : ℝ × Phase => flow p.2 p.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (lorentzField E B (t,flow z t))).coprod
        (differential z t)) (t,z)
  bijective : ∀ t, t ∈ Icc 0 T → Function.Bijective (flow · t)

lemma exists_phaseFlowOn {E B : Field} {T : ℝ} (hT : 0 < T)
    (hE : ContDiffOn ℝ 2 E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContDiffOn ℝ 2 B (Icc 0 T ×ˢ (univ : Set Vec))) :
    Nonempty (PhaseFlowOn E B T) := by
  obtain ⟨α,A,hα,hbij⟩ := exists_global_lorentz_flow_on_slab hT hE hB
  exact ⟨⟨α,A,fun z => (hα z).1,fun z => (hα z).2.1,fun z => (hα z).2.2.1,
    fun z => (hα z).2.2.2.1,fun z => (hα z).2.2.2.2,hbij⟩⟩

instance phaseVolume_isAddHaarMeasure : (volume : Measure Phase).IsAddHaarMeasure := by
  change (volume.prod volume : Measure Phase).IsAddHaarMeasure
  infer_instance

lemma PhaseFlowOn.measurePreserving {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) : MeasurePreserving (F.flow · t) :=
  measurePreserving_of_bijective_det_one volume (fun z => F.label z t ht)
    (F.bijective t ht) (fun z => F.det_one z t ht)

lemma PhaseFlowOn.integral_comp {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : Phase → G) :
    ∫ z, g (F.flow z t) = ∫ z, g z :=
  (integral_eq_integral_comp_of_bijective_det_one volume (fun z => F.label z t ht)
    (F.bijective t ht) (fun z => F.det_one z t ht) g).symm

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal


lemma PhaseFlowOn.continuousOn_time {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (z : Phase) : ContinuousOn (F.flow z) (Icc 0 T) :=
  fun t ht => (F.ode z t ht).continuousWithinAt

lemma PhaseFlowOn.timelike {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (z : Phase) :
    ∃ c : ℝ≥0, (c : ℝ) < 1 ∧ LipschitzOnWith c (fun t => (F.flow z t).1) (Icc 0 T) := by
  have hc : ContinuousOn (fun t => ‖velocity (F.flow z t).2‖) (Icc 0 T) :=
    ((contDiff_velocity (k := 1)).continuous.comp_continuousOn (F.continuousOn_time z).snd).norm
  obtain ⟨t₀,ht₀,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) hc
  refine ⟨⟨‖velocity (F.flow z t₀).2‖,norm_nonneg _⟩,norm_velocity_lt_one _,?_⟩
  apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (F.ode z t ht).fst)
  intro t ht
  exact_mod_cast hmax ht

lemma PhaseFlowOn.emission_strictMono {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (z : Phase) (x : Vec) :
    StrictMonoOn (fun s => s+‖x-(F.flow z s).1‖) (Icc 0 T) := by
  obtain ⟨c,hc,hLip⟩ := F.timelike hT z
  intro a ha b hb hab
  have hbound := hLip.dist_le_mul a ha b hb
  rw [dist_eq_norm,Real.dist_eq,abs_of_neg (sub_neg.mpr hab)] at hbound
  have hn : ‖x-(F.flow z a).1‖ ≤ ‖(F.flow z a).1-(F.flow z b).1‖ + ‖x-(F.flow z b).1‖ := by
    calc
      _ = ‖((F.flow z b).1-(F.flow z a).1)+(x-(F.flow z b).1)‖ := by congr 1; abel
      _ ≤ ‖(F.flow z b).1-(F.flow z a).1‖ + ‖x-(F.flow z b).1‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  have hp := mul_pos (sub_pos.mpr hc) (sub_pos.mpr hab)
  nlinarith

lemma PhaseFlowOn.inversePhase_flow {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) : inversePhase F.flow (s,F.flow z s) = z :=
  Function.leftInverse_invFun (F.bijective s hs).1 z

lemma PhaseFlowOn.flow_inversePhase {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) : F.flow (inversePhase F.flow (s,z)) s = z :=
  Function.invFun_eq ((F.bijective s hs).2 z)

lemma PhaseFlowOn.tip_null {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (x : Vec) : volume {z : Phase | (F.flow z t).1=x} = 0 := by
  have hz : (volume : Measure Phase) ({x} ×ˢ univ) = 0 := by
    change (volume.prod volume) ({x} ×ˢ (univ : Set Vec)) = 0
    rw [Measure.prod_prod,measure_singleton,zero_mul]
  have he : (F.flow · t) ⁻¹' ({x} ×ˢ univ) = {z : Phase | (F.flow z t).1=x} := by
    ext z
    simp
  rw [← he]
  exact (F.measurePreserving ht).preimage_null hz

open Set MeasureTheory Filter
open scoped Topology ContDiff


def retardedLabel (α : Phase → ℝ → Phase) (t : ℝ) (x : Vec) (z : Phase) : Phase :=
  inversePhase α (t-‖x-z.1‖,z)

lemma PhaseFlowOn.inverse_differential {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Ioo 0 T) (z : Phase) :
    ∃ D : Phase →L[ℝ] Phase, D.det=1 ∧
      HasStrictFDerivAt (inversePhase F.flow)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-D (lorentzField E B (s,z)))).coprod D) (s,z) := by
  let y := Function.invFun (F.flow · s) z
  have hy : F.flow y s=z := Function.invFun_eq ((F.bijective s (Ioo_subset_Icc_self hs)).2 z)
  have hh := hasStrictFDerivAt_inversePhase
    (fun r hr => F.bijective r (Ioo_subset_Icc_self hr)) hs
    (F.det_one y s (Ioo_subset_Icc_self hs)) (F.joint y s hs)
  simpa only [hy] using hh

lemma PhaseFlowOn.retarded_differential {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (x : Vec) (z : Phase) (hs : t-‖x-z.1‖ ∈ Ioo 0 T) (hx : x ≠ z.1) :
    ∃ D : Phase →L[ℝ] Phase, D.det=1 ∧
      HasStrictFDerivAt (retardedLabel F.flow t x)
        (D.comp ((ContinuousLinearMap.id ℝ Phase) -
          (ContinuousLinearMap.toSpanSingleton ℝ (lorentzField E B (t-‖x-z.1‖,z))).comp
            (coneCovector x z.1))) z := by
  obtain ⟨D,hD,hi⟩ := F.inverse_differential hs z
  have hg := (hasStrictFDerivAt_retarded_time t x hx).prodMk (hasStrictFDerivAt_id z)
  have hh := HasStrictFDerivAt.comp (f := fun y : Phase => (t-‖x-y.1‖,y)) z hi hg
  refine ⟨D,hD,?_⟩
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro y
  simp [map_smul,sub_eq_add_neg,add_comm]

lemma PhaseFlowOn.retarded_jacobian {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (x : Vec) (z : Phase) (hs : t-‖x-z.1‖ ∈ Ioo 0 T) (hx : x ≠ z.1) :
    (fderiv ℝ (retardedLabel F.flow t x) z).det =
      1-dot (‖x-z.1‖⁻¹ • (x-z.1)) (velocity z.2) := by
  obtain ⟨D,hD,hd⟩ := F.retarded_differential x z hs hx
  rw [hd.hasFDerivAt.fderiv,determinant_retarded_graph hD,coneCovector_apply]
  rfl

lemma PhaseFlowOn.retarded_jacobian_pos {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (x : Vec) (z : Phase) (hs : t-‖x-z.1‖ ∈ Ioo 0 T) (hx : x ≠ z.1) :
    0 < (fderiv ℝ (retardedLabel F.flow t x) z).det := by
  rw [F.retarded_jacobian x z hs hx]
  exact cone_deficit_positive hx z.2

end RVM

end

end OAI
