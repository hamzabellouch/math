import Mathlib
import OAI.Geometry.BallPacking.Normal.CompactUniformCentral
import OAI.Geometry.BallPacking.Moser.SmoothManifoldIntegral

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem euclideanPullback_exact_time
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (h : ManifoldMoserData Ω α) {g : F → M} {p : ℝ × F}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) (ht : p.1 ∈ Icc (0:ℝ) 1) (v w : F) :
    fderiv ℝ (euclideanPullbackTwoForm Ω g) p (1,0) v w =
      fderiv ℝ (euclideanPullbackOneForm α g) p (0,v) w -
      fderiv ℝ (euclideanPullbackOneForm α g) p (0,w) v := by
  let c := g p.2
  let g' := extChartAt 𝓘(ℝ,E) c ∘ g
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ g' p.2 := hch.contDiffAt
  have hp : (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) ∈ 𝓝 (p.1,g' p.2) :=
    (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) c).map_source hc⟩
  have he := timePullback_exact_time ((h.smooth_two c).contDiffAt hp)
    ((h.smooth_one c).contDiffAt hp) hs
      (h.exact_time p.1 ht c (g' p.2) ((extChartAt 𝓘(ℝ,E) c).map_source hc)) v w
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  have heΩ : euclideanPullbackTwoForm Ω g =ᶠ[𝓝 p]
      timePullbackTwoForm (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) g' := by
    filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
      continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
    exact euclideanPullbackTwoForm_chart (p := q) (hq.mdifferentiableAt (by simp)) hqc
  have heα : euclideanPullbackOneForm α g =ᶠ[𝓝 p]
      timePullbackOneForm (fun q : ℝ × E => chartOneForm (α q.1) c q.2) g' := by
    filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
      continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
    exact euclideanPullbackOneForm_chart (p := q) (hq.mdifferentiableAt (by simp)) hqc
  rw [heΩ.fderiv_eq,heα.fderiv_eq]
  exact he

variable {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem manifoldPullback_exact_time
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (h : ManifoldMoserData Ω α) {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    {c : N} {y : F} (hy : y ∈ (extChartAt 𝓘(ℝ,F) c).target) (v w : F) :
    fderiv ℝ (fun q : ℝ × F => chartTwoForm (manifoldPullbackTwoForm Ω e q.1) c q.2)
      (t,y) (1,0) v w =
    fderiv ℝ (fun q : ℝ × F => chartOneForm (manifoldPullbackOneForm α e q.1) c q.2)
      (t,y) (0,v) w -
    fderiv ℝ (fun q : ℝ × F => chartOneForm (manifoldPullbackOneForm α e q.1) c q.2)
      (t,y) (0,w) v := by
  have hg := he.contMDiffAt.comp y ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hy))
  have htarg : ∀ᶠ q : ℝ × F in 𝓝 (t,y), q.2 ∈ (extChartAt 𝓘(ℝ,F) c).target :=
    continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hy)
  have hΩ : (fun q : ℝ × F => chartTwoForm (manifoldPullbackTwoForm Ω e q.1) c q.2) =ᶠ[𝓝 (t,y)]
      euclideanPullbackTwoForm Ω (e ∘ (extChartAt 𝓘(ℝ,F) c).symm) := by
    filter_upwards [htarg] with q hq
    exact chartTwoForm_manifoldPullback (p := q) he hq
  have hα : (fun q : ℝ × F => chartOneForm (manifoldPullbackOneForm α e q.1) c q.2) =ᶠ[𝓝 (t,y)]
      euclideanPullbackOneForm α (e ∘ (extChartAt 𝓘(ℝ,F) c).symm) := by
    filter_upwards [htarg] with q hq
    exact chartOneForm_manifoldPullback (p := q) he hq
  rw [hΩ.fderiv_eq,hα.fderiv_eq]
  exact euclideanPullback_exact_time h hg ht v w

end
section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

namespace SmoothCircleAction
variable (A : SmoothCircleAction E M)

theorem chart_averageOneForm_fderiv {α : ℝ → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) {c : M} {p : ℝ × E}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) (v : ℝ × E) (w : E) :
    fderiv ℝ (fun q : ℝ × E => chartOneForm (A.averageOneForm α q.1) c q.2) p v w =
      ∫ s in (0:ℝ)..1, fderiv ℝ (fun q : ℝ × E =>
        chartOneForm (parameterPullbackOneForm (F := E) α A.toFun s q.1) c q.2) p v w := by
  have hf := parameterPullbackOneForm_smooth (E := E) (F := E) A.smooth hα c
  have hU := (isOpen_univ (X := ℝ)).prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)
  have he : (fun q : ℝ × E => chartOneForm (A.averageOneForm α q.1) c q.2) =
      (fun q => ∫ s in (0:ℝ)..1, chartOneForm (parameterPullbackOneForm (F := E) α A.toFun s q.1) c q.2) := by
    funext q
    exact A.chart_averageOneForm hα q.1 c q.2
  rw [he,(hasFDerivAt_fixed_integral_on hU hf ⟨mem_univ _,hp⟩).fderiv]
  have hD := continuous_at_fixed_fiber_derivative hU hf ⟨mem_univ _,hp⟩
  rw [ContinuousLinearMap.intervalIntegral_apply (hD.intervalIntegrable 0 1),
    ContinuousLinearMap.intervalIntegral_apply
      ((hD.clm_apply continuous_const).intervalIntegrable 0 1)]

theorem averaged_moser_data {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (h : ManifoldMoserData Ω α)
    (hΩ : ∀ s t x, (Ω t (A.slice s x)).bilinearComp (A.differential s x) (A.differential s x) = Ω t x) :
    ManifoldMoserData Ω (A.averageOneForm α) := by
  refine ⟨h.smooth_two,A.averageOneForm_smooth h.smooth_one,h.nondegenerate,h.skew,h.closed,?_⟩
  intro t ht c y hy v w
  have hpb (s : ℝ) : manifoldPullbackTwoForm (F := E) Ω (A.slice s) = Ω := by
    funext r x
    exact hΩ s r x
  have he (s : ℝ) := manifoldPullback_exact_time h (A.slice_smooth s) ht hy v w
  simp only [hpb] at he
  have hf := parameterPullbackOneForm_smooth (E := E) (F := E) A.smooth h.smooth_one c
  have hU := (isOpen_univ (X := ℝ)).prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)
  have hD := continuous_at_fixed_fiber_derivative hU hf (x := (t,y)) ⟨mem_univ _,hy⟩
  have hiv : IntervalIntegrable (fun s => fderiv ℝ (fun q : ℝ × E =>
      chartOneForm (parameterPullbackOneForm (F := E) α A.toFun s q.1) c q.2) (t,y) (0,v) w) volume 0 1 :=
    ((hD.clm_apply continuous_const).clm_apply continuous_const).intervalIntegrable 0 1
  have hiw : IntervalIntegrable (fun s => fderiv ℝ (fun q : ℝ × E =>
      chartOneForm (parameterPullbackOneForm (F := E) α A.toFun s q.1) c q.2) (t,y) (0,w) v) volume 0 1 :=
    ((hD.clm_apply continuous_const).clm_apply continuous_const).intervalIntegrable 0 1
  rw [A.chart_averageOneForm_fderiv h.smooth_one hy,A.chart_averageOneForm_fderiv h.smooth_one hy,
    ←intervalIntegral.integral_sub hiv hiw]
  have hh : (fun s =>
      fderiv ℝ (fun q : ℝ × E => chartOneForm (parameterPullbackOneForm (F := E) α A.toFun s q.1) c q.2) (t,y) (0,v) w -
      fderiv ℝ (fun q : ℝ × E => chartOneForm (parameterPullbackOneForm (F := E) α A.toFun s q.1) c q.2) (t,y) (0,w) v) =
      (fun _ : ℝ => fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (1,0) v w) := by
    funext s
    exact (he s).symm
  rw [hh]
  simp

end SmoothCircleAction

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem nonautonomous_curve_lift
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2} {γ : ℝ → M} {t : ℝ}
    (hγ : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,γ t)))) :
    HasMFDerivAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (fun s => (s,γ s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (timeLiftField (fun _ => 1) V (t,γ t))) := by
  apply ((hasMFDerivAt_id (I := 𝓘(ℝ,ℝ)) t).prodMk hγ).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change (a,a • V (t,γ t)) = a • ((1:ℝ) • ((1:ℝ),V (t,γ t)))
  simp only [one_smul,Prod.smul_mk,smul_eq_mul,mul_one]

variable [T2Space M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem nonautonomous_curve_eqOn
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) {γ δ : ℝ → M}
    (hγ : ∀ t ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,γ t))))
    (hδ : ∀ t ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) δ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,δ t))))
    (h0 : γ t₀ = δ t₀) : EqOn γ δ (Ioo a b) := by
  have hγl : IsMIntegralCurveOn (fun t => (t,γ t)) (timeLiftField (fun _ => 1) V) (Ioo a b) :=
    fun t ht => (nonautonomous_curve_lift (hγ t ht)).hasMFDerivWithinAt
  have hδl : IsMIntegralCurveOn (fun t => (t,δ t)) (timeLiftField (fun _ => 1) V) (Ioo a b) :=
    fun t ht => (nonautonomous_curve_lift (hδ t ht)).hasMFDerivWithinAt
  have he := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀
    ((timeLiftField_smooth contDiff_const hV).of_le (by simp)) hγl hδl (by rw [h0])
  intro t ht
  exact congrArg Prod.snd (he ht)

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem related_nonautonomous_curve
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    {W : (p : ℝ × N) → TangentSpace 𝓘(ℝ,F) p.2}
    {e : N → M} (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    {γ : ℝ → N} {t : ℝ}
    (hγ : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,F) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (W (t,γ t))))
    (hrel : mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e (γ t) (W (t,γ t)) = V (t,e (γ t))) :
    HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (e ∘ γ) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,e (γ t)))) := by
  apply (((he.mdifferentiable (by simp) _).hasMFDerivAt).comp t hγ).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e (γ t) (a • W (t,γ t)) = a • V (t,e (γ t))
  rw [ContinuousLinearMap.map_smul,hrel]

variable [T2Space M]

omit [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem related_nonautonomous_flow
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    {W : (p : ℝ × N) → TangentSpace 𝓘(ℝ,F) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {e : N → M} (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    {Φ : ℝ × M → M} {Θ : ℝ × N → N}
    (hΦ : ∀ x t, t ∈ Ioo (-2:ℝ) 2 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
      (fun s => Φ (s,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,Φ (t,x)))))
    (hΘ : ∀ x t, t ∈ Ioo (-2:ℝ) 2 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,F)
      (fun s => Θ (s,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (W (t,Θ (t,x)))))
    (hΦ0 : ∀ x, Φ (0,x) = x) (hΘ0 : ∀ x, Θ (0,x) = x)
    (hrel : ∀ t ∈ Ioo (-2:ℝ) 2, ∀ x,
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e x (W (t,x)) = V (t,e x)) :
    ∀ t ∈ Ioo (-2:ℝ) 2, ∀ x, Φ (t,e x) = e (Θ (t,x)) := by
  intro t ht x
  exact nonautonomous_curve_eqOn hV (by norm_num : (0:ℝ) ∈ Ioo (-2:ℝ) 2)
    (fun s hs => hΦ (e x) s hs)
    (fun s hs => related_nonautonomous_curve he (hΘ x s hs) (hrel s hs (Θ (s,x))))
    (by simp only [Function.comp_apply,hΦ0,hΘ0]) ht

variable [FiniteDimensional ℝ F] [T2Space N] [CompactSpace N]

theorem compact_related_flow_preserves_range
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    {W : (p : ℝ × N) → TangentSpace 𝓘(ℝ,F) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (hW : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,F)) (𝓘(ℝ,F)).tangent ∞
      (fun p => (⟨p.2,W p⟩ : TangentBundle 𝓘(ℝ,F) N)))
    {e : N → M} (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    {Φ : ℝ × M → M}
    (hΦ : ∀ x t, t ∈ Ioo (-2:ℝ) 2 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
      (fun s => Φ (s,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,Φ (t,x)))))
    (hΦ0 : ∀ x, Φ (0,x) = x)
    (hrel : ∀ t ∈ Ioo (-2:ℝ) 2, ∀ x,
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e x (W (t,x)) = V (t,e x)) :
    ∀ t ∈ Icc (0:ℝ) 1, (fun x => Φ (t,x)) '' range e = range e := by
  obtain ⟨Θ,Λ,_,_,hΘ0,hinv,hΘ,_⟩ := exists_nonautonomous_manifold_flow hW
  intro t ht
  have ht' : t ∈ Ioo (-2:ℝ) 2 := by constructor <;> linarith [ht.1,ht.2]
  have hn := related_nonautonomous_flow hV he hΦ hΘ hΦ0 hΘ0 hrel t ht'
  apply Subset.antisymm
  · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    change Φ (t,e x) ∈ range e
    rw [hn]
    exact mem_range_self _
  · rintro _ ⟨x,rfl⟩
    exact ⟨e (Λ (t,x)),mem_range_self _,by change Φ (t,e (Λ (t,x))) = e x; rw [hn,(hinv t ht x).2]⟩

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def reparametrizedTimeField (τ : ℝ → ℝ)
    (V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2)
    (p : ℝ × M) : TangentSpace 𝓘(ℝ,E) p.2 := deriv τ p.1 • V (τ p.1,p.2)

theorem reparametrizedTimeField_smooth {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ)
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M))) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,reparametrizedTimeField τ V p⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
  apply timeField_smooth_of_coordinates
  intro p
  have hq := (timeChartField_contDiffOn hV p.2).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p.2)).mem_nhds
      (show (τ p.1,extChartAt 𝓘(ℝ,E) p.2 p.2) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) p.2).target
        from ⟨mem_univ _,mem_extChartAt_target p.2⟩))
  have hdτ : ContDiff ℝ ∞ (deriv τ) := hτ.deriv'
  have hd : ContDiffAt ℝ ∞ (fun q : ℝ × E => deriv τ q.1)
      (p.1,extChartAt 𝓘(ℝ,E) p.2 p.2) := hdτ.contDiffAt.comp _ contDiffAt_fst
  have hcoord : ContDiffAt ℝ ∞ (fun q : ℝ × E => (τ q.1,q.2))
      (p.1,extChartAt 𝓘(ℝ,E) p.2 p.2) :=
    (hτ.contDiffAt.comp _ contDiffAt_fst).prodMk contDiffAt_snd
  have hspace := hq.comp (f := fun q : ℝ × E => (τ q.1,q.2))
    (p.1,extChartAt 𝓘(ℝ,E) p.2 p.2) hcoord
  have hs := hd.smul hspace
  apply hs.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro q
  dsimp only [timeChartField,reparametrizedTimeField]
  exact (chartDifferential p.2 _).map_smul _ _

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem reparametrizedTimeField_curve {τ : ℝ → ℝ} {t : ℝ}
    (hτ : DifferentiableAt ℝ τ t)
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2} {γ : ℝ → M}
    (hγ : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ (τ t)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (τ t,γ (τ t))))) :
    HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (γ ∘ τ) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (reparametrizedTimeField τ V (t,γ (τ t)))) := by
  apply (hγ.comp t (hasMFDerivAt_iff_hasFDerivAt.mpr hτ.hasFDerivAt)).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change (fderiv ℝ τ t a) • V (τ t,γ (τ t)) = a • (deriv τ t • V (τ t,γ (τ t)))
  rw [hτ.hasDerivAt.hasFDerivAt.fderiv]
  change ((a : ℝ) * deriv τ t) • V (τ t,γ (τ t)) = (a : ℝ) • (deriv τ t • V (τ t,γ (τ t)))
  exact mul_smul (a : ℝ) (deriv τ t) _

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [T2Space M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem nonautonomous_curve_eqOn_Icc
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M))) {γ δ : ℝ → M}
    (hγ : ∀ t ∈ Icc (0:ℝ) 1, HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,γ t))))
    (hδ : ∀ t ∈ Icc (0:ℝ) 1, HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) δ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,δ t))))
    (h0 : γ 0 = δ 0) : EqOn γ δ (Icc (0:ℝ) 1) := by
  let τ : ℝ → ℝ := fun s => Real.sin s ^ 2
  have hτ : ContDiff ℝ ∞ τ := by dsimp [τ]; fun_prop
  have hτI (s : ℝ) : τ s ∈ Icc (0:ℝ) 1 := ⟨sq_nonneg _,Real.sin_sq_le_one s⟩
  have hτ0 : τ 0 = 0 := by simp [τ]
  have hτ1 : τ (Real.pi/2) = 1 := by simp [τ]
  have heq : EqOn (γ ∘ τ) (δ ∘ τ) (Ioo (-2:ℝ) 2) :=
    nonautonomous_curve_eqOn (reparametrizedTimeField_smooth hτ hV)
      (by norm_num : (0:ℝ) ∈ Ioo (-2:ℝ) 2)
      (fun s _ => reparametrizedTimeField_curve (hτ.differentiable (by simp) s) (hγ _ (hτI s)))
      (fun s _ => reparametrizedTimeField_curve (hτ.differentiable (by simp) s) (hδ _ (hτI s)))
      (by simp only [Function.comp_apply,hτ0,h0])
  intro t ht
  have hsubset := intermediate_value_Icc (by positivity : (0:ℝ) ≤ Real.pi/2)
    hτ.continuous.continuousOn
  have hti : t ∈ Icc (τ 0) (τ (Real.pi/2)) := by simpa only [hτ0,hτ1] using ht
  obtain ⟨s,hs,hst⟩ := hsubset hti
  have hs' : s ∈ Ioo (-2:ℝ) 2 := by
    constructor
    · linarith [hs.1]
    · linarith [hs.2,Real.pi_lt_four]
  have h := heq hs'
  simpa only [Function.comp_apply,hst] using h

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] [T2Space M]

omit [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem related_nonautonomous_flow_Icc
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    {W : (p : ℝ × N) → TangentSpace 𝓘(ℝ,F) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {e : N → M} (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    {Φ : ℝ × M → M} {Θ : ℝ × N → N}
    (hΦ : ∀ x t, t ∈ Icc (0:ℝ) 1 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
      (fun s => Φ (s,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,Φ (t,x)))))
    (hΘ : ∀ x t, t ∈ Icc (0:ℝ) 1 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,F)
      (fun s => Θ (s,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (W (t,Θ (t,x)))))
    (hΦ0 : ∀ x, Φ (0,x) = x) (hΘ0 : ∀ x, Θ (0,x) = x)
    (hrel : ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e x (W (t,x)) = V (t,e x)) :
    ∀ t ∈ Icc (0:ℝ) 1, ∀ x, Φ (t,e x) = e (Θ (t,x)) := by
  intro t ht x
  exact nonautonomous_curve_eqOn_Icc hV (fun s hs => hΦ (e x) s hs)
    (fun s hs => related_nonautonomous_curve he (hΘ x s hs) (hrel s hs (Θ (s,x))))
    (by simp only [Function.comp_apply,hΦ0,hΘ0]) ht

variable [FiniteDimensional ℝ F] [T2Space N] [CompactSpace N]

theorem compact_related_flow_preserves_range_Icc
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    {W : (p : ℝ × N) → TangentSpace 𝓘(ℝ,F) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (hW : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,F)) (𝓘(ℝ,F)).tangent ∞
      (fun p => (⟨p.2,W p⟩ : TangentBundle 𝓘(ℝ,F) N)))
    {e : N → M} (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    {Φ : ℝ × M → M}
    (hΦ : ∀ x t, t ∈ Icc (0:ℝ) 1 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
      (fun s => Φ (s,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,Φ (t,x)))))
    (hΦ0 : ∀ x, Φ (0,x) = x)
    (hrel : ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e x (W (t,x)) = V (t,e x)) :
    ∀ t ∈ Icc (0:ℝ) 1, (fun x => Φ (t,x)) '' range e = range e := by
  obtain ⟨Θ,Λ,_,_,hΘ0,hinv,hΘ,_⟩ := exists_nonautonomous_manifold_flow hW
  have hΘ' (x : N) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :=
    hΘ x t (show t ∈ Ioo (-2:ℝ) 2 by constructor <;> linarith [ht.1,ht.2])
  intro t ht
  have hn := related_nonautonomous_flow_Icc hV he hΦ hΘ' hΦ0 hΘ0 hrel t ht
  apply Subset.antisymm
  · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    change Φ (t,e x) ∈ range e
    rw [hn]
    exact mem_range_self _
  · rintro _ ⟨x,rfl⟩
    exact ⟨e (Λ (t,x)),mem_range_self _,by change Φ (t,e (Λ (t,x))) = e x; rw [hn,(hinv t ht x).2]⟩

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

 omit [FiniteDimensional ℝ E] in
 theorem spatially_compact_flow_preserves_split_range
    (e : F →L[ℝ] E) (P : E →L[ℝ] F) (hPe : P.comp e=ContinuousLinearMap.id ℝ F)
    {V : ℝ × E → E} (hV : ContDiff ℝ ∞ V)
    {C : Set E} (hC : IsCompact C) (hVC : ∀ t x,x∉C → V (t,x)=0)
    (htan : ∀ t∈Icc (0:ℝ) 1,∀ x,e (P (V (t,e x)))=V (t,e x))
    {Φ : ℝ × E → E} (hΦ0 : ∀ x,Φ (0,x)=x)
    (hΦ : ∀ x t,t∈Icc (0:ℝ) 1 → HasDerivAt (fun s => Φ (s,x)) (V (t,Φ (t,x))) t) :
    ∀ t∈Icc (0:ℝ) 1,(fun x => Φ (t,x)) '' range e=range e := by
  have hPe' (x : F) : P (e x)=x := by
    exact congrArg (fun L : F →L[ℝ] F => L x) hPe
  have he : Topology.IsClosedEmbedding e :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr (LeftInverse.injective hPe'))
  let W : ℝ × F → F := fun p => P (V (p.1,e p.2))
  have hW : ContDiff ℝ ∞ W := P.contDiff.comp
    (hV.comp (contDiff_fst.prodMk (e.contDiff.comp contDiff_snd)))
  have hVs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p : ℝ × E => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) E)) := by
    apply timeField_smooth_of_coordinates
    intro p
    have heq : timeChartField V p.2=V := by
      funext q
      simp only [timeChartField,chartDifferential,extChartAt_model_space_eq_id,PartialEquiv.refl_coe,PartialEquiv.refl_symm,mfderiv_eq_fderiv,fderiv_id,ContinuousLinearMap.id_apply,id_eq]
    rw [heq]
    simpa only [extChartAt_model_space_eq_id,PartialEquiv.refl_coe,id_eq] using hV.contDiffAt (x := p)
  have hWs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,F)) (𝓘(ℝ,F)).tangent ∞
      (fun p : ℝ × F => (⟨p.2,W p⟩ : TangentBundle 𝓘(ℝ,F) F)) := by
    apply timeField_smooth_of_coordinates
    intro p
    have heq : timeChartField W p.2=W := by
      funext q
      simp only [timeChartField,chartDifferential,extChartAt_model_space_eq_id,PartialEquiv.refl_coe,PartialEquiv.refl_symm,mfderiv_eq_fderiv,fderiv_id,ContinuousLinearMap.id_apply,id_eq]
    rw [heq]
    simpa only [extChartAt_model_space_eq_id,PartialEquiv.refl_coe,id_eq] using hW.contDiffAt (x := p)
  have hCF : IsCompact (e ⁻¹' C) := he.isCompact_preimage hC
  have hWC (t : ℝ) (x : F) (hx : x∉e ⁻¹' C) : W (t,x)=0 := by
    simp only [W,hVC t (e x) hx,map_zero]
  obtain ⟨Θ,Λ,_hΘs,_hΛs,hΘ0,hinv,hΘ,_⟩ :=
    exists_spatially_compact_nonautonomous_flow hWs hCF hWC
  have hΦ' (x : E) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun s => Φ (s,x)) t
        ((1:ℝ →L[ℝ] ℝ).smulRight (V (t,Φ (t,x)))) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr (hΦ x t ht).hasFDerivAt
  have hΘ' (x : F) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :=
    hΘ x t (show t∈Ioo (-2:ℝ) 2 by constructor <;> linarith [ht.1,ht.2])
  have hrel (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : F) :
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e x (W (t,x))=V (t,e x) := by
    rw [mfderiv_eq_fderiv,e.fderiv]
    exact htan t ht x
  intro t ht
  have hn := related_nonautonomous_flow_Icc hVs e.contDiff.contMDiff hΦ' hΘ' hΦ0 hΘ0 hrel t ht
  apply Subset.antisymm
  · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    change Φ (t,e x)∈range e
    rw [hn]
    exact mem_range_self _
  · rintro _ ⟨x,rfl⟩
    refine ⟨e (Λ (t,x)),mem_range_self _,?_⟩
    change Φ (t,e (Λ (t,x)))=e x
    rw [hn,(hinv t ht x).2]

end
section

variable {ι : Type} [Fintype ι]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

 theorem exists_compact_radial_relative_moser
    {Ω : ℝ → ManifoldTwoForm (PlanePhase ι) (PlanePhase ι)}
    {α : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)}
    (h : ManifoldMoserData Ω α) {K O : Set (PlanePhase ι)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O)
    (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K)
    {c : ℝ} (hc : c≠0)
    (hcircle : ∀ s,∀ z∈O,∀ v,Ω s z v (phaseJ z)=c*phaseDot z v)
    (hαcircle : ∀ s,∀ z∈O,α s z (phaseJ z)=0)
    (e : F →L[ℝ] PlanePhase ι) (P : PlanePhase ι →L[ℝ] F)
    (hPe : P.comp e=ContinuousLinearMap.id ℝ F)
    (htan : ∀ s∈Icc (0:ℝ) 1,∀ x,e x∈O →
      e (P (manifoldMoserField Ω α (s,e x)))=manifoldMoserField Ω α (s,e x)) :
    ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
      (∀ x,Φ (0,x)=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (t,x))=phaseSq x) ∧
      (∀ t∈Icc (0:ℝ) 1,(fun x => Φ (t,x)) '' range e=range e) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈K,∀ v w,manifoldPullback Φ Ω t x v w=Ω 0 x v w) := by
  let U : Set (ℝ × PlanePhase ι) := (univ×ˢO) ∩ {p | (Ω p.1 p.2).IsInvertible}
  have hU : IsOpen U := (isOpen_univ.prod hO).inter (manifoldTwoForm_isOpen_nondegenerate h.smooth_two)
  have hKU : Icc (0:ℝ) 1×ˢK⊆U := fun p hp =>
    ⟨⟨mem_univ _,hKO hp.2⟩,h.nondegenerate _ hp.1 _⟩
  obtain ⟨V,hV,hVe,_hVz,⟨C,hC,hVC⟩,hVL⟩ :=
    exists_joint_localized_manifold_moser_field (Ω := Ω) (α := α) h.smooth_two h.smooth_one
      (isCompact_Icc.prod hK) hU hKU (fun _ hp => hp.2)
  have hVrad (p : ℝ × PlanePhase ι) : phaseDot p.2 (V p)=0 := by
    apply hVL p (phaseDot p.2)
    intro hp
    exact radial_moser_field_tangent (Ω := Ω) (α := α) hp.2 hc
      (hcircle _ _ hp.1.2) (hαcircle _ _ hp.1.2)
  have hVtan (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (x : F) :
      e (P (V (s,e x)))=V (s,e x) := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro L
    have hz := hVL (s,e x) (L.comp (e.comp P)-L) (by
      intro hp
      change L (e (P (manifoldMoserField Ω α (s,e x)))) -
        L (manifoldMoserField Ω α (s,e x)) = 0
      exact sub_eq_zero.mpr (congrArg L (htan s hs x hp.1.2)))
    change L (e (P (V (s,e x)))) - L (V (s,e x)) = 0 at hz
    exact sub_eq_zero.mp hz
  obtain ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦi,hODE,_hfix⟩ :=
    exists_spatially_compact_nonautonomous_flow hV hC hVC
  have hODE' (x : PlanePhase ι) (t : ℝ) (ht : t∈Ioo (-2:ℝ) 2) :
      HasDerivAt (fun s => Φ (s,x)) (V (t,Φ (t,x))) t := by
    have hd : HasFDerivAt (fun s => Φ (s,x))
        ((1 : ℝ →L[ℝ] ℝ).smulRight (show PlanePhase ι from V (t,Φ (t,x)))) t :=
      hasMFDerivAt_iff_hasFDerivAt.mp (hODE x t ht)
    exact hasDerivAt_iff_hasFDerivAt.mpr hd
  have hrad (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : PlanePhase ι) :
      phaseSq (Φ (t,x))=phaseSq x :=
    phaseSq_nonautonomous_flow_constant hΦ0 hODE' hVrad ht x
  have hΦs : ContDiff ℝ ∞ Φ := by
    rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hΦ
    exact contMDiff_iff_contDiff.mp hΦ
  have hΨs : ContDiff ℝ ∞ Ψ := by
    rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hΨ
    exact contMDiff_iff_contDiff.mp hΨ
  have hVs : ContDiff ℝ ∞ V := by
    have hs := (contMDiff_snd_tangentBundle_modelSpace (PlanePhase ι) 𝓘(ℝ,PlanePhase ι)).comp hV
    rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hs
    exact contMDiff_iff_contDiff.mp hs
  refine ⟨Φ,Ψ,hΦs,hΨs,hΦ0,hΦi,hrad,?_,?_⟩
  · apply spatially_compact_flow_preserves_split_range e P hPe hVs hC hVC hVtan hΦ0
    intro x t ht
    exact hODE' x t (by constructor <;> linarith [ht.1,ht.2])
  · intro t ht x hx v w
    have hd (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
        HasDerivAt (fun r => manifoldPullback Φ Ω r x v w) 0 s := by
      apply local_manifold_form_transport_derivative hΦ hV isOpen_Ioo hODE h.smooth_two
        (show s∈Ioo (-2:ℝ) 2 by constructor <;> linarith [hs.1,hs.2]) x
      intro b y hy he
      have hpK : (s,(extChartAt 𝓘(ℝ,PlanePhase ι) b).symm y)∈Icc (0:ℝ) 1×ˢK :=
        ⟨hs,by rw [he]; exact hKr x hx _ (hrad s hs x)⟩
      have hpU := hKU hpK
      have hn : (univ×ˢ(extChartAt 𝓘(ℝ,PlanePhase ι) b).target)∈𝓝 (s,y) :=
        (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,PlanePhase ι)) b)).mem_nhds ⟨mem_univ _,hy⟩
      apply joint_manifold_moser_PDE hV hU hy hpU (fun _ hp => hp.2)
        (hVe.filter_mono (nhds_le_nhdsSet hpK)) ((h.smooth_two b).contDiffAt hn)
        ((h.smooth_one b).contDiffAt hn) _ (h.closed s hs b y hy) (h.exact_time s hs b y hy)
      intro u z
      exact h.skew s hs b y hy u z
    have he := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hd s hs).hasDerivWithinAt)
      (fun _ _ => (by simp : ‖(0:ℝ)‖≤(0:ℝ))) (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) ht
    have he' : manifoldPullback Φ Ω t x v w=manifoldPullback Φ Ω 0 x v w := by
      simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using he
    rw [he']
    have hid : (fun y => Φ (0,y))=id := funext hΦ0
    have hD : preferredDifferential (fun y => Φ (0,y)) x=ContinuousLinearMap.id ℝ (PlanePhase ι) := by
      change mfderiv 𝓘(ℝ,PlanePhase ι) 𝓘(ℝ,PlanePhase ι) (fun y => Φ (0,y)) x=_
      rw [hid]; exact mfderiv_id
    rw [manifoldPullback,hD]
    simp only [hΦ0,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.id_apply]

end

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 @[simp] theorem cutoff_phaseSq_zero : phaseSq (0:PlanePhase ι)=0 := by simp [phaseSq]

 theorem degreeConePrimitive_zero (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c : ℝ)
    (z : PlanePhase ι) : degreeConePrimitive q F c 0 z=c•standardLiouville z := by
  by_cases hz : z=0
  · subst z
    simp [degreeConePrimitive,degreeHopfPrimitive,hopfPrimitive,standardLiouville,phaseSq]
  · ext v
    simp only [degreeConePrimitive,degreeHopfPrimitive,mul_zero,sub_zero,one_smul,
      zero_smul,add_zero,hopfPrimitive,standardLiouville,smul_apply,smul_eq_mul]
    field_simp [(phaseSq_pos hz).ne']

 def cutoffDegreePrimitive (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    (χ : ℝ → ℝ) (t : ℝ) (z : PlanePhase ι) : PlanePhase ι →L[ℝ] ℝ :=
  c•standardLiouville z+(t*d*χ (phaseSq z))•(phaseSq z•degreeHopfDifference q F c z)

 theorem cutoffDegreePrimitive_eq (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    (χ : ℝ → ℝ) (t : ℝ) : cutoffDegreePrimitive q F c d χ t=
      radialDegreeConePrimitive q F c (fun a => t*d*χ a) := by
  funext z
  rw [cutoffDegreePrimitive,radialDegreeConePrimitive,degreeConePrimitive_split,degreeConePrimitive_zero]

 theorem cutoffDegreePrimitive_smooth {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0) (q c d : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => cutoffDegreePrimitive q F c d χ p.1 p.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hz : p.2=0
  · have hn : (fun p : ℝ × PlanePhase ι => χ (phaseSq p.2))=ᶠ[𝓝 p] 0 := by
      have hct : Filter.Tendsto (fun p : ℝ × PlanePhase ι => phaseSq p.2) (𝓝 p) (𝓝 (0:ℝ)) := by
        have hh := ((phaseSq_smooth (ι := ι)).continuous.comp
          (continuous_snd : Continuous (Prod.snd : ℝ × PlanePhase ι → PlanePhase ι))).continuousAt (x := p)
        change Filter.Tendsto (fun p : ℝ × PlanePhase ι => phaseSq p.2) (𝓝 p) (𝓝 (phaseSq p.2)) at hh
        rw [hz,cutoff_phaseSq_zero] at hh
        exact hh
      exact hχ0.comp_tendsto hct
    apply ((((standardLiouville_smooth (ι := ι)).const_smul c).comp contDiff_snd).contDiffAt).congr_of_eventuallyEq
    filter_upwards [hn] with p hp
    simp only [cutoffDegreePrimitive,hp,Pi.zero_apply,mul_zero,zero_smul,add_zero,Function.comp_apply]
  · exact (((standardLiouville_smooth (ι := ι)).const_smul c).comp contDiff_snd).contDiffAt.add
      (((contDiffAt_fst.mul contDiffAt_const).mul
        (hχ.contDiffAt.comp p (phaseSq_smooth.contDiffAt.comp p contDiffAt_snd))).smul
        ((phaseSq_smooth.contDiffAt.comp p contDiffAt_snd).smul
          ((degreeHopfDifference_smoothAt hF.contDiffAt hz (hF0 _ hz) q c).comp p contDiffAt_snd)))

 theorem cutoffDegreePrimitive_nhds_zero (q : ℝ) (F : PlanePhase ι → PlanePhase κ)
    (c d t : ℝ) {χ : ℝ → ℝ} (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0) :
    cutoffDegreePrimitive q F c d χ t=ᶠ[𝓝 (0:PlanePhase ι)] (fun z => c•standardLiouville z) := by
  have hct : Filter.Tendsto (phaseSq (ι := ι)) (𝓝 (0:PlanePhase ι)) (𝓝 (0:ℝ)) := by
    simpa only [ContinuousAt, cutoff_phaseSq_zero] using (phaseSq_smooth (ι := ι)).continuous.continuousAt (x := 0)
  have hn := hχ0.comp_tendsto hct
  filter_upwards [hn] with z hz
  change χ (phaseSq z)=0 at hz
  simp only [cutoffDegreePrimitive,hz,mul_zero,zero_smul,add_zero]

 theorem cutoffDegreePrimitive_slice_smooth {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0) (q c d t : ℝ) :
    ContDiff ℝ ∞ (cutoffDegreePrimitive q F c d χ t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z=0
  · subst z
    exact ((standardLiouville_smooth (ι := ι)).contDiffAt.const_smul c).congr_of_eventuallyEq
      (cutoffDegreePrimitive_nhds_zero q F c d t hχ0)
  · exact ((standardLiouville_smooth (ι := ι)).contDiffAt.const_smul c).add
      ((hχ.contDiffAt.comp z phaseSq_smooth.contDiffAt).const_smul (t*d) |>.smul
        (phaseSq_smooth.contDiffAt.smul (degreeHopfDifference_smoothAt hF.contDiffAt hz (hF0 _ hz) q c)))

 theorem cutoffDegreePrimitive_nondegenerate {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hD : ∀ z,fderiv ℝ F z z=q•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0)
    (hχr : ∀ a,χ a∈Icc (0:ℝ) 1) {c d : ℝ} (hc : 0<c) (hd : 0≤d)
    (hq : 0≤q) (hdq : q*d<1) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (z : PlanePhase ι) :
    (euclideanExteriorOneForm (cutoffDegreePrimitive q F c d χ t) z).IsInvertible := by
  classical
  by_cases hz : z=0
  · subst z
    have he := (cutoffDegreePrimitive_nhds_zero q F c d t hχ0).fderiv_eq (𝕜 := ℝ)
    have he' : euclideanExteriorOneForm (cutoffDegreePrimitive q F c d χ t) 0=c•(phaseArea (ι := ι)) := by
      rw [euclideanExteriorOneForm,he]
      change euclideanExteriorOneForm (c•(standardLiouville (ι := ι))) 0=_
      rw [euclideanExteriorOneForm_smul c ((standardLiouville_smooth (ι := ι)).contDiffAt.differentiableAt (by simp)),
        standardLiouville_exterior]
    rw [he']
    exact bilinear_isInvertible_of_taming (J := phaseJ) (fun v hv => by
      simpa only [smul_apply,smul_eq_mul,phaseArea_J_right,phaseSq] using
        mul_pos hc (phaseSq_pos hv))
  · rw [cutoffDegreePrimitive_eq]
    apply radialDegreeConePrimitive_nondegenerate hF.contDiffAt hz (hF0 z hz) (hD z) (hJ z)
      ((hχ.differentiable (by simp) _).const_mul (t*d)) hc
      (mul_nonneg (mul_nonneg ht.1 hd) (hχr _).1)
    calc
      q*(t*d*χ (phaseSq z))≤q*d := by
        nlinarith only [ht.1,ht.2,hd,hq,(hχr (phaseSq z)).1,(hχr (phaseSq z)).2,
          mul_nonneg hq hd,mul_nonneg (mul_nonneg hq hd) ht.1,
          mul_le_mul_of_nonneg_left (hχr (phaseSq z)).2 (mul_nonneg (mul_nonneg hq ht.1) hd)]
      _<1 := hdq

end PackingSufficiencySupport.Hamiltonian
end

end OAI
