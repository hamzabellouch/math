import Mathlib
import OAI.Geometry.SmoothYau.DifferentialEq.IntegralPathSolution

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal

theorem smooth_extension_near_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    {φ : E → F} (hφ : ContDiffOn ℝ ∞ φ O) :
    ∃ ψ : E → F, ContDiff ℝ ∞ ψ ∧ φ =ᶠ[𝓝ˢ K] ψ := by
  obtain ⟨V, hV, hKV, hVO⟩ := normal_exists_closure_subset hK.isClosed hO hKO
  obtain ⟨η, hηone, hηzero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, E)) (n := ⊤) (t := V)
      hK.isClosed (by simpa only [hV.interior_eq] using hKV)
  have hη : ContDiff ℝ ∞ η := contMDiff_iff_contDiff.mp η.contMDiff
  have hsη : tsupport η ⊆ O := by
    apply (closure_mono (show support η ⊆ V from ?_)).trans hVO
    intro x hx
    by_contra hn
    exact hx (hηzero x hn)
  refine ⟨fun x => η x • φ x, ?_, ?_⟩
  · rw [← contMDiff_iff_contDiff]
    apply contMDiff_of_tsupport
    intro x hx
    have hxO : x ∈ O := hsη (tsupport_smul_subset_left η φ hx)
    rw [contMDiffAt_iff_contDiffAt]
    exact hη.contDiffAt.smul ((hφ x hxO).contDiffAt (hO.mem_nhds hxO))
  · filter_upwards [hηone] with x hx
    simp only [hx, one_smul]


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem smooth_local_flow_of_lipschitz {V : E → E} (hV : ContDiff ℝ ∞ V)
    {K : ℝ≥0} (hLip : LipschitzWith K V) (x : E) :
    ∃ (O : Set (ℝ × E)) (φ : ℝ × E → E),
      IsOpen O ∧ (0,x) ∈ O ∧ ContDiffOn ℝ ∞ φ O ∧
      (∀ q ∈ O, φ (0,q.2) = q.2) ∧
      ∀ q ∈ O, HasDerivAt (fun t => φ (t,q.2)) (V (φ q)) q.1 := by
  obtain ⟨O₀, u, hO₀, hx₀, hus, hu0, hu⟩ := smooth_integral_paths hV x
  obtain ⟨r, hr, ε, hε, hcurves⟩ :=
    ((hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by simp)).contDiffAt (x := x)).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  let O := (O₀ ∩ (fun q : ℝ × E => (0,q.2)) ⁻¹' O₀) ∩ Ioo (-ε) ε ×ˢ ball x r
  have hOo : IsOpen O := (hO₀.inter (hO₀.preimage (by fun_prop))).inter (isOpen_Ioo.prod isOpen_ball)
  let φ : ℝ × E → E := fun p => u p 1
  have heq (p : ℝ × E) (hp : p ∈ O) (α : ℝ → E) (hα0 : α 0 = p.2)
      (hα : ∀ t ∈ Ioo (-ε) ε, HasDerivAt α (V (α t)) t) : φ p = α p.1 := by
    have hh := integral_path_eq_solution hLip (abs_lt.mpr hp.2.1) (u p) (hu p hp.1.1) α hα0 hα 1
    simpa [φ] using hh
  refine ⟨O, φ, hOo, ⟨⟨hx₀,hx₀⟩, ⟨by simpa using hε, hε⟩, mem_ball_self hr⟩, ?_, ?_, ?_⟩
  · exact (ContinuousMap.evalCLM ℝ (1 : unitInterval)).contDiff.comp_contDiffOn (hus.mono (show O ⊆ O₀ from fun q hq => hq.1.1))
  · intro q hq
    have hq' : (0,q.2) ∈ O₀ := hq.1.2
    have hh := hu (0,q.2) hq'
    simp only [zero_smul, add_zero] at hh
    exact congrArg (fun v : C(unitInterval,E) => v 1) hh
  · intro q hq
    obtain ⟨α,hα0,hα⟩ := hcurves q.2 (ball_subset_closedBall hq.2.2)
    simp only [zero_sub, zero_add] at hα
    have hev : (fun t => φ (t,q.2)) =ᶠ[𝓝 q.1] α := by
      have hh : ∀ᶠ t in 𝓝 q.1, (t,q.2) ∈ O :=
        (continuous_id.prodMk continuous_const).continuousAt.eventually (hOo.mem_nhds hq)
      filter_upwards [hh] with t ht
      exact heq (t,q.2) ht α hα0 hα
    have hd := (hα q.1 hq.2.1).congr_of_eventuallyEq hev
    rw [← heq q hq α hα0 hα] at hd
    exact hd

end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma flow_initial_fderiv {O : Set (ℝ × E)} (hO : IsOpen O)
    {φ : ℝ × E → E} (hφ : ContDiffOn ℝ ∞ φ O) {x v : E} (hx : (0,x) ∈ O)
    (h0 : ∀ q ∈ O, φ (0,q.2) = q.2)
    (ht : HasDerivAt (fun t => φ (t,x)) v 0) (a : ℝ) (b : E) :
    fderiv ℝ φ (0,x) (a,b) = a • v + b := by
  have hd := ((hφ _ hx).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have htime : fderiv ℝ φ (0,x) (1,0) = v := by
    have hh := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))
    exact hh.unique ht
  have hspace : (fderiv ℝ φ (0,x)).comp (ContinuousLinearMap.inr ℝ ℝ E) = ContinuousLinearMap.id ℝ E := by
    have hh := hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (0 : ℝ) x)
    have he : (fun y => φ (0,y)) =ᶠ[𝓝 x] id := by
      have hN : ∀ᶠ y in 𝓝 x, (0,y) ∈ O :=
        (continuous_const.prodMk continuous_id).continuousAt.eventually (hO.mem_nhds hx)
      filter_upwards [hN] with y hy
      exact h0 (0,y) hy
    exact (hh.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id x)
  have hs : fderiv ℝ φ (0,x) (0,b) = b := congrArg (fun A : E →L[ℝ] E => A b) hspace
  have hab : (a,b) = a • (1,0) + (0,b) := by simp
  rw [hab, map_add, map_smul, htime, hs]

omit [FiniteDimensional ℝ E] in
lemma flow_fderiv_time {O : Set (ℝ × E)} (hO : IsOpen O)
    {φ : ℝ × E → E} (hφ : ContDiffOn ℝ ∞ φ O) {V : E → E}
    (ht : ∀ q ∈ O, HasDerivAt (fun t => φ (t,q.2)) (V (φ q)) q.1)
    {q : ℝ × E} (hq : q ∈ O) : fderiv ℝ φ q (1,0) = V (φ q) := by
  have hd := ((hφ _ hq).contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
  have hh := hd.hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  exact hh.unique (ht q hq)

theorem smooth_flowbox_of_lipschitz {V : E → E} (hV : ContDiff ℝ ∞ V)
    {K : ℝ≥0} (hLip : LipschitzWith K V) {x : E} (hv : V x ≠ 0) :
    ∃ (W : Set E) (σ : E → E), IsOpen W ∧ x ∈ W ∧ ContDiffOn ℝ ∞ σ W ∧
      σ x = 0 ∧ fderiv ℝ σ x = ContinuousLinearMap.id ℝ E ∧
      ∀ y ∈ W, fderiv ℝ σ y (V y) = V x := by
  obtain ⟨O,φ,hO,hx,hφ,h0,ht⟩ := smooth_local_flow_of_lipschitz hV hLip x
  obtain ⟨l, _, hl⟩ := exists_dual_vector ℝ (V x) (norm_ne_zero_iff.mpr hv)
  let L : E →L[ℝ] ℝ := ‖V x‖⁻¹ • l
  have hL : L (V x) = 1 := by simp [L,hl, norm_ne_zero_iff.mpr hv]
  let Q : E → ℝ × E := fun z => (L z, x + (z - L z • V x))
  let A : E →L[ℝ] (ℝ × E) := L.prod (ContinuousLinearMap.id ℝ E - L.smulRight (V x))
  have hQ : ∀ z, HasFDerivAt Q A z := by
    intro z
    exact L.hasFDerivAt.prodMk ((hasFDerivAt_id z).sub
      (L.hasFDerivAt.smul_const (V x)) |>.const_add x)
  have hQc : ContDiff ℝ ∞ Q := by dsimp [Q]; fun_prop
  have hQ0 : Q 0 = (0,x) := by simp [Q]
  have hAv : A (V x) = (1,0) := by simp [A,hL]
  let U := Q ⁻¹' O
  have hUo : IsOpen U := hO.preimage hQc.continuous
  have h0U : (0 : E) ∈ U := by simpa [U,hQ0] using hx
  let F : E → E := φ ∘ Q
  have hFs : ContDiffOn ℝ ∞ F U := hφ.comp hQc.contDiffOn (fun _ h => h)
  have hF0 : F 0 = x := by simpa [F,hQ0] using h0 (0,x) hx
  have hFd : HasFDerivAt F (ContinuousLinearMap.id ℝ E) 0 := by
    have hd := ((hφ _ hx).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hd' := hd.hasFDerivAt
    rw [← hQ0] at hd'
    have hh := hd'.comp 0 (hQ 0)
    rw [hQ0] at hh
    convert! hh using 1
    ext z
    change z = fderiv ℝ φ (0,x) (L z, z - L z • V x)
    rw [flow_initial_fderiv hO hφ hx h0 (by simpa [h0 (0,x) hx] using ht (0,x) hx)]
    abel
  obtain ⟨G,hGs,hFG⟩ := smooth_extension_near_compact (isCompact_singleton (x := (0 : E)))
    hUo (by simpa using h0U) hFs
  have hFG' : F =ᶠ[𝓝 (0 : E)] G := by simpa only [nhdsSet_singleton] using hFG
  have hG0 : G 0 = x := hFG'.eq_of_nhds.symm.trans hF0
  have hGd := hFd.congr_of_eventuallyEq hFG'.symm
  obtain ⟨e,T,hef,he0,hTo,hGT,hT,hTs⟩ := smooth_inverse_on hGs 0
    (ContinuousLinearEquiv.refl ℝ E) hGd
  have he0t : e.symm x = 0 := by rw [← hG0, ← hef]; exact e.left_inv he0
  obtain ⟨B,hBsub,hBo,hB0⟩ := _root_.mem_nhds_iff.mp (hFG'.and (hUo.mem_nhds h0U))
  let W := T ∩ e.symm ⁻¹' B
  have hxT : x ∈ T := hG0 ▸ hGT
  have hWo : IsOpen W := (e.continuousOn_symm.mono hT).isOpen_inter_preimage hTo hBo
  have hxW : x ∈ W := ⟨hxT, by simpa [he0t] using hB0⟩
  have hσs : ContDiffOn ℝ ∞ e.symm W := hTs.mono inter_subset_left
  have hsx : HasFDerivAt e.symm (ContinuousLinearMap.id ℝ E) x := by
    have hh := e.hasFDerivAt_symm (f' := ContinuousLinearEquiv.refl ℝ E) (hT hxT) (by simpa [he0t,hef] using hGd)
    simpa using hh
  refine ⟨W,e.symm,hWo,hxW,hσs,he0t,hsx.fderiv,?_⟩
  intro y hy
  have hyt := hT hy.1
  have hyB : e.symm y ∈ B := hy.2
  have hyU : e.symm y ∈ U := (hBsub hyB).2
  have hFGe : F =ᶠ[𝓝 (e.symm y)] G :=
    Filter.Eventually.mono (hBo.mem_nhds hyB) (fun z hz => (hBsub hz).1)
  have hGv : fderiv ℝ G (e.symm y) (V x) = V y := by
    have hdφ := ((hφ _ hyU).contDiffAt (hO.mem_nhds hyU)).differentiableAt (by simp)
    have hdF := hdφ.hasFDerivAt.comp (e.symm y) (hQ _)
    have heval : F (e.symm y) = y := by
      rw [hFGe.eq_of_nhds, ← hef]
      exact e.right_inv hyt
    rw [← hFGe.fderiv_eq, hdF.fderiv]
    change fderiv ℝ φ (Q (e.symm y)) (A (V x)) = V y
    rw [hAv, flow_fderiv_time hO hφ ht hyU]
    exact congrArg V heval
  have hdG := hGs.differentiable (by simp) (e.symm y)
  have hdσ := ((hσs _ hy).contDiffAt (hWo.mem_nhds hy)).differentiableAt (by simp)
  have hinv : (fun z => e.symm (G z)) =ᶠ[𝓝 (e.symm y)] id := by
    filter_upwards [e.open_source.mem_nhds (e.map_target hyt)] with z hz
    rw [← hef]
    exact e.left_inv hz
  have hGy : G (e.symm y) = y := by rw [← hef]; exact e.right_inv hyt
  have hdσ' := hdσ.hasFDerivAt
  rw [← hGy] at hdσ'
  have hid := (hdσ'.comp (e.symm y) hdG.hasFDerivAt).congr_of_eventuallyEq hinv.symm
  rw [hGy] at hid
  have heq := hid.unique (hasFDerivAt_id (e.symm y))
  have heqv := congrArg (fun D : E →L[ℝ] E => D (V x)) heq
  simpa only [ContinuousLinearMap.comp_apply, hGv, ContinuousLinearMap.id_apply] using heqv

theorem smooth_flowbox {V : E → E} (hV : ContDiff ℝ ∞ V) {x : E} (hv : V x ≠ 0) :
    ∃ (W : Set E) (σ : E → E), IsOpen W ∧ x ∈ W ∧ ContDiffOn ℝ ∞ σ W ∧
      σ x = 0 ∧ fderiv ℝ σ x = ContinuousLinearMap.id ℝ E ∧
      ∀ y ∈ W, fderiv ℝ σ y (V y) = V x := by
  let χ : ContDiffBump x := ⟨1,2,zero_lt_one,by norm_num⟩
  let Z : E → E := fun y => χ y • V y
  have hZ : ContDiff ℝ ∞ Z := χ.contDiff.smul hV
  have hZc : HasCompactSupport Z := χ.hasCompactSupport.smul_right
  obtain ⟨K,hLip⟩ := hZ.lipschitzWith_of_hasCompactSupport hZc (by simp)
  have he (y : E) (hy : y ∈ ball x 1) : Z y = V y := by
    simp only [Z, χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_smul]
  have hx : x ∈ ball x 1 := mem_ball_self zero_lt_one
  obtain ⟨W,σ,hWo,hWx,hσ,hσx,hσd,hrect⟩ := smooth_flowbox_of_lipschitz hZ hLip (he x hx ▸ hv)
  refine ⟨W ∩ ball x 1,σ,hWo.inter isOpen_ball,⟨hWx,hx⟩,hσ.mono inter_subset_left,hσx,hσd,?_⟩
  intro y hy
  simpa only [he y hy.2, he x hx] using hrect y hy.1

theorem smooth_first_integral {V : E → E} (hV : ContDiff ℝ ∞ V) {x : E} (hv : V x ≠ 0)
    (l : E →L[ℝ] ℝ) (hl : l ≠ 0) (hlv : l (V x) = 0) :
    ∃ (W : Set E) (s : E → ℝ), IsOpen W ∧ x ∈ W ∧ ContDiffOn ℝ ∞ s W ∧
      s x = 0 ∧ fderiv ℝ s x = l ∧
      ∀ y ∈ W, fderiv ℝ s y ≠ 0 ∧ fderiv ℝ s y (V y) = 0 := by
  obtain ⟨W,σ,hWo,hWx,hσ,hσx,hσd,hrect⟩ := smooth_flowbox hV hv
  let s := l ∘ σ
  have hs : ContDiffOn ℝ ∞ s W := l.contDiff.comp_contDiffOn hσ
  have hsd (y : E) (hy : y ∈ W) : fderiv ℝ s y = l.comp (fderiv ℝ σ y) := by
    exact (l.hasFDerivAt.comp y (((hσ y hy).contDiffAt (hWo.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt).fderiv
  have hsdx : fderiv ℝ s x = l := by rw [hsd x hWx,hσd,ContinuousLinearMap.comp_id]
  have hn : ∀ᶠ y in 𝓝 x, fderiv ℝ s y ≠ 0 := by
    apply ((hs.continuousOn_fderiv_of_isOpen hWo (by simp)) x hWx).continuousAt (hWo.mem_nhds hWx) |>.eventually_ne
    rwa [hsdx]
  obtain ⟨B,hB,hBo,hBx⟩ := _root_.mem_nhds_iff.mp (hn.and (hWo.mem_nhds hWx))
  refine ⟨B,s,hBo,hBx,hs.mono (fun y hy => (hB hy).2),?_,hsdx,?_⟩
  · simp [s,hσx]
  · intro y hy
    refine ⟨(hB hy).1,?_⟩
    rw [hsd y (hB hy).2, ContinuousLinearMap.comp_apply, hrect y (hB hy).2, hlv]



end YauCounterexamples
end

end OAI
