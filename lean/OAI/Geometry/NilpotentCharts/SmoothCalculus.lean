import Mathlib

namespace OAI

/-! Smooth local inverses, parameter derivatives and vector parts of closed additive groups. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawSliceInverse
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

 

theorem exists_smooth_local_inverse (f : V → E) (U : Set V) (hU : IsOpen U) (h0 : (0 : V) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (L : V ≃L[ℝ] E) (hD : HasFDerivAt f L.toContinuousLinearMap 0) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ,V) 𝓘(ℝ,E) V E ∞,
      0 ∈ e.source ∧ e.source ⊆ U ∧ (e : V → E) = f := by
  have hf0 : ContDiffAt ℝ ∞ f 0 := hf.contDiffAt (hU.mem_nhds h0)
  have hnear : {x : V | ∃ l : V ≃L[ℝ] E, l.toContinuousLinearMap = fderiv ℝ f x} ∈ 𝓝 0 := by
    have hL := L.nhds
    rw [← hD.fderiv] at hL
    exact (hf0.continuousAt_fderiv (by simp)).preimage_mem_nhds hL
  obtain ⟨U',hU'sub,hU'open,hU'0⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds h0) hnear)
  have hs := hf0.hasStrictFDerivAt' hD (by simp)
  let e₀ := hs.toOpenPartialHomeomorph f
  let e := e₀.restr U'
  have heq : (e : V → E) = f := rfl
  have heSource : e.source = e₀.source ∩ U' := OpenPartialHomeomorph.restr_source' _ _ hU'open
  have he0 : (0 : V) ∈ e.source := by
    rw [heSource]
    exact ⟨hs.mem_toOpenPartialHomeomorph_source,hU'0⟩
  have heU : e.source ⊆ U := fun _ hx => (hU'sub ((heSource ▸ hx).2)).1
  have heSmooth : ContDiffOn ℝ ∞ e e.source := hf.mono heU
  have heInvSmooth : ContDiffOn ℝ ∞ e.symm e.target := by
    intro y hy
    have hx := e.map_target hy
    obtain ⟨l,hl⟩ := (hU'sub ((heSource ▸ hx).2)).2
    have hfx : ContDiffAt ℝ ∞ f (e.symm y) := hf.contDiffAt (hU.mem_nhds (heU hx))
    have hdx : HasFDerivAt e l.toContinuousLinearMap (e.symm y) := by
      rw [heq,hl]
      exact (hfx.differentiableAt (by simp)).hasFDerivAt
    exact (e.contDiffAt_symm hy hdx hfx).contDiffWithinAt
  exact ⟨{ e with
    contMDiffOn_toFun := heSmooth.contMDiffOn
    contMDiffOn_invFun := heInvSmooth.contMDiffOn }, he0, heU, heq⟩
end RawSliceInverse

namespace RawParameterDerivative
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local notation "I₀" => 𝓘(ℝ,E)
def D (g : M → M) (p : M) : E →L[ℝ] E := mfderiv I₀ I₀ g p

lemma contDiff_parameter_derivative (f : ℝ → M → M)
    (hf : ContMDiff (𝓘(ℝ,ℝ).prod I₀) I₀ ∞ (Function.uncurry f))
    (p : M) (hp : ∀ t, f t p = p) :
    ContDiff ℝ ∞ (fun t => D (E := E) (f t) p) := by
  let c := extChartAt I₀ p
  let F : ℝ → E → E := fun t x => c (f t (c.symm x))
  have hF : ∀ t, ContDiffAt ℝ ∞ (Function.uncurry F) (t,c p) := by
    intro t
    have hsym : ContMDiffAt I₀ I₀ ∞ c.symm (c p) := by
      apply contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I := I₀) (n := ∞) p)
      exact (chartAt E p).map_source (mem_chart_source E p)
    have hin : ContMDiffAt (𝓘(ℝ,ℝ).prod I₀) (𝓘(ℝ,ℝ).prod I₀) ∞
        (fun y : ℝ × E => (y.1,c.symm y.2)) (t,c p) :=
      contMDiffAt_fst.prodMk (hsym.comp (t,c p) contMDiffAt_snd)
    have hh : ContMDiffAt (𝓘(ℝ,ℝ).prod I₀) I₀ ∞
        (fun y : ℝ × E => f y.1 (c.symm y.2)) (t,c p) :=
      (hf (t,c.symm (c p))).comp (t,c p) hin
    have hc : ContMDiffAt I₀ I₀ ∞ c (f t (c.symm (c p))) := by
      rw [c.left_inv (mem_extChartAt_source p),hp]
      exact contMDiffAt_extChartAt
    have H := ContMDiffAt.comp (f := fun y : ℝ × E => f y.1 (c.symm y.2))
      (g := c) (t,c p) hc hh
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at H
    exact H.contDiffAt
  have hD : ∀ t, D (E := E) (f t) p = fderiv ℝ (F t) (c p) := by
    intro t
    have hm : MDifferentiableAt I₀ I₀ (f t) p := by
      exact ((hf (t,p)).comp p (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
    simp only [D,mfderiv,ite_eq_left hm,writtenInExtChartAt,hp,modelWithCornersSelf_coe,range_id,
      fderivWithin_univ]
    rfl
  rw [show (fun t => D (E := E) (f t) p) =
      fun t => fderiv ℝ (F t) (c p) from funext hD]
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (hF t).fderiv contDiffAt_const (by simp)
end RawParameterDerivative

namespace RawParameterDerivativeGeneral
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M N : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace V N] [IsManifold 𝓘(ℝ,V) ∞ N]
local notation "I₀" => 𝓘(ℝ,E)
local notation "J₀" => 𝓘(ℝ,V)
def D (g : M → M) (p : M) : E →L[ℝ] E := mfderiv I₀ I₀ g p

lemma contMDiff_parameter_derivative (f : N → M → M)
    (hf : ContMDiff ((J₀).prod I₀) I₀ ∞ (Function.uncurry f))
    (p : M) (hp : ∀ t, f t p = p) :
    ContMDiff J₀ 𝓘(ℝ,E →L[ℝ] E) ∞ (fun t => D (E := E) (f t) p) := by
  intro a
  let c := extChartAt I₀ p
  let q := extChartAt J₀ a
  let F : V → E → E := fun t x => c (f (q.symm t) (c.symm x))
  have hcsym : ContMDiffAt I₀ I₀ ∞ c.symm (c p) := by
    apply contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := I₀) (n := ∞) p)
    exact (chartAt E p).map_source (mem_chart_source E p)
  have hqsym : ContMDiffAt J₀ J₀ ∞ q.symm (q a) := by
    apply contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := J₀) (n := ∞) a)
    exact (chartAt V a).map_source (mem_chart_source V a)
  have hin : ContMDiffAt ((J₀).prod I₀) ((J₀).prod I₀) ∞
      (fun y : V × E => (q.symm y.1,c.symm y.2)) (q a,c p) :=
    (hqsym.comp (q a,c p) contMDiffAt_fst).prodMk
      (hcsym.comp (q a,c p) contMDiffAt_snd)
  have hh : ContMDiffAt ((J₀).prod I₀) I₀ ∞
      (fun y : V × E => f (q.symm y.1) (c.symm y.2)) (q a,c p) :=
    (hf (q.symm (q a),c.symm (c p))).comp (q a,c p) hin
  have hc : ContMDiffAt I₀ I₀ ∞ c (f (q.symm (q a)) (c.symm (c p))) := by
    rw [c.left_inv (mem_extChartAt_source p),hp]
    exact contMDiffAt_extChartAt
  have hF : ContDiffAt ℝ ∞ (Function.uncurry F) (q a,c p) := by
    have H := ContMDiffAt.comp (f := fun y : V × E => f (q.symm y.1) (c.symm y.2))
      (g := c) (q a,c p) hc hh
    rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at H
    exact H.contDiffAt
  have hD : ∀ t, D (E := E) (f (q.symm t)) p = fderiv ℝ (F t) (c p) := by
    intro t
    have hm : MDifferentiableAt I₀ I₀ (f (q.symm t)) p :=
      ((hf (q.symm t,p)).comp p (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
    simp only [D,mfderiv,ite_eq_left hm,writtenInExtChartAt,hp,modelWithCornersSelf_coe,range_id,
      fderivWithin_univ]
    rfl
  have hDc : ContDiffAt ℝ ∞ (fun t => D (E := E) (f (q.symm t)) p) (q a) := by
    simp_rw [hD]
    exact hF.fderiv contDiffAt_const (by simp)
  have hcomp := hDc.contMDiffAt.comp a (show ContMDiffAt J₀ J₀ ∞ q a from contMDiffAt_extChartAt)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I := J₀) a] with b hb
  exact congrArg (fun x : N => D (E := E) (f x) p) ((q.left_inv hb).symm)

end RawParameterDerivativeGeneral

namespace RawSmoothInverse
variable {V E G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G]
lemma contMDiff_inverse (h : V ≃ₜ G) (hf : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ h)
    (hD : ∀ x : V, ∃ L : V ≃L[ℝ] E,
      (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) h x : V →L[ℝ] E) = L.toContinuousLinearMap) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ h.symm := by
  intro g
  let x := h.symm g
  have hxg : h x = g := h.apply_symm_apply g
  let c := chartAt E g
  have hcg : g ∈ c.source := mem_chart_source E g
  have hc : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ c g :=
    (contMDiffOn_chart (n := ∞)).contMDiffAt (c.open_source.mem_nhds hcg)
  have hcD : (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c g : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    rw [mfderiv_chartAt_eq_tangentCoordChange hcg]
    apply ContinuousLinearMap.ext
    intro v
    exact tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ,E)) g)
  let e : OpenPartialHomeomorph V E := h.toOpenPartialHomeomorph.trans c
  have hxe : x ∈ e.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change h x ∈ c.source
    rwa [hxg]
  have hex : e x = c g := by change c (h x) = c g; rw [hxg]
  have hfc : ContDiffAt ℝ ∞ e x := by
    have hc' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ c (h x) := hxg.symm ▸ hc
    exact (hc'.comp x (hf x)).contDiffAt
  obtain ⟨L,hL⟩ := hD x
  have hdc : HasFDerivAt e L.toContinuousLinearMap x := by
    have hd := (hxg.symm ▸ hc).mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
    have hd' := (hf x).mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
    have heD : (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) e x : V →L[ℝ] E) = L.toContinuousLinearMap := by
      change mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) (c ∘ h) x = _
      rw [mfderiv_comp x hd hd',hxg,hcD,hL]
      exact ContinuousLinearMap.id_comp _
    exact (HasMFDerivAt.congr_mfderiv ((hfc.contMDiffAt).mdifferentiableAt (by simp)).hasMFDerivAt heD).hasFDerivAt
  have hinv : ContDiffAt ℝ ∞ e.symm (c g) := by
    rw [← hex]
    have hdx : HasFDerivAt e L.toContinuousLinearMap (e.symm (e x)) := by
      rwa [e.left_inv hxe]
    have hfx : ContDiffAt ℝ ∞ e (e.symm (e x)) := by rwa [e.left_inv hxe]
    exact e.contDiffAt_symm (e.map_source hxe) hdx hfx
  have hcomp : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ (e.symm ∘ c) g :=
    hinv.contMDiffAt.comp g hc
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hcg] with y hy
  change h.symm y = h.symm (c.symm (c y))
  rw [c.left_inv hy]
end RawSmoothInverse

namespace RawClosedAddGroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma deriv_mem (H : AddSubgroup E) (hH : IsClosed (H : Set E))
    {f : ℝ → E} {v : E} {x : ℝ} (hf : HasDerivAt f v x)
    (hm : ∀ t, f t ∈ H) : v ∈ H := by
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall ?_⟩
    intro n
    simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
    positivity
  have hd := hf.tendsto_slope_zero.comp ht
  apply hH.mem_of_tendsto hd
  apply Eventually.of_forall
  intro n
  change (1 / ((n : ℝ)+1))⁻¹ • (f (x+1/((n:ℝ)+1)) - f x) ∈ H
  rw [one_div,inv_inv,show (n : ℝ)+1 = ((n+1 : ℕ) : ℝ) by simp, Nat.cast_smul_eq_nsmul]
  exact H.nsmul_mem (H.sub_mem (hm _) (hm _)) _

def vectorPart (H : AddSubgroup E) : Submodule ℝ E where
  carrier := {v | ∀ t : ℝ, t • v ∈ H}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy t; rw [smul_add]; exact H.add_mem (hx t) (hy t)
  smul_mem' := by intro r x hx t; rw [smul_smul]; exact hx (t*r)

lemma vectorPart_le (H : AddSubgroup E) : (vectorPart H).toAddSubgroup ≤ H := by
  intro v hv
  simpa only [one_smul] using hv 1

lemma deriv_mem_vectorPart (H : AddSubgroup E) (hH : IsClosed (H : Set E))
    {f : ℝ → E} {v : E} {x : ℝ} (hf : HasDerivAt f v x)
    (hm : ∀ t, f t ∈ H) : v ∈ vectorPart H := by
  intro r
  have ha : HasDerivAt (fun t : ℝ => x+r*t) r 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul r).const_add x using 1 <;> first | rfl | simp only [mul_one]
  have hb : HasDerivAt (fun t : ℝ => f (x+r*t)) (r • v) 0 := by
    exact (by simpa only [mul_zero,add_zero] using hf : HasDerivAt f v (x+r*0)).scomp 0 ha
  exact deriv_mem H hH hb (fun t => hm _)

 

lemma curve_mem_vectorPart [FiniteDimensional ℝ E]
    (H : AddSubgroup E) (hH : IsClosed (H : Set E))
    {f : ℝ → E} (hf : Differentiable ℝ f) (hm : ∀ t, f t ∈ H)
    (h0 : f 0 = 0) (x : ℝ) : f x ∈ vectorPart H := by
  by_contra hn
  obtain ⟨L,hL,hV⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  let C : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap L
  have hD (t : ℝ) : HasDerivAt (fun t => L (f t)) 0 t := by
    have hv := deriv_mem_vectorPart H hH (hf t).hasDerivAt hm
    have hz : L (deriv f t) = 0 := by
      have hi : L (deriv f t) ∈ (vectorPart H).map L := Submodule.mem_map_of_mem hv
      rw [hV,Submodule.mem_bot] at hi
      exact hi
    have hc : C (deriv f t) = 0 := hz
    change HasDerivAt (fun t => C (f t)) 0 t
    simpa only [Function.comp_def,hc] using C.hasFDerivAt.comp_hasDerivAt t (hf t).hasDerivAt
  have he := is_const_of_deriv_eq_zero (fun t => (hD t).differentiableAt)
    (fun t => (hD t).deriv) x 0
  exact hL (he.trans (by rw [h0,map_zero]))
end RawClosedAddGroup
end

end OAI
