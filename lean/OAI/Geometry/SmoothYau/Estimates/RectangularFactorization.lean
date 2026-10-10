import Mathlib

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology
namespace YauCounterexamples
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem rectangular_factorization {I : Set ℝ} {J : Set W}
    (hIo : IsOpen I) (hJo : IsOpen J) (hJc : IsPreconnected J)
    {w₀ : W} (hw₀ : w₀ ∈ J) (V : ℝ × W → ℝ)
    (hV : ContDiffOn ℝ 2 V (I ×ˢ J))
    (hvert : ∀ s ∈ I, ∀ w ∈ J, ∀ v : W,
      fderiv ℝ V (s,w) (0,v) = 0) :
    ∃ F : ℝ → ℝ, ContDiffOn ℝ 2 F I ∧
      ∀ s ∈ I, ∀ w ∈ J, V (s,w) = F s := by
  let F : ℝ → ℝ := fun s => V (s,w₀)
  refine ⟨F, ?_, ?_⟩
  · exact hV.comp (contDiffOn_id.prodMk contDiffOn_const) (fun s hs => ⟨hs,hw₀⟩)
  intro s hs w hw
  have hd (w : W) (hw : w ∈ J) : DifferentiableAt ℝ V (s,w) :=
    (hV.differentiableOn (by norm_num)).differentiableAt
      ((hIo.prod hJo).mem_nhds ⟨hs,hw⟩)
  have hslice : DifferentiableOn ℝ (fun w : W => V (s,w)) J := by
    intro w hw
    exact ((hd w hw).comp w ((differentiableAt_const s).prodMk differentiableAt_id)).differentiableWithinAt
  have hz : EqOn (fderiv ℝ (fun w : W => V (s,w))) 0 J := by
    intro w hw
    change fderiv ℝ (V ∘ (fun w : W => (s,w))) w = 0
    rw [fderiv_comp w (hd w hw) ((differentiableAt_const s).prodMk differentiableAt_id)]
    ext v
    simpa [(hasFDerivAt_prodMk_right (𝕜:=ℝ) s w).fderiv] using hvert s hs w hw v
  exact hJo.is_const_of_fderiv_eq_zero hJc hslice hz hw hw₀
open Filter Function Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem local_factor_of_kernel {f g : E → ℝ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    (hd : fderiv ℝ f x ≠ 0)
    (hker : ∀ y ∈ U, ∀ v : E, fderiv ℝ f y v = 0 → fderiv ℝ g y v = 0) :
    ∃ (V : Set E) (I : Set ℝ) (F : ℝ → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      IsOpen I ∧ IsPreconnected I ∧ f x ∈ I ∧ ContDiffOn ℝ 2 F I ∧
      MapsTo f V I ∧ EqOn g (F ∘ f) V := by
  let L := fderiv ℝ f x
  have hL : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    apply surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (f := L.toLinearMap) (by simp)
    intro hh
    apply hd
    ext y
    exact DFunLike.congr_fun hh y
  have hfx := (hf x hx).contDiffAt (hU.mem_nhds hx)
  have hs : HasStrictFDerivAt f L x := hfx.hasStrictFDerivAt (by norm_num)
  have hLc : L.ker.ClosedComplemented := L.ker_closedComplemented_of_finiteDimensional_range
  let φ := hs.implicitFunctionDataOfComplemented f L hL hLc
  let e := φ.toOpenPartialHomeomorph
  have hex : x ∈ e.source := φ.pt_mem_toOpenPartialHomeomorph_source
  have hefx (y : E) : (e y).1 = f y := rfl
  have he0 : e x = (f x,0) := by simp [e,φ,ImplicitFunctionData.prodFun]
  have hext : (f x, (0 : L.ker)) ∈ e.target := he0 ▸ e.map_source hex
  have heix : e.symm (f x,0) = x := by rw [←he0]; exact e.left_inv hex
  have hr : ContDiffAt ℝ 2 φ.rightFun φ.pt := by
    exact ((Classical.choose hLc).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hi := φ.contDiffAt_implicitFunction hfx hr (by norm_num)
  change ContDiffAt ℝ 2 e.symm (e x) at hi
  rw [he0] at hi
  have hpre : e.symm ⁻¹' U ∈ 𝓝 (f x,(0:L.ker)) := by
    apply (e.continuousAt_symm hext).tendsto
    rw [heix]
    exact hU.mem_nhds hx
  obtain ⟨r,hrpos,hrsub⟩ := Metric.mem_nhds_iff.mp
    (((hi.eventually (by norm_num)).and (e.open_target.mem_nhds hext)).and hpre)
  let I := ball (f x) r
  let J : Set L.ker := ball 0 r
  let B := I ×ˢ J
  have hBo : IsOpen B := isOpen_ball.prod isOpen_ball
  have hBsub (y : ℝ × L.ker) (hy : y ∈ B) :
      ContDiffAt ℝ 2 e.symm y ∧ y ∈ e.target ∧ e.symm y ∈ U := by
    have hy' : y ∈ ball (f x,(0:L.ker)) r := by
      rw [←ball_prod_same]; exact hy
    have hh := hrsub hy'
    exact ⟨hh.1.1,hh.1.2,hh.2⟩
  let G := g ∘ e.symm
  have hG : ContDiffOn ℝ 2 G B := by
    intro y hy
    exact (((hg _ (hBsub y hy).2.2).contDiffAt (hU.mem_nhds (hBsub y hy).2.2)).comp y
      (hBsub y hy).1).contDiffWithinAt
  have hvertical : ∀ s ∈ I, ∀ w ∈ J, ∀ v : L.ker,
      fderiv ℝ G (s,w) (0,v) = 0 := by
    intro s hs w hw v
    let y : ℝ × L.ker := (s,w)
    have hy : y ∈ B := ⟨hs,hw⟩
    have hyU := (hBsub y hy).2.2
    have hdi := (hBsub y hy).1.differentiableAt (by norm_num)
    have hdf := ((hf _ hyU).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
    have hdg := ((hg _ hyU).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
    have heq : f ∘ e.symm =ᶠ[𝓝 y] Prod.fst := by
      filter_upwards [e.open_target.mem_nhds (hBsub y hy).2.1] with z hz
      exact congrArg Prod.fst (e.right_inv hz)
    have hff : fderiv ℝ f (e.symm y) (fderiv ℝ e.symm y (0,v)) = 0 := by
      have hh := heq.fderiv_eq (𝕜:=ℝ)
      rw [fderiv_comp y hdf hdi] at hh
      rw [fderiv_fst] at hh
      exact congrArg (fun A : (ℝ × L.ker) →L[ℝ] ℝ => A (0,v)) hh
    change fderiv ℝ (g ∘ e.symm) y (0,v) = 0
    rw [fderiv_comp y hdg hdi]
    exact hker _ hyU _ hff
  obtain ⟨F,hF,hGF⟩ := rectangular_factorization (I:=I) (J:=J) isOpen_ball isOpen_ball
    (convex_ball (0:L.ker) r).isPreconnected (mem_ball_self hrpos) G hG hvertical
  let V := e.source ∩ e ⁻¹' B
  have hVo : IsOpen V := e.continuousOn.isOpen_inter_preimage e.open_source hBo
  have hxV : x ∈ V := ⟨hex,by change e x ∈ B; rw [he0]; exact ⟨mem_ball_self hrpos,mem_ball_self hrpos⟩⟩
  have hVU : V ⊆ U := by
    intro y hy
    have hh := (hBsub (e y) hy.2).2.2
    rwa [e.left_inv hy.1] at hh
  refine ⟨V,I,F,hVo,hxV,hVU,isOpen_ball,(convex_ball (f x) r).isPreconnected,
    mem_ball_self hrpos,hF,?_,?_⟩
  · intro y hy
    exact hy.2.1
  · intro y hy
    have hh := hGF (e y).1 hy.2.1 (e y).2 hy.2.2
    change g (e.symm (e y)) = F (f y) at hh
    rwa [e.left_inv hy.1] at hh
end YauCounterexamples


end

end OAI
