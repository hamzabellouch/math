import Mathlib
import OAI.Geometry.BallPacking.Moser.PlanarCorrection

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Metric
open scoped Classical
open Function MeasureTheory
def circlePullback (alpha : Plane → Plane →L[ℝ] ℝ) (R t : ℝ) : ℝ :=
  alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t)

theorem circlePullback_smooth {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) (R : ℝ) : ContDiff ℝ ∞ (circlePullback alpha R) := by
  apply (ha.comp (polar_smooth.comp (contDiff_const.prodMk contDiff_id))).clm_apply
  fun_prop

theorem circlePullback_periodic (alpha : Plane → Plane →L[ℝ] ℝ) (R : ℝ) :
    Periodic (circlePullback alpha R) (2*Real.pi) := by
  intro t
  simp only [circlePullback,polarCoord_symm_apply,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem exists_circle_primitive {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) {R delta : ℝ} (hR : 0 < R) (hd : 0 < delta)
    (hdR : delta < R^2) (hz : (∫ p in roundDisk R, planarCurl alpha p) = 0) :
    ∃ H : Plane → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      (∀ p, delta ≤ |radiusSq p-R^2| → H p = 0) ∧
      ∀ t, fderiv ℝ H (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) =
        circlePullback alpha R t := by
  let a := circlePullback alpha R
  have has := circlePullback_smooth ha R
  have haz : (∫ t in -Real.pi..Real.pi, a t) = 0 := by
    rw [integral_curl_roundDisk ha hR] at hz
    exact hz
  have hp := periodicPrimitive_periodic has.continuous (circlePullback_periodic alpha R) haz
  let H := angularExtension R delta hd (periodicPrimitive a)
  have hH := angularExtension_smooth hd hdR (periodicPrimitive_smooth has) hp
  refine ⟨H,hH,angularExtension_compact hd _,angularExtension_zero hd _,?_⟩
  intro t
  have hc : HasDerivAt (fun t => polarCoord.symm (R,t))
      (-R*Real.sin t,R*Real.cos t) t := by
    change HasDerivAt (fun t => (R*Real.cos t,R*Real.sin t)) _ t
    exact (((Real.hasDerivAt_cos t).const_mul R).prodMk
      ((Real.hasDerivAt_sin t).const_mul R)).congr_deriv (by ext <;> simp [neg_mul])
  have hdH := ((hH.differentiable (by simp)) (polarCoord.symm (R,t))).hasFDerivAt.comp_hasDerivAt t hc
  have he : (fun t => H (polarCoord.symm (R,t))) = periodicPrimitive a :=
    funext (fun t => angularExtension_polar hR hd hp t)
  change HasDerivAt (fun t => H (polarCoord.symm (R,t))) _ t at hdH
  rw [he] at hdH
  exact hdH.unique (periodicPrimitive_hasDerivAt has.continuous t)

theorem polar_surjective_circle {R : ℝ} (hR : 0 < R) {p : Plane}
    (hp : radiusSq p = R^2) : ∃ t : ℝ, polarCoord.symm (R,t) = p := by
  let z := Complex.equivRealProdCLM.symm p
  have hn : ‖z‖ = R := by
    have hsq : ‖z‖^2 = radiusSq p := by
      rw [Complex.sq_norm]
      simp [z,Complex.normSq_apply,radiusSq,Complex.equivRealProdCLM_symm_apply,pow_two]
    nlinarith [norm_nonneg z]
  refine ⟨z.arg,?_⟩
  have hx := Complex.norm_mul_cos_arg z
  have hy := Complex.norm_mul_sin_arg z
  rw [hn] at hx hy
  exact Prod.ext hx hy

theorem fderiv_zero_outside_collar {H : Plane → ℝ} {R delta : ℝ}
    (hH : ∀ p, delta ≤ |radiusSq p-R^2| → H p = 0) {p : Plane}
    (hp : delta < |radiusSq p-R^2|) : fderiv ℝ H p = 0 := by
  have he : H =ᶠ[𝓝 p] (fun _ => (0:ℝ)) := by
    filter_upwards [(isOpen_lt continuous_const ((radiusSq_smooth.continuous.sub continuous_const).abs)).mem_nhds hp]
      with x hx
    exact hH x hx.le
  rw [he.fderiv_eq]
  simp only [fderiv_const_apply]

theorem exists_positive_lt_finite {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) : ∃ d : ℝ, 0 < d ∧ ∀ i ∈ s, d < a i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨d,hd,hds⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    refine ⟨min d (a i/2),lt_min hd (half_pos (ha i (Finset.mem_insert_self _ _))),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (min_le_right _ _).trans_lt (half_lt_self (ha j (Finset.mem_insert_self _ _)))
    · exact (min_le_left _ _).trans_lt (hds j hj)

theorem planarCurl_sub_differential {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) {H : Plane → ℝ} (hH : ContDiff ℝ ∞ H) (p : Plane) :
    planarCurl (fun p => alpha p - fderiv ℝ H p) p = planarCurl alpha p := by
  have hs := (hH.contDiffAt (x := p)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  unfold planarCurl
  rw [fderiv_fun_sub ((ha.differentiable (by simp)) p)
    (((hH.fderiv_right (by simp : (∞ : ℕ∞ω)+1 ≤ ∞)).differentiable (by simp)) p)]
  simp only [sub_apply]
  rw [hs.eq (1,0) (0,1)]
  ring

theorem exists_disjoint_radial_collars {ι : Type*} [Fintype ι]
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRi : Injective R) (i : ι) :
    ∃ d : ℝ, 0 < d ∧ d < (R i)^2 ∧ ∀ j, j ≠ i → d < |(R j)^2-(R i)^2| := by
  classical
  let a : ι → ℝ := fun j => if j = i then (R i)^2 else |(R j)^2-(R i)^2|
  have ha0 (j : ι) : 0 < a j := by
    dsimp [a]
    split_ifs with hj
    · exact sq_pos_of_pos (hR i)
    · apply abs_pos.mpr
      intro he
      have heq : R j = R i := by nlinarith [hR i,hR j]
      exact hj (hRi heq)
  obtain ⟨d,hd,hda⟩ := exists_positive_lt_finite Finset.univ a (fun j _ => ha0 j)
  refine ⟨d,hd,?_,?_⟩
  · simpa [a] using hda i (Finset.mem_univ i)
  · intro j hj
    simpa [a,hj] using hda j (Finset.mem_univ j)

theorem finite_potential_correction {ι : Type*} [Fintype ι]
    {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (hac : HasCompactSupport alpha) (R : ι → ℝ)
    (H : ι → Plane → ℝ) (hHs : ∀ i, ContDiff ℝ ∞ (H i))
    (hHc : ∀ i, HasCompactSupport (H i))
    (hself : ∀ i p, radiusSq p = (R i)^2 →
      fderiv ℝ (H i) p (-p.2,p.1) = alpha p (-p.2,p.1))
    (hother : ∀ i j, j ≠ i → ∀ p, radiusSq p = (R i)^2 → fderiv ℝ (H j) p = 0) :
    ∃ beta : Plane → Plane →L[ℝ] ℝ, ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
      (∀ p, planarCurl beta p = planarCurl alpha p) ∧
      ∀ i p, radiusSq p = (R i)^2 → beta p (-p.2,p.1) = 0 := by
  classical
  let F : Plane → ℝ := fun p => ∑ i, H i p
  have hFs : ContDiff ℝ ∞ F := ContDiff.sum (fun i _ => hHs i)
  have hFc : HasCompactSupport F := by
    have he : (∑ i, H i) = F := by
      funext p
      simp [F]
    rw [← he]
    exact HasCompactSupport.finset_sum (s := Finset.univ) (f := H) (fun i _ => hHc i)
  have hFd (p v : Plane) : fderiv ℝ F p v = ∑ i, fderiv ℝ (H i) p v := by
    change fderiv ℝ (fun p => ∑ i, H i p) p v = _
    rw [fderiv_fun_sum (fun i _ => ((hHs i).differentiable (by simp)) p)]
    simp only [sum_apply]
  let beta : Plane → Plane →L[ℝ] ℝ := fun p => alpha p - fderiv ℝ F p
  refine ⟨beta,ha.sub (hFs.fderiv_right (by simp)),hac.sub (hFc.fderiv (𝕜 := ℝ)),
    planarCurl_sub_differential ha hFs,?_⟩
  intro i p hp
  change alpha p (-p.2,p.1) - fderiv ℝ F p (-p.2,p.1) = 0
  rw [hFd,Finset.sum_eq_single i,hself i p hp,sub_self]
  · intro j _ hj
    rw [hother i j hj p hp]
    rfl
  · simp

theorem exists_finite_circle_correction {ι : Type*} [Fintype ι]
    {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (hac : HasCompactSupport alpha) (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hRi : Injective R) (hz : ∀ i, (∫ p in roundDisk (R i), planarCurl alpha p) = 0) :
    ∃ beta : Plane → Plane →L[ℝ] ℝ, ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
      (∀ p, planarCurl beta p = planarCurl alpha p) ∧
      ∀ i p, radiusSq p = (R i)^2 → beta p (-p.2,p.1) = 0 := by
  classical
  choose d hd hdR hdsep using exists_disjoint_radial_collars R hR hRi
  choose H hHs hHc hHspt hHt using fun i => exists_circle_primitive ha (hR i) (hd i) (hdR i) (hz i)
  apply finite_potential_correction ha hac R H hHs hHc
  · intro i p hp
    obtain ⟨t,rfl⟩ := polar_surjective_circle (hR i) hp
    simpa only [circlePullback,polarCoord_symm_apply,neg_mul] using hHt i t
  · intro i j hj p hp
    apply fderiv_zero_outside_collar (hHspt j)
    rw [hp]
    exact hdsep j i hj.symm

theorem exists_sphere_distance_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {R : ℝ} (hR : 0 < R) (v : E) (hv : ‖v‖ = R) (x : E) :
    ∃ y : E, ‖y‖ = R ∧ dist x y ≤ |‖x‖^2-R^2| / R := by
  by_cases hx : x = 0
  · subst x
    refine ⟨v,hv,?_⟩
    simp only [dist_zero_left,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_sub,
      abs_neg,abs_of_nonneg (sq_nonneg R),hv]
    rw [pow_two,mul_div_cancel_right₀ _ hR.ne']
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y := (R/‖x‖) • x
    have hy : ‖y‖ = R := by
      simp only [y,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hR hx0)]
      exact div_mul_cancel₀ R hx0.ne'
    refine ⟨y,hy,?_⟩
    have hd : dist x y = |‖x‖-R| := by
      rw [dist_eq_norm,show x-y = (1-R/‖x‖) • x by dsimp [y]; rw [sub_smul,one_smul]]
      rw [norm_smul,Real.norm_eq_abs]
      calc
        |1-R/‖x‖| *‖x‖ = |(1-R/‖x‖)*‖x‖| := by rw [abs_mul,abs_of_pos hx0]
        _ = |‖x‖-R| := by congr 1; field_simp
    rw [hd]
    apply (le_div_iff₀ hR).mpr
    have he : |‖x‖^2-R^2| = |‖x‖-R| *(‖x‖+R) := by
      rw [show ‖x‖^2-R^2 = (‖x‖-R)*(‖x‖+R) by ring,abs_mul,
        abs_of_pos (add_pos hx0 hR)]
    rw [he]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hx0.le) (abs_nonneg _)

theorem lipschitz_zero_on_sphere_bound {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] {L : ℝ≥0} {f : E → F}
    (hf : LipschitzWith L f) {R : ℝ} (hR : 0 < R) (v : E) (hv : ‖v‖ = R)
    (hz : ∀ x, ‖x‖ = R → f x = 0) (x : E) :
    ‖f x‖ ≤ ((L : ℝ)/R)*|‖x‖^2-R^2| := by
  obtain ⟨y,hy,hxy⟩ := exists_sphere_distance_bound hR v hv x
  have h := hf.dist_le_mul x y
  rw [hz y hy,dist_zero_right] at h
  calc
    ‖f x‖ ≤ (L:ℝ)*dist x y := h
    _ ≤ (L:ℝ)*(|‖x‖^2-R^2|/R) := mul_le_mul_of_nonneg_left hxy L.coe_nonneg
    _ = _ := by ring

def radialDrift (X : ℝ × Plane → Plane) (p : ℝ × Plane) : ℝ :=
  2*(p.2.1*(X p).1+p.2.2*(X p).2)

theorem radialDrift_smooth {X : ℝ × Plane → Plane} (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (radialDrift X) := by unfold radialDrift; fun_prop

theorem radialDrift_compact {X : ℝ × Plane → Plane} (hc : HasCompactSupport X) :
    HasCompactSupport (radialDrift X) := by
  apply hc.mono ?_
  intro p hp
  contrapose! hp
  simpa only [mem_support,not_not] using (show radialDrift X p = 0 by
    simp [radialDrift,show X p = 0 from notMem_support.mp hp])

theorem complex_normSq_plane (p : Plane) :
    ‖Complex.equivRealProdCLM.symm p‖^2 = radiusSq p := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,radiusSq,Complex.equivRealProdCLM_symm_apply,pow_two]

theorem exists_radialDrift_bound {X : ℝ × Plane → Plane} (hX : ContDiff ℝ ∞ X)
    (hc : HasCompactSupport X) {R : ℝ} (hR : 0 < R)
    (htan : ∀ t x, radiusSq x = R^2 → radialDrift X (t,x) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, |radialDrift X (t,x)| ≤ C*|radiusSq x-R^2| := by
  let e : (ℝ × ℂ) ≃L[ℝ] (ℝ × Plane) :=
    (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr Complex.equivRealProdCLM
  let D : ℝ × ℂ → ℝ := fun p => radialDrift X (e p)
  have hDs : ContDiff ℝ ∞ D := (radialDrift_smooth hX).comp e.contDiff
  have hDc : HasCompactSupport D := (radialDrift_compact hc).comp_homeomorph e.toHomeomorph
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hDc hDs (by simp)
  refine ⟨(L:ℝ)/R,div_nonneg L.coe_nonneg hR.le,?_⟩
  intro t x
  have hLt : LipschitzWith L (fun z : ℂ => D (t,z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist z w)] using hL.dist_le_mul (t,z) (t,w)
  have hz (z : ℂ) (hz : ‖z‖ = R) : D (t,z) = 0 := by
    apply htan t (Complex.equivRealProdCLM z)
    rw [← complex_normSq_plane,ContinuousLinearEquiv.symm_apply_apply,hz]
  have h := lipschitz_zero_on_sphere_bound hLt hR (R:ℂ)
    (by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]) hz
    (Complex.equivRealProdCLM.symm x)
  simpa only [D,e,ContinuousLinearEquiv.prodCongr_apply,ContinuousLinearEquiv.refl_apply,
    ContinuousLinearEquiv.apply_symm_apply,Real.norm_eq_abs,complex_normSq_plane] using h

theorem trajectory_preserves_circle {X : ℝ × Plane → Plane} (hX : ContDiff ℝ ∞ X)
    (hc : HasCompactSupport X) {R : ℝ} (hR : 0 < R)
    (htan : ∀ t x, radiusSq x = R^2 → radialDrift X (t,x) = 0)
    {u : ℝ → Plane} {a b c h : ℝ} (hu : ContinuousOn u (Icc a b))
    (hud : ∀ s ∈ Ico a b, HasDerivWithinAt u (h • X (c+h*s,u s)) (Ici s) s)
    (ha : radiusSq (u a) = R^2) :
    ∀ s ∈ Icc a b, radiusSq (u s) = R^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_radialDrift_bound hX hc hR htan
  let g : ℝ → ℝ := fun s => radiusSq (u s)-R^2
  let g' : ℝ → ℝ := fun s => h*radialDrift X (c+h*s,u s)
  have hgc : ContinuousOn g (Icc a b) := (radiusSq_smooth.continuous.comp_continuousOn hu).sub continuousOn_const
  have hgd (s : ℝ) (hs : s ∈ Ico a b) : HasDerivWithinAt g (g' s) (Ici s) s := by
    have hd1 : HasDerivWithinAt (fun s => (u s).1) (h*(X (c+h*s,u s)).1) (Ici s) s :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt s (hud s hs)
    have hd2 : HasDerivWithinAt (fun s => (u s).2) (h*(X (c+h*s,u s)).2) (Ici s) s :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt s (hud s hs)
    have hd := ((hd1.pow 2).add (hd2.pow 2)).sub_const (R^2)
    exact hd.congr_deriv (by simp only [g',radialDrift]; ring)
  have hgb (s : ℝ) (_hs : s ∈ Ico a b) : ‖g' s‖ ≤ (|h| *C)*‖g s‖ := by
    simp only [g',g,Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_left (hbound (c+h*s) (u s)) (abs_nonneg h)).trans_eq (by ring)
  have he := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hgc hgd
    (show g a = 0 from sub_eq_zero.mpr ha) hgb
  intro s hs
  exact sub_eq_zero.mp (he s hs)

theorem timeStep_preserves_circle {L : ℝ≥0} (X : C(ℝ × Plane,Plane))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    {R : ℝ} (hR : 0 < R)
    (htan : ∀ t x, radiusSq x = R^2 → radialDrift X (t,x) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) {x : Plane} (hx : radiusSq x = R^2) :
    radiusSq (timeStep X hX h t x) = R^2 := by
  let Y := clockField X
  let hY := clockField_lipschitz X hX
  let u := fixedStep Y hY h (t,x)
  let v : ℝ → Plane := fun s => (extendPath u s).2
  have hc : ContinuousOn v (Icc (0:ℝ) 1) := (extendPath u).continuous.snd.continuousOn
  have hd (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      HasDerivWithinAt v (h • X (t+h*s,v s)) (Ici s) s := by
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.le⟩
    have he : (extendPath u s).1 = t+h*s := by
      rw [show extendPath u s = u ⟨s,hs'⟩ from extendPath_coe u ⟨s,hs'⟩]
      exact fixedStep_clock X hX hh (t,x) ⟨s,hs'⟩
    have hd0 : HasDerivWithinAt v (h • X (extendPath u s)) (Icc (0:ℝ) 1) s :=
      (ContinuousLinearMap.snd ℝ ℝ Plane).hasFDerivAt.comp_hasDerivWithinAt s
        (fixedStep_derivative Y hY hh (t,x) hs')
    have hd1 := hd0.mono_of_mem_nhdsWithin (s := Ici s) (by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs.2),
        (self_mem_nhdsWithin : Ici s ∈ 𝓝[Ici s] s)] with q hq hsq
      exact ⟨hs.1.trans hsq,hq.le⟩)
    change HasDerivWithinAt v (h • X (extendPath u s)) (Ici s) s at hd1
    have hp : extendPath u s = (t+h*s,v s) := Prod.ext he rfl
    rwa [hp] at hd1
  have hv0 : v 0 = x := by
    change (extendPath u 0).2 = x
    rw [show extendPath u 0 = u ⟨0,by simp⟩ from extendPath_coe u ⟨0,by simp⟩]
    change (fixedStep Y hY h (t,x) ⟨0,by simp⟩).2 = x
    rw [fixedStep_initial Y hY hh]
  have he := trajectory_preserves_circle hXs hXc hR htan hc hd
    (show radiusSq (v 0) = R^2 by rw [hv0]; exact hx) 1 (by simp)
  change radiusSq ((extendPath u 1).2) = R^2 at he
  rw [show extendPath u 1 = u ⟨1,by simp⟩ from extendPath_coe u ⟨1,by simp⟩] at he
  exact he

theorem timeStep_preserves_circle_iff {L : ℝ≥0} (X : C(ℝ × Plane,Plane))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    {R : ℝ} (hR : 0 < R)
    (htan : ∀ t x, radiusSq x = R^2 → radialDrift X (t,x) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (x : Plane) :
    radiusSq (timeStep X hX h t x) = R^2 ↔ radiusSq x = R^2 := by
  constructor
  · intro hx
    have he := timeStep_preserves_circle X hX hXs hXc hR htan
      (h := -h) (by simpa using hh) (t+h) hx
    rwa [timeStep_inverse X hX hh t x] at he
  · exact timeStep_preserves_circle X hX hXs hXc hR htan hh t

theorem timeSteps_preserves_circle_iff {L : ℝ≥0} (X : C(ℝ × Plane,Plane))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    {R : ℝ} (hR : 0 < R)
    (htan : ∀ t x, radiusSq x = R^2 → radialDrift X (t,x) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (N : ℕ) (x : Plane) :
    radiusSq (timeSteps X hX hXs hh t N x) = R^2 ↔ radiusSq x = R^2 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change radiusSq (timeStep X hX h (t+N*h) (timeSteps X hX hXs hh t N x)) = R^2 ↔ _
    rw [timeStep_preserves_circle_iff X hX hXs hXc hR htan hh,ih]

def coordinateForm (U V : Plane → ℝ) (p : Plane) : Plane →L[ℝ] ℝ :=
  U p • ContinuousLinearMap.fst ℝ ℝ ℝ + V p • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem coordinateForm_apply (U V : Plane → ℝ) (p v : Plane) :
    coordinateForm U V p v = U p*v.1+V p*v.2 := rfl

theorem coordinateForm_smooth {U V : Plane → ℝ} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (coordinateForm U V) :=
  (hU.smul contDiff_const).add (hV.smul contDiff_const)

theorem coordinateForm_compact {U V : Plane → ℝ} (hU : HasCompactSupport U)
    (hV : HasCompactSupport V) : HasCompactSupport (coordinateForm U V) := by
  apply HasCompactSupport.intro (hU.union hV)
  intro p hp
  have hu : U p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inl h))
  have hv : V p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inr h))
  simp only [coordinateForm,hu,hv,zero_smul,zero_add]

theorem form_eval_fderiv {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (p v w : Plane) : fderiv ℝ (fun q => alpha q w) p v = fderiv ℝ alpha p v w := by
  have he := ((ContinuousLinearMap.apply ℝ ℝ w : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
    ((ha.differentiable (by simp)) p).hasFDerivAt).fderiv
  exact congrArg (fun D : Plane →L[ℝ] ℝ => D v) he

theorem coordinateForm_curl {U V : Plane → ℝ} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) (p : Plane) :
    planarCurl (coordinateForm U V) p =
      deriv (fun x => V (x,p.2)) p.1 - deriv (fun y => U (p.1,y)) p.2 := by
  rw [plane_deriv_first (hV.differentiable (by simp)),
    plane_deriv_second (hU.differentiable (by simp))]
  unfold planarCurl
  rw [← form_eval_fderiv (coordinateForm_smooth hU hV),
    ← form_eval_fderiv (coordinateForm_smooth hU hV)]
  simp only [coordinateForm_apply,mul_zero,mul_one,zero_add,add_zero]

theorem exists_relative_planar_primitive {ι : Type*} [Fintype ι]
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hf0 : (∫ p, f p) = 0) (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRi : Injective R)
    (hz : ∀ i, (∫ p in roundDisk (R i), f p) = 0) :
    ∃ U V : Plane → ℝ, ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧
      HasCompactSupport U ∧ HasCompactSupport V ∧
      (∀ p, deriv (fun x => V (x,p.2)) p.1 - deriv (fun y => U (p.1,y)) p.2 = f p) ∧
      (∀ i p, radiusSq p = (R i)^2 → -p.2*U p+p.1*V p = 0) := by
  obtain ⟨U,V,hU,hV,hUc,hVc,hcurl⟩ := exists_compact_planar_primitive hf hfc hf0
  have hc (p : Plane) : planarCurl (coordinateForm U V) p = f p :=
    (coordinateForm_curl hU hV p).trans (hcurl p)
  have hz' (i : ι) : (∫ p in roundDisk (R i), planarCurl (coordinateForm U V) p) = 0 := by
    simp_rw [hc]
    exact hz i
  obtain ⟨beta,hbs,hbc,hcurlb,hbt⟩ := exists_finite_circle_correction
    (coordinateForm_smooth hU hV) (coordinateForm_compact hUc hVc) R hR hRi hz'
  let U' : Plane → ℝ := fun p => beta p (1,0)
  let V' : Plane → ℝ := fun p => beta p (0,1)
  have hUs : ContDiff ℝ ∞ U' := hbs.clm_apply contDiff_const
  have hVs : ContDiff ℝ ∞ V' := hbs.clm_apply contDiff_const
  have hU'c : HasCompactSupport U' := by
    apply HasCompactSupport.intro hbc
    intro p hp
    simp only [U',image_eq_zero_of_notMem_tsupport hp,zero_apply]
  have hV'c : HasCompactSupport V' := by
    apply HasCompactSupport.intro hbc
    intro p hp
    simp only [V',image_eq_zero_of_notMem_tsupport hp,zero_apply]
  refine ⟨U',V',hUs,hVs,hU'c,hV'c,?_,?_⟩
  · intro p
    rw [plane_deriv_first (hVs.differentiable (by simp)),
      plane_deriv_second (hUs.differentiable (by simp))]
    change fderiv ℝ (fun q => beta q (0,1)) p (1,0) -
      fderiv ℝ (fun q => beta q (1,0)) p (0,1) = f p
    rw [form_eval_fderiv hbs,form_eval_fderiv hbs]
    exact (hcurlb p).trans (hc p)
  · intro i p hp
    have he : (-p.2,p.1) = (-p.2) • ((1:ℝ),(0:ℝ)) + p.1 • ((0:ℝ),(1:ℝ)) := by
      ext <;> simp
    have ht := hbt i p hp
    rw [he,map_add,map_smul,map_smul] at ht
    exact ht

theorem moserField_tangent {f U V : Plane → ℝ} {R : ℝ}
    (ht : ∀ p, radiusSq p = R^2 → -p.2*U p+p.1*V p = 0) :
    ∀ t p, radiusSq p = R^2 → radialDrift (moserField f U V) (t,p) = 0 := by
  intro t p hp
  have he := ht p hp
  unfold radialDrift moserField
  dsimp only
  calc
    2*(p.1*(-deriv Real.smoothTransition t*V p/moserDensity f (t,p)) +
      p.2*(deriv Real.smoothTransition t*U p/moserDensity f (t,p))) =
      (-2*deriv Real.smoothTransition t/moserDensity f (t,p)) * (-p.2*U p+p.1*V p) := by ring
    _ = 0 := by rw [he,mul_zero]

def closedRoundDisk (R : ℝ) : Set Plane := {p | radiusSq p ≤ R^2}

theorem closedRoundDisk_isCompact (R : ℝ) : IsCompact (closedRoundDisk R) := by
  apply (isCompact_closedBall (0 : Plane) (R^2+1)).of_isClosed_subset
    (isClosed_le radiusSq_smooth.continuous continuous_const)
  intro p hp
  rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff,
    Real.norm_eq_abs,Real.norm_eq_abs]
  change p.1^2+p.2^2 ≤ R^2 at hp
  constructor
  · apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg p.2,sq_nonneg (p.1-1),sq_nonneg (p.1+1)]
  · apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg p.1,sq_nonneg (p.2-1),sq_nonneg (p.2+1)]

theorem radiusSq_eq_zero_of_isLocalMax {p : Plane} (hp : IsLocalMax radiusSq p) :
    p = 0 := by
  have h1 : IsLocalMax (fun x : ℝ => x^2+p.2^2) p.1 :=
    hp.comp_continuous (g := fun x : ℝ => (x,p.2))
      (continuousAt_id.prodMk continuousAt_const)
  have h2 : IsLocalMax (fun y : ℝ => p.1^2+y^2) p.2 :=
    hp.comp_continuous (g := fun y : ℝ => (p.1,y))
      (continuousAt_const.prodMk continuousAt_id)
  have hd1 : HasDerivAt (fun x : ℝ => x^2+p.2^2) (2*p.1) p.1 := by
    simpa using (hasDerivAt_pow 2 p.1).add_const (p.2^2)
  have hd2 : HasDerivAt (fun y : ℝ => p.1^2+y^2) (2*p.2) p.2 := by
    simpa using (hasDerivAt_pow 2 p.2).const_add (p.1^2)
  have he1 : 2*p.1 = 0 := hd1.deriv.symm.trans h1.deriv_eq_zero
  have he2 : 2*p.2 = 0 := hd2.deriv.symm.trans h2.deriv_eq_zero
  apply Prod.ext <;> dsimp <;> linarith

theorem homeomorph_mapsTo_closedRoundDisk (Φ : Plane ≃ₜ Plane) (R : ℝ)
    (hcircle : ∀ p, radiusSq p = R^2 → radiusSq (Φ p) = R^2) :
    MapsTo Φ (closedRoundDisk R) (closedRoundDisk R) := by
  have hne : (closedRoundDisk R).Nonempty := ⟨0,by simp [closedRoundDisk,radiusSq,sq_nonneg]⟩
  obtain ⟨p,hp,hm⟩ := (closedRoundDisk_isCompact R).exists_isMaxOn hne
    (radiusSq_smooth.continuous.comp Φ.continuous).continuousOn
  have hbound : radiusSq (Φ p) ≤ R^2 := by
    by_cases he : radiusSq p = R^2
    · exact (hcircle p he).le
    · have hlt : radiusSq p < R^2 := lt_of_le_of_ne hp he
      have hnhds : closedRoundDisk R ∈ 𝓝 p :=
        Filter.mem_of_superset ((isOpen_lt radiusSq_smooth.continuous continuous_const).mem_nhds hlt)
          (fun q (hq : radiusSq q < R^2) => (show q ∈ closedRoundDisk R from hq.le))
      have hlocal : IsLocalMax (radiusSq ∘ Φ) p := hm.isLocalMax hnhds
      have hlocal' : IsLocalMax (radiusSq ∘ Φ) (Φ.symm (Φ p)) := by simpa using hlocal
      have hcomp := hlocal'.comp_continuous Φ.symm.continuous.continuousAt
      have hz : Φ p = 0 := radiusSq_eq_zero_of_isLocalMax (by
        simpa only [Function.comp_def,Homeomorph.apply_symm_apply] using hcomp)
      simpa only [hz,radiusSq,Prod.fst_zero,Prod.snd_zero,zero_pow (by norm_num : 2 ≠ 0),zero_add]
        using sq_nonneg R
  intro q hq
  exact (hm hq).trans hbound

theorem homeomorph_mapsTo_roundDisk (Φ : Plane ≃ₜ Plane) (R : ℝ)
    (hcircle : ∀ p, radiusSq (Φ p) = R^2 ↔ radiusSq p = R^2) :
    MapsTo Φ (roundDisk R) (roundDisk R) := by
  intro p hp
  have hle := homeomorph_mapsTo_closedRoundDisk Φ R (fun p => (hcircle p).mpr)
    (show p ∈ closedRoundDisk R from (show radiusSq p ≤ R^2 from le_of_lt hp))
  change radiusSq (Φ p) < R^2
  apply lt_of_le_of_ne hle
  intro he
  exact (ne_of_lt hp) ((hcircle p).mp he)

theorem homeomorph_image_roundDisk (Φ : Plane ≃ₜ Plane) (R : ℝ)
    (hcircle : ∀ p, radiusSq (Φ p) = R^2 ↔ radiusSq p = R^2) :
    Φ '' roundDisk R = roundDisk R := by
  apply Set.Subset.antisymm
  · exact (homeomorph_mapsTo_roundDisk Φ R hcircle).image_subset
  · intro p hp
    have hi : ∀ q, radiusSq (Φ.symm q) = R^2 ↔ radiusSq q = R^2 := by
      intro q
      simpa only [Homeomorph.apply_symm_apply] using (hcircle (Φ.symm q)).symm
    exact ⟨Φ.symm p,homeomorph_mapsTo_roundDisk Φ.symm R hi hp,Φ.apply_symm_apply p⟩

theorem exists_density_transport_relative {ι : Type*} {L : ℝ≥0}
    (X : C(ℝ × Plane,Plane)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    (ρ : ℝ × Plane → ℝ) (hρ : ContDiff ℝ ∞ ρ) (B : Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (hPDE : ∀ p v w, fderiv ℝ ρ p (1,X p) * B v w +
      ρ p * (B (fderiv ℝ X p (0,v)) w + B v (fderiv ℝ X p (0,w))) = 0)
    (K : Set Plane) (hK : IsCompact K) (hXspt : ∀ s x, x ∉ K → X (s,x) = 0)
    (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (htan : ∀ i t x, radiusSq x = (R i)^2 → radialDrift X (t,x) = 0)
    (t T : ℝ) : ∃ Φ : Plane ≃ₜ Plane, ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      (∀ x, x ∉ K → Φ x = x) ∧ HasCompactSupport (fun x => Φ x - x) ∧
      (∀ x v w, ρ (t+T,Φ x) * B (fderiv ℝ Φ x v) (fderiv ℝ Φ x w) = ρ (t,x) * B v w) ∧
      (∀ i x, radiusSq (Φ x) = (R i)^2 ↔ radiusSq x = (R i)^2) ∧
      (∀ i, Φ '' roundDisk (R i) = roundDisk (R i)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (‖T‖ * L)
  have hN0 : (0:ℝ) < N := (mul_nonneg (norm_nonneg _) L.coe_nonneg).trans_lt hN
  let h := T / N
  have hh : ‖h‖ * L < 1 := by
    change ‖T / (N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le, div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr hN
  have he : (N:ℝ) * h = T := by dsimp [h]; field_simp
  let Φ := timeSteps X hX hXs hh t N
  have hfix (x : Plane) (hx : x ∉ K) : Φ x = x :=
    timeSteps_of_stationary X hX hXs hh t N (fun s => hXspt s x hx)
  have hcircle (i : ι) (x : Plane) : radiusSq (Φ x) = (R i)^2 ↔ radiusSq x = (R i)^2 :=
    timeSteps_preserves_circle_iff X hX hXs hXc (hR i) (htan i) hh t N x
  refine ⟨Φ,(timeSteps_smooth X hX hXs hh t N).1,
    (timeSteps_smooth X hX hXs hh t N).2,hfix,?_,?_,hcircle,?_⟩
  · exact HasCompactSupport.intro hK (fun x hx => sub_eq_zero.mpr (hfix x hx))
  · intro x v w
    simpa only [he] using timeSteps_preserves_density X hX hXs ρ hρ B hPDE hh t N x v w
  · intro i
    exact homeomorph_image_roundDisk Φ (R i) (hcircle i)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
