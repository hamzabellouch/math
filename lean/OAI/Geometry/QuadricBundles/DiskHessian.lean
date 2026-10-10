import OAI.Geometry.QuadricBundles.Graphs

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Laplacian InnerProductSpace
noncomputable section

lemma _root_.OAI.IsLocalMax.second_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] fun _ ↦ f x := by
    filter_upwards [hm,hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hd : deriv f =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [he.eventuallyEq_nhds] with y hy
    rw [hy.deriv_eq,deriv_const]
  have hz : deriv (deriv f) x=0 := by rw [hd.deriv_eq,deriv_const]
  exact hp.ne' hz

lemma deriv_affine_eventually {X : Type u1} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u : X → ℝ} {x v : X} (hu : ContDiffAt ℝ 2 u x) :
    deriv (fun t : ℝ ↦ u (x+t • v)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t ↦ fderiv ℝ u (x+t • v) v) := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y :=
    hu.eventually (by norm_num) |>.mono fun _ h ↦
      h.differentiableAt (by norm_num)
  have htend : Tendsto (fun t : ℝ ↦ x+t • v) (𝓝 0) (𝓝 x) := by
    have hc : ContinuousAt (fun t : ℝ ↦ x+t • v) 0 := by fun_prop
    simpa only [zero_smul,add_zero] using hc.tendsto
  filter_upwards [htend hd] with t ht
  have hl : HasDerivAt (fun t : ℝ ↦ x+t • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v |>.const_add x
  exact (ht.hasFDerivAt.comp_hasDerivAt t hl).deriv

lemma hasDerivAt_fderiv_affine {X : Type u2} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u : X → ℝ} {x v : X} (hu : ContDiffAt ℝ 2 u x) :
    HasDerivAt (fun t : ℝ ↦ fderiv ℝ u (x+t • v) v)
      ((fderiv ℝ (fderiv ℝ u) x v) v) 0 := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hline : HasDerivAt (fun t : ℝ ↦ x+t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add x
  have hfd' : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) (x+(0 : ℝ) • v) := by
    simpa only [zero_smul,add_zero] using hfd.hasFDerivAt
  have hh : HasDerivAt (fun t : ℝ ↦ fderiv ℝ u (x+t • v))
      (fderiv ℝ (fderiv ℝ u) x v) 0 := hfd'.comp_hasDerivAt 0 hline
  have hv : HasDerivAt (fun _ : ℝ ↦ v) 0 0 := hasDerivAt_const 0 v
  simpa only [map_zero,add_zero] using hh.clm_apply hv

lemma second_deriv_affine {X : Type u3} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u : X → ℝ} {x v : X} (hu : ContDiffAt ℝ 2 u x) :
    deriv (deriv (fun t : ℝ ↦ u (x+t • v))) 0 =
      (fderiv ℝ (fderiv ℝ u) x v) v := by
  rw [(deriv_affine_eventually hu).deriv_eq]
  exact (hasDerivAt_fderiv_affine hu).deriv

lemma _root_.OAI.IsLocalMax.hessian_nonpos {X : Type u4} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u : X → ℝ} {x : X} (hm : IsLocalMax u x) (hu : ContDiffAt ℝ 2 u x) (v : X) :
    (fderiv ℝ (fderiv ℝ u) x v) v ≤ 0 := by
  rw [← second_deriv_affine hu]
  have hc : ContinuousAt (fun t : ℝ ↦ x+t • v) 0 := by fun_prop
  have hm' : IsLocalMax (fun t : ℝ ↦ u (x+t • v)) 0 := by
    have ht : Tendsto (fun t : ℝ ↦ x+t • v) (𝓝 0) (𝓝 x) := by
      simpa only [zero_smul,add_zero] using hc.tendsto
    change ∀ᶠ t in 𝓝 (0 : ℝ), u (x+t • v) ≤ u (x+0 • v)
    simpa only [zero_smul,add_zero] using ht.eventually hm
  apply _root_.OAI.IsLocalMax.second_deriv_nonpos hm'
  apply ContinuousAt.comp _ hc
  simpa only [zero_smul,add_zero] using hu.continuousAt

def complexLaplacian (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (fderiv ℝ (fderiv ℝ u) z 1) 1 +
  (fderiv ℝ (fderiv ℝ u) z Complex.I) Complex.I

lemma _root_.OAI.IsLocalMax.complexLaplacian_nonpos {u : ℂ → ℝ} {z : ℂ}
    (hm : IsLocalMax u z) (hu : ContDiffAt ℝ 2 u z) : complexLaplacian u z ≤ 0 :=
  add_nonpos (_root_.OAI.IsLocalMax.hessian_nonpos hm hu 1) (_root_.OAI.IsLocalMax.hessian_nonpos hm hu Complex.I)

lemma rotated_hessian_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (a : ℂ) :
    (B a) a + (B (Complex.I*a)) (Complex.I*a) =
      Complex.normSq a * ((B 1) 1 + (B Complex.I) Complex.I) := by
  have ha : a=a.re • (1 : ℂ) + a.im • Complex.I := by
    apply Complex.ext <;> simp
  have hi : Complex.I*a = (-a.im) • (1 : ℂ) + a.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  rw [hi]
  conv_lhs => lhs; rw [ha]
  simp only [map_add,map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [Complex.normSq_apply]
  ring

lemma complexLaplacian_norm_sq (z : ℂ) :
    complexLaplacian (fun x : ℂ ↦ ‖x‖^2) z=4 := by
  unfold complexLaplacian
  rw [fderiv_norm_sq]
  have hh : fderiv ℝ (fun x : ℂ ↦ ((2 : ℝ) • (innerSL ℝ (E := ℂ))) x) z =
      (2 : ℝ) • (innerSL ℝ (E := ℂ)) := ((2 : ℝ) • (innerSL ℝ (E := ℂ))).fderiv
  have he : (2 • ⇑(innerSL ℝ (E := ℂ)) : ℂ → ℂ →L[ℝ] ℝ) =
      (fun x : ℂ ↦ ((2 : ℝ) • innerSL ℝ (E := ℂ)) x) := by
    ext x y
    simp [two_smul]
  rw [he,hh]
  change 2 * @inner ℝ ℂ _ 1 1 + 2 * @inner ℝ ℂ _ Complex.I Complex.I = 4
  norm_num

lemma hessian_add {X : Type u5} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u v : X → ℝ} {x : X} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    fderiv ℝ (fderiv ℝ (u+v)) x =
      fderiv ℝ (fderiv ℝ u) x + fderiv ℝ (fderiv ℝ v) x := by
  have he : fderiv ℝ (u+v) =ᶠ[𝓝 x] (fun y ↦ fderiv ℝ u y + fderiv ℝ v y) := by
    filter_upwards [hu.eventually (by norm_num),hv.eventually (by norm_num)] with y hy hy'
    exact fderiv_add (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact fderiv_add
    ((hu.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt (by norm_num))
    ((hv.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt (by norm_num))

lemma complexLaplacian_add {u v : ℂ → ℝ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) (hv : ContDiffAt ℝ 2 v z) :
    complexLaplacian (u+v) z=complexLaplacian u z+complexLaplacian v z := by
  simp only [complexLaplacian,hessian_add hu hv,add_apply]
  ring

lemma hessian_smul {X : Type u6} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u : X → ℝ} {x : X} (hu : ContDiffAt ℝ 2 u x) (a : ℝ) :
    fderiv ℝ (fderiv ℝ (a • u)) x = a • fderiv ℝ (fderiv ℝ u) x := by
  have he : fderiv ℝ (a • u) =ᶠ[𝓝 x] (fun y ↦ a • fderiv ℝ u y) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact fderiv_const_smul (hy.differentiableAt (by norm_num)) a
  rw [he.fderiv_eq]
  exact fderiv_const_smul
    ((hu.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt (by norm_num)) a

lemma complexLaplacian_smul {u : ℂ → ℝ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) (a : ℝ) :
    complexLaplacian (a • u) z=a*complexLaplacian u z := by
  simp only [complexLaplacian,hessian_smul hu,smul_apply,smul_eq_mul]
  ring

lemma C2_le_boundary {u : ℂ → ℝ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hc : ContinuousOn u (closedBall c R))
    (hu : ContDiffOn ℝ 2 u (ball c R))
    (hΔ : ∀ z ∈ ball c R, 0 ≤ complexLaplacian u z)
    (hb : ∀ z ∈ sphere c R, u z ≤ M) : ∀ z ∈ closedBall c R, u z ≤ M := by
  have heps (ε : ℝ) (hε : 0 < ε) (z : ℂ) (hz : z∈closedBall c R) :
      u z ≤ M+ε*(‖c‖+R)^2 := by
    let v : ℂ → ℝ := u+ε • (fun x : ℂ ↦ ‖x‖^2)
    have hvc : ContinuousOn v (closedBall c R) := hc.add (continuousOn_const.mul (by fun_prop))
    obtain ⟨x,hx,hmax⟩ := (isCompact_closedBall c R).exists_isMaxOn
      ⟨c,mem_closedBall_self hR.le⟩ hvc
    have hxb : x∈sphere c R := by
      by_contra hn
      have hxi : x∈ball c R := by
        rw [mem_ball,mem_closedBall] at *
        exact lt_of_le_of_ne hx (by simpa only [mem_sphere] using hn)
      have hux : ContDiffAt ℝ 2 u x := (hu x hxi).contDiffAt (isOpen_ball.mem_nhds hxi)
      have hnx : ContDiffAt ℝ 2 (fun y : ℂ ↦ ‖y‖^2) x := (contDiff_norm_sq ℝ).contDiffAt
      have hmx : IsLocalMax v x := by
        filter_upwards [closedBall_mem_nhds_of_mem hxi] with y hy
        exact hmax hy
      have hnΔ := _root_.OAI.IsLocalMax.complexLaplacian_nonpos hmx (hux.add (ContDiffAt.const_smul ε hnx))
      have hpΔ : complexLaplacian v x=complexLaplacian u x+4*ε := by
        change complexLaplacian (u+ε • (fun y : ℂ ↦ ‖y‖^2)) x = _
        rw [complexLaplacian_add (v := ε • (fun y : ℂ ↦ ‖y‖^2)) hux
          (ContDiffAt.const_smul ε hnx),complexLaplacian_smul hnx,
          complexLaplacian_norm_sq]
        ring
      rw [hpΔ] at hnΔ
      linarith [hΔ x hxi]
    have hnorm : ‖x‖ ≤ ‖c‖+R := by
      have hd : ‖x-c‖=R := by simpa [mem_sphere,dist_eq_norm] using hxb
      calc ‖x‖ = ‖(x-c)+c‖ := by congr 1; abel
           _ ≤ ‖x-c‖+‖c‖ := norm_add_le _ _
           _ = ‖c‖+R := by rw [hd]; ring
    have hsq : ‖x‖^2 ≤ (‖c‖+R)^2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hnorm
    have hvz := hmax hz
    have hub := hb x hxb
    change u z+ε*‖z‖^2 ≤ u x+ε*‖x‖^2 at hvz
    nlinarith [mul_le_mul_of_nonneg_left hsq hε.le, mul_nonneg hε.le (sq_nonneg ‖z‖)]
  intro z hz
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := δ/((‖c‖+R)^2+1)
  have hden : 0 < (‖c‖+R)^2+1 := by positivity
  have hp : 0 < ε := div_pos hδ hden
  have heq : ε*((‖c‖+R)^2+1)=δ := by dsimp [ε]; exact div_mul_cancel₀ _ hden.ne'
  have hh := heps ε hp z hz
  linarith

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory
noncomputable section

section
variable {α : Type u7} {X : Type u8} {Y : Type u9} [TopologicalSpace α] [CompactSpace α] [T2Space α]
  [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {D : Set X} {F : α → X → Y} {F' : α → X → X →L[ℝ] Y}

omit [NormedSpace ℝ X] [ProperSpace X] [NormedSpace ℝ Y] in
lemma compactParameter_integrable {z : X} (hz : z∈D)
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ D)) :
    Integrable (fun a ↦ F a z) μ := by
  have h : Continuous (fun a ↦ F a z) :=
    hc.comp_continuous (f := fun a ↦ (a,z)) (by fun_prop) (fun a ↦ ⟨mem_univ a,hz⟩)
  exact integrableOn_univ.mp (h.continuousOn.integrableOn_compact isCompact_univ)

omit [NormedSpace ℝ X] in
lemma compactParameter_continuousAtIntegral (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ D)) {z : X} (hz : z∈D) :
    ContinuousAt (fun x ↦ ∫ a, F a x ∂μ) z := by
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hD.mem_nhds hz)
  obtain ⟨C,hC⟩ := (isCompact_univ.prod (isCompact_closedBall z r)).exists_bound_of_continuousOn
    (hc.mono (prod_mono (Subset.refl univ) hball))
  apply continuousAt_of_dominated (F := fun x a ↦ F a x) (bound := fun _ ↦ C)
  · filter_upwards [hD.mem_nhds hz] with x hx
    exact (compactParameter_integrable hx hc).aestronglyMeasurable
  · filter_upwards [closedBall_mem_nhds z hr] with x hx
    exact Eventually.of_forall fun a ↦ hC (a,x) ⟨mem_univ a,hx⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun a ↦
      (hc (a,z) ⟨mem_univ a,hz⟩).continuousAt
        ((isOpen_univ.prod hD).mem_nhds ⟨mem_univ a,hz⟩) |>.comp
          (continuousAt_const.prodMk continuousAt_id)

lemma compactParameter_hasFDerivAtIntegral (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ D))
    (hc' : ContinuousOn (Function.uncurry F') (univ ×ˢ D))
    (hd : ∀ a z, z∈D → HasFDerivAt (F a) (F' a z) z) {z : X} (hz : z∈D) :
    HasFDerivAt (fun x ↦ ∫ a, F a x ∂μ) (∫ a, F' a z ∂μ) z := by
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hD.mem_nhds hz)
  obtain ⟨C,hC⟩ := (isCompact_univ.prod (isCompact_closedBall z r)).exists_bound_of_continuousOn
    (hc'.mono (prod_mono (Subset.refl univ) hball))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x a ↦ F a x) (F' := fun x a ↦ F' a x)
    (bound := fun _ ↦ C) (closedBall_mem_nhds z hr)
  · filter_upwards [hD.mem_nhds hz] with x hx
    exact (compactParameter_integrable hx hc).aestronglyMeasurable
  · exact compactParameter_integrable hz hc
  · exact (compactParameter_integrable hz hc').aestronglyMeasurable
  · exact Eventually.of_forall fun a x hx ↦ hC (a,x) ⟨mem_univ a,hx⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun a x hx ↦ hd a x (hball hx)

lemma compactParameter_secondFDerivIntegral (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ D))
    (hc' : ContinuousOn (Function.uncurry F') (univ ×ˢ D))
    {F'' : α → X → X →L[ℝ] X →L[ℝ] Y}
    (hc'' : ContinuousOn (Function.uncurry F'') (univ ×ˢ D))
    (hd : ∀ a z, z∈D → HasFDerivAt (F a) (F' a z) z)
    (hd' : ∀ a z, z∈D → HasFDerivAt (F' a) (F'' a z) z)
    {z : X} (hz : z∈D) :
    fderiv ℝ (fderiv ℝ (fun x ↦ ∫ a, F a x ∂μ)) z = ∫ a, F'' a z ∂μ := by
  have he : fderiv ℝ (fun x ↦ ∫ a, F a x ∂μ) =ᶠ[𝓝 z] fun x ↦ ∫ a, F' a x ∂μ := by
    filter_upwards [hD.mem_nhds hz] with x hx
    exact (compactParameter_hasFDerivAtIntegral hD hc hc' hd hx).fderiv
  rw [he.fderiv_eq]
  exact (compactParameter_hasFDerivAtIntegral hD hc' hc'' hd' hz).fderiv
lemma compactParameter_contDiffOn_one_Integral (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ D))
    (hc' : ContinuousOn (Function.uncurry F') (univ ×ˢ D))
    (hd : ∀ a z, z∈D → HasFDerivAt (F a) (F' a z) z) :
    ContDiffOn ℝ 1 (fun x ↦ ∫ a, F a x ∂μ) D := by
  rw [show (1 : WithTop ℕ∞)=0+1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hD]
  refine ⟨fun z hz ↦ (compactParameter_hasFDerivAtIntegral hD hc hc' hd hz).differentiableAt.differentiableWithinAt,
    fun h ↦ by simp at h, ?_⟩
  rw [contDiffOn_zero]
  have hh : ContinuousOn (fun x ↦ ∫ a, F' a x ∂μ) D :=
    fun z hz ↦ (compactParameter_continuousAtIntegral hD hc' hz).continuousWithinAt
  apply hh.congr
  intro x hx
  exact (compactParameter_hasFDerivAtIntegral hD hc hc' hd hx).fderiv

lemma compactParameter_contDiffOn_two_Integral (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ D))
    (hc' : ContinuousOn (Function.uncurry F') (univ ×ˢ D))
    {F'' : α → X → X →L[ℝ] X →L[ℝ] Y}
    (hc'' : ContinuousOn (Function.uncurry F'') (univ ×ˢ D))
    (hd : ∀ a z, z∈D → HasFDerivAt (F a) (F' a z) z)
    (hd' : ∀ a z, z∈D → HasFDerivAt (F' a) (F'' a z) z) :
    ContDiffOn ℝ 2 (fun x ↦ ∫ a, F a x ∂μ) D := by
  rw [show (2 : WithTop ℕ∞)=1+1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hD]
  refine ⟨fun z hz ↦ (compactParameter_hasFDerivAtIntegral hD hc hc' hd hz).differentiableAt.differentiableWithinAt,
    fun h ↦ by simp at h, ?_⟩
  apply (compactParameter_contDiffOn_one_Integral (μ := μ) hD hc' hc'' hd').congr
  intro x hx
  exact (compactParameter_hasFDerivAtIntegral hD hc hc' hd hx).fderiv

end

end
end QuadricCounterexample

end OAI
