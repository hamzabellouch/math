import OAI.Probability.SLE.Stochastic.PlanarLogLifting

namespace OAI

/-! A continuous injection of a closed planar disk contains a neighborhood
of its center image. The proof uses exponential-covering homotopy lifting. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma planar_closedBall_image_contains_ball
    (f : ℂ → ℂ) (r δ : ℝ) (hr : 0<r)
    (hf : ContinuousOn f (closedBall 0 r)) (hi : InjOn f (closedBall 0 r))
    (hsep : ∀ z∈sphere (0:ℂ) r, δ≤‖f z-f 0‖) :
    ball (f 0) δ ⊆ f '' closedBall 0 r := by
  intro y hy
  by_contra hmiss
  have hyδ : ‖y-f 0‖<δ := by simpa only [mem_ball,dist_eq_norm] using hy
  have hn (z : ℂ) (hz : z∈closedBall 0 r) : f z-y≠0 := by
    intro he
    exact hmiss ⟨z,hz,sub_eq_zero.mp he⟩
  let S := sphere (0:ℂ) r
  have hS : IsPreconnected S := isPreconnected_sphere (by simp) 0 r
  have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  have hnorm (z : S) : ‖(z:ℂ)‖=r := by
    simpa only [S,mem_sphere,dist_zero_right] using z.property
  have hc : Continuous (fun z : S => f z) :=
    hf.comp_continuous continuous_subtype_val (fun z => sphere_subset_closedBall z.property)
  have hscale (q : unitInterval × S) : ((q.1:ℝ):ℂ)*(q.2:ℂ)∈closedBall (0:ℂ) r := by
    rw [mem_closedBall,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg q.1.property.1,hnorm]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right q.1.property.2 hr.le
  have hnscale (q : unitInterval × S) : -(((q.1:ℝ):ℂ)*(q.2:ℂ))∈closedBall (0:ℂ) r := by
    simpa only [mem_closedBall,dist_zero_right,norm_neg] using hscale q
  have hsc : Continuous (fun q : unitInterval × S => f (((q.1:ℝ):ℂ)*(q.2:ℂ))) :=
    hf.comp_continuous (by fun_prop) hscale
  have hsn : Continuous (fun q : unitInterval × S => f (-(((q.1:ℝ):ℂ)*(q.2:ℂ)))) :=
    hf.comp_continuous (by fun_prop) hnscale
  let H₁ : C(unitInterval × S,ℂ) := ⟨fun q => f (((q.1:ℝ):ℂ)*(q.2:ℂ))-y,
    hsc.sub continuous_const⟩
  obtain ⟨L₁,hL₁⟩ := continuous_log_at_end_of_homotopy H₁
    (fun q => hn _ (hscale q)) (.const S (Complex.log (f 0-y))) (by
      intro z
      simpa [H₁] using Complex.exp_log (hn 0 (mem_closedBall_self hr.le)))
  have hL₁' (z : S) : Complex.exp (L₁ z)=f z-y := by simpa [H₁] using hL₁ z
  let H₂ : C(unitInterval × S,ℂ) :=
    ⟨fun q => f q.2-f 0-(1-((q.1:ℝ):ℂ))*(y-f 0),by
      exact (hc.comp continuous_snd).sub continuous_const |>.sub (by fun_prop)⟩
  have hH₂ (q : unitInterval × S) : H₂ q≠0 := by
    intro he
    have heq : f q.2-f 0=(1-((q.1:ℝ):ℂ))*(y-f 0) := sub_eq_zero.mp he
    have ht : ‖1-((q.1:ℝ):ℂ)‖≤1 := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr q.1.property.2)]
      linarith [q.1.property.1]
    have hsmall : ‖f q.2-f 0‖<δ := by
      rw [heq,norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans_lt hyδ
    exact not_lt_of_ge (hsep q.2 q.2.property) hsmall
  obtain ⟨L₂,hL₂⟩ := continuous_log_at_end_of_homotopy H₂ hH₂ L₁ (by
    intro z
    rw [hL₁']
    dsimp [H₂]
    ring)
  have hL₂' (z : S) : Complex.exp (L₂ z)=f z-f 0 := by simpa [H₂] using hL₂ z
  let H₃ : C(unitInterval × S,ℂ) := ⟨fun q => f q.2-f (-(((q.1:ℝ):ℂ)*(q.2:ℂ))),
    (hc.comp continuous_snd).sub hsn⟩
  have hH₃ (q : unitInterval × S) : H₃ q≠0 := by
    intro he
    have heq := hi (sphere_subset_closedBall q.2.property) (hnscale q) (sub_eq_zero.mp he)
    have hz0 : (q.2:ℂ)≠0 := by
      intro hz
      have := hnorm q.2
      rw [hz,norm_zero] at this
      exact hr.ne' this.symm
    have hp : (1+((q.1:ℝ):ℂ))*(q.2:ℂ)=0 := by linear_combination heq
    have hp0 := (mul_eq_zero.mp hp).resolve_right hz0
    have hpR : (1:ℝ)+(q.1:ℝ)=0 := by exact_mod_cast hp0
    linarith [q.1.property.1]
  obtain ⟨L₃,hL₃⟩ := continuous_log_at_end_of_homotopy H₃ hH₃ L₂ (by
    intro z
    simpa [H₃] using hL₂' z)
  let J : S → S := fun z => ⟨-z,by simpa only [S,mem_sphere,dist_zero_right,norm_neg] using z.property⟩
  have hJ : Continuous J := (continuous_subtype_val.neg).subtype_mk _
  have hJi : Involutive J := fun z => Subtype.ext (neg_neg z.1)
  let F : C(S,ℂ) := ⟨fun z => f z-f (-z),hc.sub (hf.comp_continuous
    (continuous_subtype_val.neg) (fun z => by
      simpa only [mem_closedBall,dist_zero_right,norm_neg] using sphere_subset_closedBall z.property))⟩
  have hF (z : S) : F z≠0 := by simpa [F,H₃] using hH₃ (1,z)
  have hodd (z : S) : F (J z)= -F z := by dsimp [F,J]; rw [neg_neg]; ring
  have hlog (z : S) : Complex.exp (L₃ z)=F z := by simpa [F,H₃] using hL₃ z
  have ha : (r:ℂ)∈S := by
    simp only [S,mem_sphere,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  exact no_continuous_log_of_odd_involution J hJ hJi F L₃ hF hodd hlog ⟨r,ha⟩

end SLEExactGauge

end

end OAI
