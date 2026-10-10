import OAI.Probability.SLE.Stochastic.PlanarLogLifting

namespace OAI

/-! A locally injective isolated zero has nontrivial boundary monodromy.
This is the local obstruction used for separating the sides of a crosscut. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma univalent_boundary_no_continuous_log (f : ℂ → ℂ) (r : ℝ) (hr : 0<r)
    (hf : ContinuousOn f (closedBall 0 r)) (hi : InjOn f (closedBall 0 r))
    (L : C(sphere (0:ℂ) r,ℂ)) (hL : ∀ z, Complex.exp (L z)=f z-f 0) : False := by
  let S := sphere (0:ℂ) r
  have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere (by simp) 0 r)
  have hn (z : S) : ‖(z:ℂ)‖=r := by simpa only [S,mem_sphere,dist_zero_right] using z.property
  have hc : Continuous (fun z : S => f z) :=
    hf.comp_continuous continuous_subtype_val (fun z => sphere_subset_closedBall z.property)
  have hns (q : unitInterval × S) : -((q.1:ℂ)*(q.2:ℂ))∈closedBall (0:ℂ) r := by
    rw [mem_closedBall,dist_zero_right,norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg q.1.property.1,hn]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right q.1.property.2 hr.le
  let H : C(unitInterval × S,ℂ) := ⟨fun q => f q.2-f (-((q.1:ℂ)*(q.2:ℂ))),
    (hc.comp continuous_snd).sub (hf.comp_continuous (by fun_prop) hns)⟩
  have hH (q : unitInterval × S) : H q≠0 := by
    intro he
    have heq := hi (sphere_subset_closedBall q.2.property) (hns q) (sub_eq_zero.mp he)
    have hz : (q.2:ℂ)≠0 := by
      intro hz
      have := hn q.2
      rw [hz,norm_zero] at this
      exact hr.ne' this.symm
    have hp : (1+(q.1:ℂ))*(q.2:ℂ)=0 := by linear_combination heq
    have hp0 := (mul_eq_zero.mp hp).resolve_right hz
    have hpR : (1:ℝ)+(q.1:ℝ)=0 := by exact_mod_cast hp0
    linarith [q.1.property.1]
  obtain ⟨M,hM⟩ := continuous_log_at_end_of_homotopy H hH L (by intro z; simpa [H] using hL z)
  let J : S → S := fun z => ⟨-z,by simpa only [S,mem_sphere,dist_zero_right,norm_neg] using z.property⟩
  have hJ : Continuous J := continuous_subtype_val.neg.subtype_mk _
  let F : C(S,ℂ) := ⟨fun z => f z-f (-z),hc.sub (hf.comp_continuous
    continuous_subtype_val.neg (fun z => by
      simpa only [mem_closedBall,dist_zero_right,norm_neg] using sphere_subset_closedBall z.property))⟩
  apply no_continuous_log_of_odd_involution J hJ (fun z => Subtype.ext (neg_neg z.1)) F M
    (fun z => by simpa [F,H] using hH (1,z))
    (fun z => by dsimp [F,J]; rw [neg_neg]; ring)
    (fun z => by simpa [F,H] using hM z)
    ⟨r,by simp [S,abs_of_pos hr]⟩

lemma isolated_zero_no_continuous_boundary_log (f : ℂ → ℂ) (r ρ : ℝ)
    (hr : 0<r) (hρ : 0<ρ) (hρr : ρ≤r)
    (hf : ContinuousOn f (closedBall 0 r))
    (hz : ∀ z∈closedBall 0 r, f z=f 0 → z=0)
    (hi : InjOn f (closedBall 0 ρ))
    (L : C(sphere (0:ℂ) r,ℂ)) (hL : ∀ z, Complex.exp (L z)=f z-f 0) : False := by
  let S := sphere (0:ℂ) r
  let s (t : unitInterval) : ℝ := 1-(t:ℝ)+(t:ℝ)*(ρ/r)
  have hs (t : unitInterval) : 0<s t ∧ s t≤1 := by
    have hd : 0<ρ/r := div_pos hρ hr
    have hle : ρ/r≤1 := (div_le_one hr).mpr hρr
    constructor
    · dsimp [s]
      by_cases ht : (t:ℝ)=1
      · simp [ht,hd]
      · have hlt : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 ht
        nlinarith [mul_nonneg t.property.1 hd.le]
    · dsimp [s]
      nlinarith [mul_le_mul_of_nonneg_left hle t.property.1]
  have hn (z : S) : ‖(z:ℂ)‖=r := by simpa only [S,mem_sphere,dist_zero_right] using z.property
  have hscale (q : unitInterval × S) : (s q.1:ℂ)*(q.2:ℂ)∈closedBall (0:ℂ) r := by
    rw [mem_closedBall,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (hs q.1).1,hn]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hs q.1).2 hr.le
  let H : C(unitInterval × S,ℂ) := ⟨fun q => f ((s q.1:ℂ)*(q.2:ℂ))-f 0,
    (hf.comp_continuous (by dsimp [s]; fun_prop) hscale).sub continuous_const⟩
  have hH (q : unitInterval × S) : H q≠0 := by
    intro he
    have he0 := hz _ (hscale q) (sub_eq_zero.mp he)
    have heq := congrArg norm he0
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hs q.1).1,hn,norm_zero] at heq
    exact (mul_pos (hs q.1).1 hr).ne' heq
  obtain ⟨M,hM⟩ := continuous_log_at_end_of_homotopy H hH L (by intro z; simpa [H,s] using hL z)
  let e : sphere (0:ℂ) ρ → S := fun z => ⟨((r/ρ:ℝ):ℂ)*(z:ℂ),by
    rw [mem_sphere,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (div_pos hr hρ)]
    have hnz : ‖(z:ℂ)‖=ρ := by simpa only [mem_sphere,dist_zero_right] using z.property
    rw [hnz,div_mul_cancel₀ _ hρ.ne']⟩
  have hec : Continuous e := (continuous_const.mul continuous_subtype_val).subtype_mk _
  apply univalent_boundary_no_continuous_log f ρ hρ
    (hf.mono (closedBall_subset_closedBall hρr)) hi (M.comp ⟨e,hec⟩)
  intro z
  have harg : ((ρ/r:ℝ):ℂ)*(((r/ρ:ℝ):ℂ)*(z:ℂ))=(z:ℂ) := by
    push_cast
    field_simp [hr.ne',hρ.ne']
  simpa only [ContinuousMap.comp_apply,H,ContinuousMap.coe_mk,s,
    Set.Icc.coe_one,sub_self,zero_add,one_mul,e,harg] using hM (e z)

end SLEExactGauge

end

end OAI
