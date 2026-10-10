import OAI.MathematicalPhysics.Heisenberg.SpinFieldUniform

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma dynamics_norm (t : ℝ) (B : QuasiLocal d ℓ) : ‖dynamics d ℓ t B‖=‖B‖ := by
  classical
  have h:=((dynamics_converges d ℓ t B).norm)
  have hn (n : ℕ) := norm_finiteDynamics d ℓ (box d n) t B
  simp only [hn] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

lemma dynamics_continuous (B : QuasiLocal d ℓ) : Continuous (fun t=>dynamics d ℓ t B) :=
  (dynamics_locallyUniform d ℓ B).continuous
    (Filter.Eventually.of_forall (fun n=>(finiteDynamics_equicontinuous d ℓ B).continuous (box d n))).frequently

lemma state_limit_locallyUniform {η : ℕ → State d ℓ} {ω : State d ℓ}
    (hη : ∀ A,Tendsto (fun n=>(η n).functional A) atTop (𝓝 (ω.functional A)))
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ) :
    TendstoLocallyUniformly (fun n t=>(η n).functional (M (dynamics d ℓ t B)))
      (fun t=>ω.functional (M (dynamics d ℓ t B))) atTop := by
  classical
  apply EquicontinuousLimits.locallyUniform
  · apply EquicontinuousLimits.equicontinuous_apply (C:=4) (by norm_num) (fun n=>state_norm_bound (η n))
    intro t
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ,hδ,hh⟩:=Metric.continuousAt_iff.mp (M.continuous.comp (dynamics_continuous B)).continuousAt ε hε
    exact ⟨δ,hδ,fun y hy _=>by rw [dist_comm]; exact hh (by simpa only [dist_comm] using hy)⟩
  · intro t
    exact hη _

def cubeBoundary (Λ : Finset (Site d)) (ω : State d ℓ) (h : ℝ)
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ) (t : ℝ) : ℂ :=
  (Λ.card:ℂ)⁻¹*∑ x∈Λ,ω.functional (translation d ℓ x
    (M (GibbsStrip.evolve (shiftedField (Λ.image (fun y=>-x+y)) h) t B)))

lemma translated_state_difference (ω : State d ℓ) (x : Site d)
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (v w : QuasiLocal d ℓ) :
    ‖ω.functional (translation d ℓ x (M v))-ω.functional (translation d ℓ x (M w))‖≤4*‖M‖*dist v w := by
  rw [←map_sub ω.functional _ _,←map_sub (translation d ℓ x) _ _,←map_sub M _ _,dist_eq_norm]
  calc _ ≤ 4*‖translation d ℓ x (M (v-w))‖ := state_apply_norm_le ω _
       _ ≤ 4*(‖M‖*‖v-w‖) := by rw [norm_translation]; exact mul_le_mul_of_nonneg_left (M.le_opNorm _) (by norm_num)
       _ = _ := by ring

lemma cubeBoundary_error (N r : ℕ) (hr : r≤N) (ω : State d ℓ) (h t : ℝ)
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ)
    {δ : ℝ} (hδ : 0≤δ)
    (hgood : ∀ Γ : Finset (Site d),box d r⊆Γ →
      dist (GibbsStrip.evolve (shiftedField Γ h) t B) (dynamics d ℓ t B)≤δ) :
    ‖cubeBoundary (box d N) ω h M B t-
      (cubeAverage (box d N) (box_nonempty d N) ω).functional (M (dynamics d ℓ t B))‖≤
        4*‖M‖*δ+(((box d N\box d (N-r)).card:ℝ)/(box d N).card)*(8*‖M‖*‖B‖) := by
  classical
  rw [cubeBoundary,cubeAverage_apply,←mul_sub,←Finset.sum_sub_distrib]
  apply Average.norm_uniform_bulk_le _ (box d (N-r)) (box_nonempty d N) (box_mono (Nat.sub_le N r)) _ (by positivity)
  · intro x hx
    exact (translated_state_difference ω _ M _ _).trans (mul_le_mul_of_nonneg_left (hgood _ (box_deep_translate hr hx)) (by positivity))
  · intro x _
    have hb : dist (GibbsStrip.evolve (shiftedField ((box d N).image (fun y=>-x+y)) h) t B) (dynamics d ℓ t B)≤2*‖B‖ := by
      classical
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans_eq (by rw [GibbsStrip.real_evolve_norm (shiftedField_selfAdjoint _ _),dynamics_norm]; ring)
    exact (translated_state_difference ω _ M _ _).trans (by nlinarith [mul_le_mul_of_nonneg_left hb (show 0≤4*‖M‖ by positivity)])

lemma scaled_quarter {ε C : ℝ} (hε : 0<ε) (hC : 0≤C) :
    C*(ε/(4*(C+1)))<ε/4 := by
  have hp : 0<C+1:=by linarith
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
  field_simp
  nlinarith

theorem cubeBoundary_locallyUniform (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (η : ℕ → State d ℓ)
    (ω : State d ℓ) (hω : ∀ A,Tendsto (fun n=>(cubeAverage (box d (N n)) (box_nonempty d (N n)) (η n)).functional A) atTop (𝓝 (ω.functional A)))
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ) :
    TendstoLocallyUniformly (fun n t=>cubeBoundary (box d (N n)) (η n) (h n) M B t)
      (fun t=>ω.functional (M (dynamics d ℓ t B))) atTop := by
  classical
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨r,δ,hδ,hgood⟩:=field_deep_uniform B K hK (show 0<ε/(4*(4*‖M‖+1)) by positivity)
  have hsmall := (Metric.tendsto_nhds.mp hh) δ hδ
  have hratio : Tendsto (fun n=>(((box d (N n)\box d (N n-r)).card:ℝ)/(box d (N n)).card)*(8*‖M‖*‖B‖)) atTop (𝓝 0) := by
    classical
    simpa only [Function.comp_def,zero_mul] using ((box_boundary_inner_tendsto d r).comp hN).mul_const (8*‖M‖*‖B‖)
  have heval := tendstoLocallyUniformly_iff_forall_isCompact.mp (state_limit_locallyUniform hω M B) K hK
  filter_upwards [hN.eventually (eventually_ge_atTop r),hsmall,
    hratio.eventually (eventually_lt_nhds (show (0:ℝ)<ε/4 by positivity)),
    (Metric.tendstoUniformlyOn_iff.mp heval) (ε/4) (by positivity)] with n hn hhn hb he
  intro t ht
  have hhn' : |h n|<δ := by simpa only [dist_zero_right,Real.norm_eq_abs] using hhn
  have herr:=cubeBoundary_error (N n) r hn (η n) (h n) t M B (show 0≤ε/(4*(4*‖M‖+1)) by positivity)
    (fun Γ hΓ=>(hgood Γ hΓ (h n) hhn' t ht).le)
  have hpart:=scaled_quarter hε (show 0≤4*‖M‖ by positivity)
  have htri:=dist_triangle (ω.functional (M (dynamics d ℓ t B)))
    ((cubeAverage (box d (N n)) (box_nonempty d (N n)) (η n)).functional (M (dynamics d ℓ t B)))
    (cubeBoundary (box d (N n)) (η n) (h n) M B t)
  rw [←dist_eq_norm,dist_comm] at herr
  have hei:=he t ht
  linarith

end Heisenberg
end
end

end OAI
