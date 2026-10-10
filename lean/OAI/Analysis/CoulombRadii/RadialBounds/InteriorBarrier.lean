import Mathlib
import OAI.Analysis.CoulombRadii.Variational.WeakLaplacian

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom

lemma second_deriv_general_quadratic_rpow {q b c p : ℝ} (hq : 0<q) :
    deriv (deriv (fun t : ℝ => (q+2*t*b+c*t^2)^p)) 0 =
      p*(p-1)*q^(p-2)*(2*b)^2+2*c*p*q^(p-1) := by
  let Q : ℝ → ℝ := fun t => q+2*t*b+c*t^2
  have hQ (t : ℝ) : HasDerivAt Q (2*b+2*c*t) t := by
    convert (((hasDerivAt_const t q).add
      (((hasDerivAt_id t).const_mul 2).mul_const b)).add
      (((hasDerivAt_id t).pow 2).const_mul c)) using 1
    all_goals first | rfl | dsimp [Q]; ring
  have hQ0 : Q 0=q := by simp [Q]
  have hQe : ∀ᶠ t in 𝓝 (0:ℝ), Q t≠0 :=
    (hQ 0).continuousAt.eventually_ne (by simpa [hQ0] using ne_of_gt hq)
  have hd : deriv (fun t => Q t^p) =ᶠ[𝓝 0] fun t => p*Q t^(p-1)*(2*b+2*c*t) := by
    filter_upwards [hQe] with t ht
    convert ((hQ t).rpow_const (Or.inl ht)).deriv using 1
    ring
  rw [hd.deriv_eq]
  have hh := (((hQ 0).rpow_const (p := p-1)
    (Or.inl (by simpa [hQ0] using ne_of_gt hq))).const_mul p).mul
    ((hasDerivAt_const 0 (2*b)).add ((hasDerivAt_id 0).const_mul (2*c)))
  have hh' : HasDerivAt (fun t => p*Q t^(p-1)*(2*b+2*c*t))
      (p*((2*b)*(p-1)*q^(p-1-1))*(2*b)+p*q^(p-1)*(2*c)) 0 := by
    convert hh using 1
    all_goals first | rfl | norm_num [Q]
  rw [hh'.deriv,show p-1-1=p-2 by ring]
  ring

def interiorBump (y : Position) (s A : ℝ) (x : Position) : ℝ :=
  A*(s^2-‖x-y‖^2)^(-4:ℝ)

lemma interiorBump_eq_div {y x : Position} {s A : ℝ}
    (h : 0<s^2-‖x-y‖^2) : interiorBump y s A x=A/(s^2-‖x-y‖^2)^4 := by
  rw [interiorBump, Real.rpow_neg h.le]
  norm_num [div_eq_mul_inv]

lemma coordinateLaplacian_interiorBump {y x : Position} {s A : ℝ}
    (h : 0<s^2-‖x-y‖^2) : coordinateLaplacian (interiorBump y s A) x =
      A*(80*‖x-y‖^2*(s^2-‖x-y‖^2)^(-6:ℝ)+24*(s^2-‖x-y‖^2)^(-5:ℝ)) := by
  unfold interiorBump
  rw [coordinateLaplacian_const_mul]
  unfold coordinateLaplacian
  have he (a : Fin 3) : (fun t : ℝ => (s^2-‖x+t • axis a-y‖^2)^(-4:ℝ))=
      (fun t : ℝ => ((s^2-‖x-y‖^2)+2*t*(-(x-y) a)+(-1)*t^2)^(-4:ℝ)) := by
    funext t
    rw [show x+t • axis a-y=(x-y)+t • axis a by module,norm_sq_axis_shift]
    congr 1
    ring
  simp_rw [he,second_deriv_general_quadratic_rpow h]
  congr 1
  norm_num
  have H : (∑ a : Fin 3, (y a-x a)^2)=‖x-y‖^2 := by
    have H := EuclideanSpace.real_norm_sq_eq (y-x)
    simpa only [PiLp.sub_apply,norm_sub_rev] using H.symm
  simp only [Finset.sum_add_distrib]
  rw [show (∑ a : Fin 3, 20*((s^2-‖x-y‖^2)^6)⁻¹*(2*(y a-x a))^2)=
      80*((s^2-‖x-y‖^2)^6)⁻¹*(∑ a : Fin 3, (y a-x a)^2) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha; ring]
  rw [H]
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul]
  ring

lemma contDiffOn_interiorBump {y : Position} {s : ℝ} (hs : 0<s) (A : ℝ) :
    ContDiffOn ℝ 2 (interiorBump y s A) (Metric.ball y s) := by
  apply contDiffOn_const.mul
  apply ((contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).contDiffOn).rpow_const_of_ne
  intro x hx
  have hx' : ‖x-y‖<s := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  exact ne_of_gt (sub_pos.mpr (sq_lt_sq₀ (norm_nonneg _) hs.le |>.mpr hx'))

lemma coordinateLaplacian_interiorBump_le {y x : Position} {s A : ℝ}
    (hs : 0<s) (hA : 0 ≤ A) (hx : x∈Metric.ball y s) :
    coordinateLaplacian (interiorBump y s A) x ≤ 80*A*s^2/(s^2-‖x-y‖^2)^6 := by
  have hx' : ‖x-y‖<s := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have h : 0<s^2-‖x-y‖^2 := sub_pos.mpr ((sq_lt_sq₀ (norm_nonneg _) hs.le).mpr hx')
  rw [coordinateLaplacian_interiorBump h]
  norm_num [Real.rpow_neg_natCast]
  have hid : ((s^2-‖x-y‖^2)^5)⁻¹=(s^2-‖x-y‖^2)*((s^2-‖x-y‖^2)^6)⁻¹ := by
    field_simp
  rw [hid,div_eq_mul_inv]
  calc
    _=(A*(80*‖x-y‖^2+24*(s^2-‖x-y‖^2)))*((s^2-‖x-y‖^2)^6)⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (show A*(80*‖x-y‖^2+24*(s^2-‖x-y‖^2)) ≤ 80*A*s^2 by
      nlinarith [mul_nonneg hA h.le]) (inv_nonneg.mpr (pow_nonneg h.le 6))

lemma weighted_reaction_bound {A c s : ℝ} (hA : 0<A) (hc : 0<c)
    (h : c*A^(3/2:ℝ) ≤ 80*A*s^2) : A ≤ (80/c)^2*s^4 := by
  have hp : A^(3/2:ℝ)=A*Real.sqrt A := by
    calc
      _=A^((1:ℝ)+(1/2:ℝ)) := by norm_num
      _=_ := by rw [Real.rpow_add hA,Real.rpow_one,←Real.sqrt_eq_rpow]
  rw [hp] at h
  have hsq : Real.sqrt A ≤ 80*s^2/c := by
    apply (le_div_iff₀ hc).mpr
    apply (mul_le_mul_iff_right₀ hA).mp
    nlinarith [h]
  have H := pow_le_pow_left₀ (Real.sqrt_nonneg A) hsq 2
  rw [Real.sq_sqrt hA.le] at H
  calc
    A ≤ (80*s^2/c)^2 := H
    _=(80/c)^2*s^4 := by ring

theorem weak_power_interior_upper {F : Position → ℝ} {y : Position} {s c : ℝ}
    (hs : 0<s) (hc : 0<c) (hF : ContinuousOn F (Metric.closedBall y s))
    (hw : HasWeakLaplacian F (Metric.ball y s) (fun x => c*(max (F x) 0)^(3/2:ℝ)))
    {z : Position} (hz : z∈Metric.ball y s) :
    F z ≤ (80/c)^2*s^4/(s^2-‖z-y‖^2)^4 := by
  let g : Position → ℝ := fun x => (s^2-‖x-y‖^2)^4*F x
  have hg : ContinuousOn g (Metric.closedBall y s) :=
    (((continuous_const.sub ((continuous_id.sub continuous_const).norm.pow 2)).pow 4).continuousOn).mul hF
  obtain ⟨x,hx,hm⟩ := (isCompact_closedBall y s).exists_isMaxOn
    ⟨y,Metric.mem_closedBall_self hs.le⟩ hg
  have hzsq : 0<s^2-‖z-y‖^2 := by
    apply sub_pos.mpr
    exact (sq_lt_sq₀ (norm_nonneg _) hs.le).mpr (by simpa only [Metric.mem_ball,dist_eq_norm] using hz)
  have hfinal : g z ≤ (80/c)^2*s^4 → F z ≤ (80/c)^2*s^4/(s^2-‖z-y‖^2)^4 := by
    intro H
    apply (le_div_iff₀ (pow_pos hzsq 4)).mpr
    simpa only [g,mul_comm] using H
  apply hfinal
  by_cases hpos : 0<g x
  · have hxi : x∈Metric.ball y s := by
      by_contra hn
      have hd : ‖x-y‖=s := le_antisymm
        (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
        (le_of_not_gt (by simpa only [Metric.mem_ball,dist_eq_norm] using hn))
      simp [g,hd] at hpos
    have hxq : 0<s^2-‖x-y‖^2 := sub_pos.mpr ((sq_lt_sq₀ (norm_nonneg _) hs.le).mpr
      (by simpa only [Metric.mem_ball,dist_eq_norm] using hxi))
    have hFx : 0<F x := (mul_pos_iff_of_pos_left (pow_pos hxq 4)).mp hpos
    have hbar (v : Position) (hv : v∈Metric.ball y s) : F v ≤ interiorBump y s (g x) v := by
      have hvq : 0<s^2-‖v-y‖^2 := sub_pos.mpr ((sq_lt_sq₀ (norm_nonneg _) hs.le).mpr
        (by simpa only [Metric.mem_ball,dist_eq_norm] using hv))
      rw [interiorBump_eq_div hvq]
      apply (le_div_iff₀ (pow_pos hvq 4)).mpr
      simpa only [g,mul_comm] using (show g v ≤ g x from hm (Metric.ball_subset_closedBall hv))
    have he : F x=interiorBump y s (g x) x := by
      rw [interiorBump_eq_div hxq]
      dsimp [g]
      field_simp
    have hmax : IsLocalMax (fun v => F v-interiorBump y s (g x) v) x := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxi] with v hv
      rw [he,sub_self]
      exact sub_nonpos.mpr (hbar v hv)
    have hq : ContinuousOn (fun v => c*(max (F v) 0)^(3/2:ℝ)) (Metric.ball y s) := by
      exact continuousOn_const.mul (((hF.mono Metric.ball_subset_closedBall).sup continuousOn_const).rpow_const
        (fun _ _ => Or.inr (by norm_num)))
    have HL := (weakLaplacian_le_at_local_max Metric.isOpen_ball hxi
      (hF.mono Metric.ball_subset_closedBall) hq (contDiffOn_interiorBump hs (g x)) hw hmax).trans
      (coordinateLaplacian_interiorBump_le hs hpos.le hxi)
    rw [max_eq_left hFx.le] at HL
    have hid : (g x)^(3/2:ℝ)=(s^2-‖x-y‖^2)^6*(F x)^(3/2:ℝ) := by
      dsimp [g]
      rw [Real.mul_rpow (pow_nonneg hxq.le 4) hFx.le]
      congr 1
      rw [←Real.rpow_natCast _ 4,←Real.rpow_mul hxq.le]
      norm_num
    have HR : c*(g x)^(3/2:ℝ) ≤ 80*(g x)*s^2 := by
      rw [hid]
      have H := (le_div_iff₀ (pow_pos hxq 6)).mp HL
      nlinarith [H]
    exact (hm (Metric.ball_subset_closedBall hz)).trans (weighted_reaction_bound hpos hc HR)
  · exact (hm (Metric.ball_subset_closedBall hz)).trans
      ((le_of_not_gt hpos).trans (by positivity))

end NeutralAtom
end

end
end

end OAI
