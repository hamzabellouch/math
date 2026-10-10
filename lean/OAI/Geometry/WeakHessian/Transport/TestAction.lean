import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SubConst

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma hamiltonJacobi_slope_of_test_action
    {u W : ℝ → Lp ℝ 2 m} {s q A ε : ℝ} {v : Lp ℝ 2 m}
    (hu : HasDerivAt u v s) (hqs : 0 < q+s)
    (hS : Sobolev m (W s : X → ℝ))
    (hΓ : MemLp (fun x => (weakGradient m (W s) x)^2) 2 m)
    (hun : ∀ z, s < z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (hHJ : ∀ z, s < z → ∀ᵐ x ∂m,
      W z x-W s x ≤ (-(z-s)*(q+s)/(2*(q+z)))*(weakGradient m (W s) x)^2)
    (hA : 2*⟪v,W s⟫_ℝ ≤ A+∫ x,(u s x+ε)*(weakGradient m (W s) x)^2 ∂m) :
    ∀ r, (A+ε*(∫ x, (weakGradient m (W s) x)^2 ∂m))/2 < r →
      ∀ᶠ z in 𝓝[>] s, slope (fun t => ⟪W t,u t⟫_ℝ) s z < r := by
  let Γ : Lp ℝ 2 m := hΓ.toLp (fun x => (weakGradient m (W s) x)^2)
  have hΓe : Γ =ᵐ[m] fun x => (weakGradient m (W s) x)^2 := hΓ.coeFn_toLp
  have hpair (z : ℝ) : ⟪Γ,u z⟫_ℝ = ∫ x, u z x*(weakGradient m (W s) x)^2 ∂m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hΓe] with x hx
    simp only [hx,RCLike.inner_apply,RCLike.conj_to_real]
  have hρΓ : Integrable (fun x => u s x*(weakGradient m (W s) x)^2) m :=
    (L2.integrable_inner (u s) Γ).congr (by
      filter_upwards [hΓe] with x hx
      simp only [hx,RCLike.inner_apply,RCLike.conj_to_real,mul_comm])
  have hE : (∫ x, (u s x+ε)*(weakGradient m (W s) x)^2 ∂m) =
      ⟪Γ,u s⟫_ℝ+ε*(∫ x, (weakGradient m (W s) x)^2 ∂m) := by
    simp_rw [add_mul]
    rw [integral_add hρΓ (hS.2.2.integrable_sq.const_mul ε),integral_const_mul,← hpair s]
  have hAa := hA
  rw [hE,real_inner_comm (W s) v] at hAa
  have hder : HasDerivAt (fun z => ⟪W s,u z⟫_ℝ) ⟪W s,v⟫_ℝ s := by
    simpa using (hasDerivAt_const s (W s)).inner ℝ hu
  have hsl : Tendsto (slope (fun z => ⟪W s,u z⟫_ℝ) s) (𝓝[>] s) (𝓝 ⟪W s,v⟫_ℝ) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hder).2
  have hid : Tendsto (fun z : ℝ => z) (𝓝[>] s) (𝓝 s) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun z => -(q+s)/(2*(q+z))*⟪Γ,u z⟫_ℝ+
      slope (fun z => ⟪W s,u z⟫_ℝ) s z) (𝓝[>] s)
      (𝓝 (-⟪Γ,u s⟫_ℝ/2+⟪W s,v⟫_ℝ)) := by
    have hdnom : Tendsto (fun z => 2*(q+z)) (𝓝[>] s) (𝓝 (2*(q+s))) :=
      (tendsto_const_nhds.add hid).const_mul 2
    have hpl : Tendsto (fun z => ⟪Γ,u z⟫_ℝ) (𝓝[>] s) (𝓝 ⟪Γ,u s⟫_ℝ) :=
      (continuousAt_const.inner hu.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have HH := (((tendsto_const_nhds (x := -(q+s))).div hdnom
      (by positivity : 2*(q+s) ≠ 0)).mul hpl).add hsl
    convert HH using 1
    congr 1
    field_simp [hqs.ne']
  intro r hr
  have hlt : -⟪Γ,u s⟫_ℝ/2+⟪W s,v⟫_ℝ < r := by linarith
  filter_upwards [hlim.eventually_lt_const hlt,self_mem_nhdsWithin] with z hz hzs
  change s < z at hzs
  apply lt_of_le_of_lt _ hz
  rw [slope_def_field,slope_def_field]
  apply (div_le_iff₀ (sub_pos.mpr hzs)).mpr
  have hiW : Integrable (fun x => (W z x-W s x)*u z x) m :=
    (L2.integrable_inner (u z) (W z)).sub (L2.integrable_inner (u z) (W s)) |>.congr (by
      filter_upwards [] with x
      simp only [RCLike.inner_apply,RCLike.conj_to_real,Pi.sub_apply]
      ring)
  have hiΓ : Integrable (fun x => (weakGradient m (W s) x)^2*u z x) m :=
    (L2.integrable_inner Γ (u z)).congr (by
      filter_upwards [hΓe] with x hx
      simp only [hx,RCLike.inner_apply,RCLike.conj_to_real,mul_comm])
  have H := integral_mono_ae hiW (hiΓ.const_mul (-(z-s)*(q+s)/(2*(q+z)))) (by
    filter_upwards [hHJ z hzs,hun z hzs] with x hx hn
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hx hn)
  have hI : (∫ x, (W z x-W s x)*u z x ∂m) = ⟪W z-W s,u z⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (W z) (W s)] with x hx
    simp only [hx,RCLike.inner_apply,RCLike.conj_to_real,mul_comm,Pi.sub_apply]
  rw [hI,integral_const_mul] at H
  have hIΓ : (∫ x, (weakGradient m (W s) x)^2*u z x ∂m) = ⟪Γ,u z⟫_ℝ := by
    rw [hpair]; congr 1; funext x; ring
  rw [hIΓ,inner_sub_left] at H
  have he : (-(q+s)/(2*(q+z))*⟪Γ,u z⟫_ℝ+
      (⟪W s,u z⟫_ℝ-⟪W s,u s⟫_ℝ)/(z-s))*(z-s) =
      (-(z-s)*(q+s)/(2*(q+z)))*⟪Γ,u z⟫_ℝ+⟪W s,u z⟫_ℝ-⟪W s,u s⟫_ℝ := by
    field_simp [sub_ne_zero.mpr hzs.ne']; ring
  rw [he]
  linarith

lemma integrated_hamiltonJacobi_test_action
    {W u : ℝ → Lp ℝ 2 m} {E P a : ℝ → ℝ} {q τ ε D : ℝ}
    (hq : 0 < q) (hε : 0 ≤ ε)
    (hW : ContinuousOn W (Icc 0 1)) (hu : ContinuousOn u (Icc 0 1))
    (hE : ContinuousOn E (Icc 0 1)) (hP : ContinuousOn P (Icc 0 1))
    (hP' : ∀ s ∈ Ico (0:ℝ) 1, HasDerivAt P (a s/2) s)
    (hWS : ∀ s ∈ Ico (0:ℝ) 1, Sobolev m (W s : X → ℝ))
    (hΓ : ∀ s ∈ Ico (0:ℝ) 1, MemLp (fun x => (weakGradient m (W s) x)^2) 2 m)
    (hD : ∀ s ∈ Ico (0:ℝ) 1, (∫ x, (weakGradient m (W s) x)^2 ∂m) ≤ D)
    (hun : ∀ z, 0 ≤ z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (hHJ : ∀ s z, 0 ≤ s → s < z → ∀ᵐ x ∂m,
      W z x-W s x ≤ (-(z-s)*(q+s)/(2*(q+z)))*(weakGradient m (W s) x)^2)
    (hA : ∀ s ∈ Ico (0:ℝ) 1, ∃ v : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt u v s ∧ HasDerivAt E e s ∧
      2*⟪v,W s⟫_ℝ ≤ a s-2*τ*e+∫ x,(u s x+ε)*(weakGradient m (W s) x)^2 ∂m) :
    ⟪W 1,u 1⟫_ℝ-⟪W 0,u 0⟫_ℝ+τ*(E 1-E 0) ≤ P 1-P 0+ε*D/2 := by
  choose v e hd he hA using hA
  let J := fun s => ⟪W s,u s⟫_ℝ
  let B := fun s => J 0+(P s-P 0)-τ*(E s-E 0)+ε*D/2*s
  let B' := fun s => if hs : s ∈ Ico (0:ℝ) 1 then a s/2-τ*(e s hs)+ε*D/2 else 0
  have hB : ContinuousOn B (Icc 0 1) := by
    exact (((continuousOn_const.add (hP.sub continuousOn_const)).sub
      ((hE.sub continuousOn_const).const_mul τ)).add (continuousOn_const.mul continuousOn_id))
  have hB' (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : HasDerivWithinAt B (B' s) (Ici s) s := by
    dsimp only [B']
    rw [dite_eq_left hs]
    convert! (((((hP' s hs).sub_const (P 0)).const_add (J 0)).sub
      (((he s hs).sub_const (E 0)).const_mul τ)).add
      ((hasDerivAt_id s).const_mul (ε*D/2))).hasDerivWithinAt using 1
    simp
  have H := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := J) (B := B) (B' := B') (hW.inner hu)
    (by dsimp [B]; simp) hB hB' (by
      intro s hs r hr
      change B' s < r at hr
      dsimp only [B'] at hr
      rw [dite_eq_left hs] at hr
      have hineq : (a s-2*τ*(e s hs)+ε*(∫ x, (weakGradient m (W s) x)^2 ∂m))/2 < r := by
        have HH := mul_le_mul_of_nonneg_left (hD s hs) hε
        linarith
      exact (hamiltonJacobi_slope_of_test_action (hd s hs)
        (by linarith [hs.1]) (hWS s hs) (hΓ s hs)
        (fun z hz => hun z (by linarith [hs.1]))
        (fun z hz => hHJ s z hs.1 hz) (hA s hs) r hineq).frequently) ⟨zero_le_one,le_rfl⟩
  dsimp only [B,J] at H
  linarith

end WeakHessian

end
end

end OAI
