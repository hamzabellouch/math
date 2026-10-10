import OAI.Geometry.SurfaceImmersion.Geometry.MonotoneGermExtension

namespace OAI

/-! The increasing extensions are global diffeomorphisms, allowing local
arc coordinates to be joined without changing their germs. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma affine_tails_of_deriv_one {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (hd : ∀ x ∉ K, deriv g x = 1) :
    ∃ R cPos cNeg : ℝ, (∀ x, R < x → g x = x+cPos) ∧
      ∀ x, x < -R → g x = x+cNeg := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (continuous_id : Continuous (id : ℝ → ℝ)).continuousOn
  let R := |C|+1
  have hout : ∀ x, R < |x| → x ∉ K := by
    intro x hx hin
    have hb := hC x hin
    change ‖x‖ ≤ C at hb
    rw [Real.norm_eq_abs] at hb
    have hc := le_abs_self C
    dsimp [R] at hx
    linarith
  have hplus : EqOn g (fun x => x+(g (R+1)-(R+1))) (Ioi R) := by
    apply isOpen_Ioi.eqOn_of_deriv_eq (convex_Ioi R).isPreconnected
      (hg.differentiable (by simp)).differentiableOn
      (differentiable_id.add_const _).differentiableOn
    · intro x hx
      rw [hd x (hout x (lt_of_lt_of_le hx (le_abs_self x)))]
      simp
    · change R < R+1
      linarith
    · dsimp only [id]
      ring
  have hminus : EqOn g (fun x => x+(g (-R-1)-(-R-1))) (Iio (-R)) := by
    apply isOpen_Iio.eqOn_of_deriv_eq (convex_Iio (-R)).isPreconnected
      (hg.differentiable (by simp)).differentiableOn
      (differentiable_id.add_const _).differentiableOn
    · intro x hx
      have hxr : x < -R := hx
      have habs : R < |x| := by linarith [neg_le_abs x]
      rw [hd x (hout x habs)]
      simp
    · change -R-1 < -R
      linarith
    · dsimp only [id]
      ring
  exact ⟨R,g (R+1)-(R+1),g (-R-1)-(-R-1),fun x hx => hplus hx,fun x hx => hminus hx⟩

lemma surjective_of_deriv_one_off_compact {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (hd : ∀ x ∉ K, deriv g x = 1) :
    Function.Surjective g := by
  obtain ⟨R,cPos,cNeg,hplus,hminus⟩ := affine_tails_of_deriv_one hg hK hd
  have htop : Tendsto g atTop atTop := by
    apply (tendsto_atTop_add_const_right atTop cPos tendsto_id).congr'
    filter_upwards [eventually_gt_atTop R] with x hx
    exact (hplus x hx).symm
  have hbot : Tendsto g atBot atBot := by
    apply (tendsto_atBot_add_const_right atBot cNeg tendsto_id).congr'
    filter_upwards [eventually_lt_atBot (-R)] with x hx
    exact (hminus x hx).symm
  exact hg.continuous.surjective htop hbot

theorem increasing_smooth_germ_diffeomorphism {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ℝ) (ha : 0 < deriv h a) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      StrictMono e ∧ e =ᶠ[𝓝 a] h := by
  obtain ⟨g,K,hg,hmono,he,hpos,hK,hd⟩ := increasing_smooth_germ_extension hh a ha
  have hsurj := surjective_of_deriv_one_off_compact hg hK hd
  let e := (hmono.orderIsoOfSurjective g hsurj).toHomeomorph
  have heq : (e : ℝ → ℝ) = g := rfl
  refine ⟨e,by simpa only [heq] using hg,?_,by simpa only [heq] using hmono,by simpa only [heq] using he⟩
  apply e.contDiff_symm_deriv (f' := deriv g)
  · intro x
    exact ne_of_gt (hpos x)
  · intro x
    change HasDerivAt g (deriv g x) x
    exact (hg.differentiable (by simp) x).hasDerivAt
  · simpa only [heq] using hg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
