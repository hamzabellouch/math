import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.PlanHeatEntropy

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integrated_hamiltonJacobi_action_interval
    {W u : ℝ → Lp ℝ 2 m} {E P a : ℝ → ℝ} {q τ ε D l r : ℝ}
    (hql : 0 < q+l) (hlr : l ≤ r) (hε : 0 ≤ ε)
    (hW : ContinuousOn W (Icc l r)) (hu : ContinuousOn u (Icc l r))
    (hE : ContinuousOn E (Icc l r)) (hP : ContinuousOn P (Icc l r))
    (hP' : ∀ s ∈ Ico l r, HasDerivAt P (a s/2) s)
    (hWS : ∀ s ∈ Ico l r, Sobolev m (W s : X → ℝ))
    (hΓ : ∀ s ∈ Ico l r, MemLp (fun x => (weakGradient m (W s) x)^2) 2 m)
    (hD : ∀ s ∈ Ico l r, (∫ x, (weakGradient m (W s) x)^2 ∂m) ≤ D)
    (hun : ∀ z, l ≤ z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (hHJ : ∀ s z, l ≤ s → s < z → ∀ᵐ x ∂m,
      W z x-W s x ≤ (-(z-s)*(q+s)/(2*(q+z)))*(weakGradient m (W s) x)^2)
    (hA : ∀ s ∈ Ico l r, ∃ v : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt u v s ∧ HasDerivAt E e s ∧
      FormActionBound m (fun x => u s x+ε) v (a s-2*τ*e)) :
    ⟪W r,u r⟫_ℝ-⟪W l,u l⟫_ℝ+τ*(E r-E l) ≤ P r-P l+ε*D/2*(r-l) := by
  choose v e hd he hA using hA
  let J := fun s => ⟪W s,u s⟫_ℝ
  let B := fun s => J l+(P s-P l)-τ*(E s-E l)+ε*D/2*(s-l)
  let B' := fun s => if hs : s ∈ Ico l r then a s/2-τ*(e s hs)+ε*D/2 else 0
  have hB : ContinuousOn B (Icc l r) := by
    exact (((continuousOn_const.add (hP.sub continuousOn_const)).sub
      ((hE.sub continuousOn_const).const_mul τ)).add
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
  have hB' (s : ℝ) (hs : s ∈ Ico l r) : HasDerivWithinAt B (B' s) (Ici s) s := by
    dsimp only [B']; rw [dite_eq_left hs]
    convert! (((((hP' s hs).sub_const (P l)).const_add (J l)).sub
      (((he s hs).sub_const (E l)).const_mul τ)).add
      (((hasDerivAt_id s).sub_const l).const_mul (ε*D/2))).hasDerivWithinAt using 1
    simp
  have H := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := J) (B := B) (B' := B') (hW.inner hu)
    (by dsimp [B]; simp) hB hB' (by
      intro s hs z hz
      change B' s < z at hz
      dsimp only [B'] at hz; rw [dite_eq_left hs] at hz
      have hineq : (a s-2*τ*(e s hs)+ε*(∫ x, (weakGradient m (W s) x)^2 ∂m))/2 < z := by
        have HH := mul_le_mul_of_nonneg_left (hD s hs) hε
        linarith
      exact ((hA s hs).hamiltonJacobi_slope (hd s hs)
        (by linarith [hs.1]) (hWS s hs) (hΓ s hs)
        (fun z hz => hun z (by linarith [hs.1]))
        (fun z hz => hHJ s z hs.1 hz) z hineq).frequently) ⟨hlr,le_rfl⟩
  dsimp only [B,J] at H
  linarith

omit [SigmaFinite m] in
lemma compact_dual_entropy_interval
    (hfin : FiniteOnBoundedSets m) (o : X)
    {u : ℝ → Lp ℝ 2 m} {E P a : ℝ → ℝ} {τ ε l r : ℝ}
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) (hε : 0 ≤ ε)
    (hu : ContinuousOn u (Icc l r)) (hE : ContinuousOn E (Icc l r))
    (hP : ContinuousOn P (Icc l r))
    (hP' : ∀ s ∈ Ico l r, HasDerivAt P (a s/2) s)
    (hun : ∀ z, l ≤ z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (hA : ∀ s ∈ Ico l r, ∃ v : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt u v s ∧ HasDerivAt E e s ∧
      FormActionBound m (fun x => u s x+ε) v (a s-2*τ*e))
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {q : ℝ} (hq : 0 < q) :
    (∫ x, u r x*boundedHopfMap f (q+r) x ∂m)-
      (∫ x, u l x*boundedHopfMap f (q+l) x ∂m)+τ*(E r-E l) ≤
        P r-P l+ε*compactHopfDualBound hfin o f hf hq/2*(r-l) := by
  let data := compactHopf_exists_L2_curve hfin f o hf hq (by linarith : q ≤ q+1)
  let W := data.choose
  obtain ⟨hWe,hWc,hWS,hΓ,hD,hHJ⟩ := data.choose_spec.choose_spec
  have hmap : MapsTo (fun s : ℝ => q+s) (Icc l r) (Icc q (q+1)) := by
    intro s hs; constructor <;> linarith [hs.1,hs.2]
  have H := integrated_hamiltonJacobi_action_interval (W := fun s => W (q+s))
    (by linarith : 0 < q+l) hlr hε (hWc.comp (by fun_prop) hmap) hu hE hP hP'
    (fun s hs => hWS _ (by linarith [hs.1]))
    (fun s hs => hΓ _ (by linarith [hs.1]))
    (fun s hs => hD _ (hmap ⟨hs.1,hs.2.le⟩)) hun
    (fun s z hs hsz => by
      have H := hHJ (q+s) (q+z) (by linarith) (by linarith)
      simpa only [add_sub_add_left_eq_sub] using H) hA
  have hpair (s : ℝ) (hs : 0 ≤ s) : ⟪W (q+s),u s⟫_ℝ =
      ∫ x, u s x*boundedHopfMap f (q+s) x ∂m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWe (q+s) (by linarith)] with x hx
    simp only [W,hx,RCLike.inner_apply,RCLike.conj_to_real]
  rw [hpair r (hl.trans hlr),hpair l hl] at H
  simpa only [compactHopfDualBound,data] using H

end WeakHessian

end
end

end OAI
