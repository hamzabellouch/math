import Mathlib
import OAI.Geometry.WeakHessian.Entropy.DensityHamiltonJacobi
import OAI.Geometry.WeakHessian.Calculus.CompactHopfCurve

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integrated_hamiltonJacobi_action
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
      FormActionBound m (fun x => u s x+ε) v (a s-2*τ*e)) :
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
      exact ((hA s hs).hamiltonJacobi_slope (hd s hs)
        (by linarith [hs.1]) (hWS s hs) (hΓ s hs)
        (fun z hz => hun z (by linarith [hs.1]))
        (fun z hz => hHJ s z hs.1 hz) r hineq).frequently) ⟨zero_le_one,le_rfl⟩
  dsimp only [B,J] at H
  linarith

omit [SigmaFinite m] in
lemma compact_dual_of_entropy_action
    (hfin : FiniteOnBoundedSets m) (o : X)
    {u : ℝ → Lp ℝ 2 m} {E P a : ℝ → ℝ} {τ ε : ℝ}
    (hε : 0 ≤ ε) (hu : ContinuousOn u (Icc 0 1))
    (hE : ContinuousOn E (Icc 0 1)) (hP : ContinuousOn P (Icc 0 1))
    (hP' : ∀ s ∈ Ico (0:ℝ) 1, HasDerivAt P (a s/2) s)
    (hun : ∀ z, 0 ≤ z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (hA : ∀ s ∈ Ico (0:ℝ) 1, ∃ v : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt u v s ∧ HasDerivAt E e s ∧
      FormActionBound m (fun x => u s x+ε) v (a s-2*τ*e))
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {q : ℝ} (hq : 0 < q) :
    ∃ D : ℝ,
      (∫ x, u 1 x*boundedHopfMap f (q+1) x ∂m)-
        (∫ x, u 0 x*boundedHopfMap f q x ∂m)+τ*(E 1-E 0) ≤ P 1-P 0+ε*D/2 := by
  obtain ⟨W,D,hWe,hWc,hWS,hΓ,hD,hHJ⟩ := compactHopf_exists_L2_curve hfin f o hf hq
    (by linarith : q ≤ q+1)
  refine ⟨D,?_⟩
  have hmap : MapsTo (fun s : ℝ => q+s) (Icc 0 1) (Icc q (q+1)) := by
    intro s hs; constructor <;> linarith [hs.1,hs.2]
  have H := integrated_hamiltonJacobi_action (W := fun s => W (q+s)) hq hε
    (hWc.comp (by fun_prop) hmap) hu hE hP hP'
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
    simp only [hx,RCLike.inner_apply,RCLike.conj_to_real]
  rw [hpair 1 zero_le_one,hpair 0 le_rfl] at H
  simpa only [add_zero] using H

end WeakHessian

end
end

end OAI
