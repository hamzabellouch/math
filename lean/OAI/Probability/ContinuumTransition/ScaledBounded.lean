import OAI.Probability.ContinuumTransition.ScaledActive

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma bounded_zero_mul {a d : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    {D : ℝ} (hd : ∀ n, |d n| ≤ D) : Tendsto (fun n => a n*d n) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hh : Tendsto (fun n => |a n| * D) atTop (𝓝 0) := by simpa using (ha.abs.mul_const D)
  apply squeeze_zero (fun n => abs_nonneg _) _ hh
  intro n
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hd n) (abs_nonneg _)

lemma scaled_active_subseq {F : Parameter → ℝ} (hF : ConvexOn ℝ pressureDomain F)
    {Q P : ℕ → Parameter → ℝ} {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hQ : ∀ n, ConvexOn ℝ pressureDomain (Q n)) (hP : ∀ n, IsMeanField (Q n) (a n) (P n))
    {x : Parameter} (hx : x ∈ pressureDomain) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ pressureDomain)
    (happ : ∀ n, ∀ y ∈ ball x r, |Q n y-F y| ≤ (a n)^2)
    {Ξ W : ℕ → Parameter} {S D : ℝ} (hΞ : ∀ n, ‖Ξ n‖ ≤ S)
    (hXS : ∀ n, x+a n • Ξ n ∈ pressureDomain)
    (hA : ∀ n, W n ∈ activeLifts (Q n) (a n) (P n) (x+a n • Ξ n))
    (hD : ∀ n, |(W n).2| ≤ D) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ξ v : Parameter,
      Tendsto (Ξ ∘ φ) atTop (𝓝 ξ) ∧ Tendsto (W ∘ φ) atTop (𝓝 v) ∧
      SupportOn pressureDomain F x v ∧
      ∀ u, SupportOn pressureDomain F x u → quadraticObjective ξ u x.1 ≤ quadraticObjective ξ v x.1 := by
  obtain ⟨ξ,_,φ,hφ,hξ⟩ := (isCompact_closedBall (0 : Parameter) S).tendsto_subseq
    (fun n => by simpa only [mem_closedBall,dist_zero_right] using hΞ n)
  let b := a ∘ φ
  let X : ℕ → Parameter := fun n => x+b n • Ξ (φ n)
  let Y : ℕ → Parameter := fun n => shiftedField (b n) (X n) (W (φ n)).2
  let V : ℕ → Parameter := fun n => unlift (b n) (W (φ n))
  have hb : Tendsto b atTop (𝓝 0) := ha0.comp hφ.tendsto_atTop
  have hX : Tendsto X atTop (𝓝 x) := by
    simpa only [Function.comp_def,X,zero_smul,add_zero] using tendsto_const_nhds.add (hb.smul hξ)
  have hY : Tendsto Y atTop (𝓝 x) := by
    have hh := ((continuous_fst.tendsto x).comp hX).prodMk_nhds
      (((continuous_snd.tendsto x).comp hX).add
        (((continuous_fst.tendsto x).comp hX).mul (bounded_zero_mul hb (fun n => hD (φ n)))))
    simpa only [Function.comp_def,Y,shiftedField,mul_zero,add_zero,Prod.mk.eta,mul_assoc] using hh
  have hpoint : ∀ y ∈ ball x r, Tendsto (fun n => Q (φ n) y) atTop (𝓝 (F y)) := by
    intro y hy
    exact uniform_square_error_tendsto hb (fun n => happ (φ n)) hy tendsto_const_nhds
      ((hF.continuousOn isOpen_pressureDomain).continuousAt (isOpen_pressureDomain.mem_nhds (hball hy)))
  obtain ⟨C,hC⟩ := eventually_subgradients_bounded isOpen_ball
    (Eventually.of_forall fun n => (hQ (φ n)).subset hball (convex_ball x r)) hpoint
    (mem_ball_self hr) hY
  have hVC : ∀ᶠ n in atTop, V n ∈ closedBall 0 C := by
    filter_upwards [hC] with n hn
    simpa only [mem_closedBall,dist_zero_right] using hn (V n) (fun y hy => (hA (φ n)).2 y (hball hy))
  obtain ⟨v,_,ψ,hψ,hv⟩ := (isCompact_closedBall (0 : Parameter) C).tendsto_subseq' hVC.frequently
  have hw : Tendsto (W ∘ (φ ∘ ψ)) atTop (𝓝 v) := by
    have hd2 : ∀ n, |(W (φ (ψ n))).2^2| ≤ D^2 := by
      intro n
      simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hD (φ (ψ n))) 2
    have he := (bounded_zero_mul (hb.comp hψ.tendsto_atTop) hd2).div_const 2
    have hh := (((continuous_fst.tendsto v).comp hv).add he).prodMk_nhds
      ((continuous_snd.tendsto v).comp hv)
    simpa only [Function.comp_def,V,unlift,b,zero_div,add_zero,sub_add_cancel,Prod.mk.eta] using hh
  have hxi := hξ.comp hψ.tendsto_atTop
  have hb0 := ha0.comp (hφ.comp hψ).tendsto_atTop
  have hh := scaled_active_limit hF (fun n => ha (φ (ψ n))) hb0
    (fun n => hP (φ (ψ n))) hx hr hball (fun n => happ (φ (ψ n))) hxi hw
    (fun n => hXS (φ (ψ n))) (fun n => hA (φ (ψ n)))
  exact ⟨φ ∘ ψ,hφ.comp hψ,ξ,v,hxi,hw,hh⟩

end ContinuumTemperature
end
end

end OAI
