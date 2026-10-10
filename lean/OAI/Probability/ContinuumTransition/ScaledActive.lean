import OAI.Probability.ContinuumTransition.ApproximateSupports

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma scaled_active_limit {F : Parameter → ℝ} (hF : ConvexOn ℝ pressureDomain F)
    {Q P : ℕ → Parameter → ℝ} {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hP : ∀ n, IsMeanField (Q n) (a n) (P n))
    {x ξ v : Parameter} (hx : x ∈ pressureDomain) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ pressureDomain)
    (happ : ∀ n, ∀ y ∈ ball x r, |Q n y-F y| ≤ (a n)^2)
    {Ξ W : ℕ → Parameter} (hΞ : Tendsto Ξ atTop (𝓝 ξ)) (hW : Tendsto W atTop (𝓝 v))
    (hXS : ∀ n, x+a n • Ξ n ∈ pressureDomain)
    (hA : ∀ n, W n ∈ activeLifts (Q n) (a n) (P n) (x+a n • Ξ n)) :
    SupportOn pressureDomain F x v ∧
      ∀ u, SupportOn pressureDomain F x u → quadraticObjective ξ u x.1 ≤ quadraticObjective ξ v x.1 := by
  let X : ℕ → Parameter := fun n => x+a n • Ξ n
  let V : ℕ → Parameter := fun n => unlift (a n) (W n)
  let Y : ℕ → Parameter := fun n => shiftedField (a n) (X n) (W n).2
  have hX : Tendsto X atTop (𝓝 x) := by
    simpa only [zero_smul,add_zero] using tendsto_const_nhds.add (ha0.smul hΞ)
  have hw2 := (continuous_snd.tendsto v).comp hW
  have hV : Tendsto V atTop (𝓝 v) := by
    have hh := (((continuous_fst.tendsto v).comp hW).sub ((ha0.mul (hw2.pow 2)).div_const 2)).prodMk_nhds hw2
    simpa only [Function.comp_def,V,unlift,zero_mul,zero_div,sub_zero,Prod.mk.eta] using hh
  have hY : Tendsto Y atTop (𝓝 x) := by
    have hh := ((continuous_fst.tendsto x).comp hX).prodMk_nhds
      (((continuous_snd.tendsto x).comp hX).add
        ((((continuous_fst.tendsto x).comp hX).mul ha0).mul hw2))
    simpa only [Function.comp_def,Y,shiftedField,mul_zero,zero_mul,add_zero,Prod.mk.eta] using hh
  have hv := approximate_support_limit hF ha0 hx hr hball happ hY hV (fun n => (hA n).2)
  refine ⟨hv,?_⟩
  intro u hu
  let Z : ℕ → Parameter := fun n => shiftedField (a n) (X n) u.2
  have hZ : Tendsto Z atTop (𝓝 x) := by
    have hh := ((continuous_fst.tendsto x).comp hX).prodMk_nhds
      (((continuous_snd.tendsto x).comp hX).add
        ((((continuous_fst.tendsto x).comp hX).mul ha0).mul_const u.2))
    simpa only [Function.comp_def,Z,shiftedField,mul_zero,zero_mul,add_zero,Prod.mk.eta] using hh
  have hineq : ∀ᶠ n in atTop,
      pDot u (Ξ n)+(X n).1*u.2^2/2 ≤ pDot (V n) (Ξ n)+(X n).1*(W n).2^2/2+2*a n := by
    filter_upwards [hZ.eventually (ball_mem_nhds x hr)] with n hn
    have h1 := hu (Z n) (hball hn)
    have h2 := (hA n).2 x hx
    have h3 := (hP n (X n) (hXS n)).1 (mem_range_self u.2)
    have h4 := (hA n).1
    have h5 := (abs_le.mp (happ n (Z n) hn)).1
    have h6 := (abs_le.mp (happ n x (mem_ball_self hr))).2
    have he1 : pDot u (Z n-x) = a n*(pDot u (Ξ n)+(X n).1*u.2^2) := by dsimp [Z,shiftedField,X,pDot]; ring
    have he2 : pDot (unlift (a n) (W n)) (x-Y n) =
        -(a n*(pDot (V n) (Ξ n)+(X n).1*(W n).2^2)) := by dsimp [Y,X,shiftedField,V,unlift,pDot]; ring
    rw [he1] at h1
    change Q n (Y n)+pDot (unlift (a n) (W n)) (x-Y n) ≤ Q n x at h2
    rw [he2] at h2
    change Q n (Z n)-(X n).1*a n*u.2^2/2 ≤ P n (X n) at h3
    change Q n (Y n)-(X n).1*a n*(W n).2^2/2 = P n (X n) at h4
    have hmul : a n*(pDot u (Ξ n)+(X n).1*u.2^2/2) ≤
        a n*(pDot (V n) (Ξ n)+(X n).1*(W n).2^2/2+2*a n) := by
      nlinarith only [h1,h2,h3,h4,h5,h6]
    exact (mul_le_mul_iff_right₀ (ha n)).mp (by simpa only [mul_comm] using hmul)
  have hdotu : Tendsto (fun n => pDot u (Ξ n)) atTop (𝓝 (pDot u ξ)) :=
    (show Continuous (fun z => pDot u z) by unfold pDot; fun_prop).tendsto ξ |>.comp hΞ
  have hdotv : Tendsto (fun n => pDot (V n) (Ξ n)) atTop (𝓝 (pDot v ξ)) :=
    (show Continuous (fun p : Parameter × Parameter => pDot p.1 p.2) by unfold pDot; fun_prop).tendsto
      (v,ξ) |>.comp (hV.prodMk_nhds hΞ)
  have ht1 := (continuous_fst.tendsto x).comp hX
  have hh := le_of_tendsto_of_tendsto (hdotu.add ((ht1.mul_const (u.2^2)).div_const 2))
    ((hdotv.add ((ht1.mul (hw2.pow 2)).div_const 2)).add (ha0.const_mul 2)) hineq
  dsimp only [quadraticObjective,pDot]
  dsimp only [pDot] at hh
  nlinarith only [hh]

end ContinuumTemperature
end
end

end OAI
