import OAI.Probability.ContinuumTransition.SubgradientBounds

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma pDot_continuous_left (ξ : Parameter) : Continuous (fun v : Parameter => pDot v ξ) := by
  unfold pDot
  fun_prop

lemma pDot_monotone_supports {S : Set Parameter} {F : Parameter → ℝ}
    {x y v w : Parameter} (hx : x ∈ S) (hy : y ∈ S)
    (hv : SupportOn S F x v) (hw : SupportOn S F y w) :
    pDot v (y-x) ≤ pDot w (y-x) := by
  have h1 := hv y hy
  have h2 := hw x hx
  dsimp [pDot] at *
  linarith

theorem support_generators_closedHull {S : Set Parameter} (hS : IsOpen S)
    {F : Parameter → ℝ} (hF : ConvexOn ℝ S F) (A : Parameter → Set Parameter)
    (hAsub : ∀ x ∈ S, A x ⊆ subgradients S F x)
    (hAne : ∀ x ∈ S, (A x).Nonempty)
    (hAcl : ∀ {X V : ℕ → Parameter} {x v : Parameter}, x ∈ S →
      Tendsto X atTop (𝓝 x) → Tendsto V atTop (𝓝 v) →
      (∀ n, X n ∈ S) → (∀ n, V n ∈ A (X n)) → v ∈ A x)
    {x : Parameter} (hx : x ∈ S) :
    subgradients S F x = closedConvexHull ℝ (A x) := by
  classical
  apply subset_antisymm
  · intro w hw
    by_contra hn
    obtain ⟨L,c,hL,hc⟩ := geometric_hahn_banach_closed_point
      (convex_closedConvexHull (𝕜 := ℝ)) isClosed_closedConvexHull hn
    let ξ : Parameter := (L (1,0),L (0,1))
    let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
    have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
    have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    let X : ℕ → Parameter := fun n => x+ε n • ξ
    have hX : Tendsto X atTop (𝓝 x) := by
      simpa only [zero_smul,add_zero] using tendsto_const_nhds.add (hεlim.smul_const ξ)
    have hXS : ∀ᶠ n in atTop, X n ∈ S := hX.eventually (hS.mem_nhds hx)
    let Y : ℕ → Parameter := fun n => if X n ∈ S then X n else x
    have hYS : ∀ n, Y n ∈ S := by intro n; dsimp [Y]; split_ifs with h; exact h; exact hx
    have hYX : Y =ᶠ[atTop] X := hXS.mono fun n hn => ite_eq_left hn
    have hY : Tendsto Y atTop (𝓝 x) := hX.congr' hYX.symm
    choose V hV using fun n => hAne (Y n) (hYS n)
    obtain ⟨C,hC⟩ := eventually_subgradients_bounded (l := atTop) hS
      (F := fun _ : ℕ => F) (Eventually.of_forall fun _ => hF)
      (fun _ _ => tendsto_const_nhds) hx hY
    have hb : ∀ᶠ n in atTop, V n ∈ closedBall (0 : Parameter) C := by
      filter_upwards [hC] with n hn
      simpa only [mem_closedBall,dist_zero_right] using hn (V n) (hAsub _ (hYS n) (hV n))
    obtain ⟨v,_,φ,hφ,hvlim⟩ := (isCompact_closedBall (0 : Parameter) C).tendsto_subseq' hb.frequently
    have hvA := hAcl hx (hY.comp hφ.tendsto_atTop) hvlim
      (fun n => hYS (φ n)) (fun n => hV (φ n))
    have hd : pDot w ξ ≤ pDot v ξ := by
      apply ge_of_tendsto ((pDot_continuous_left ξ).tendsto v |>.comp hvlim)
      filter_upwards [hφ.tendsto_atTop.eventually hYX] with n hn
      have hm := pDot_monotone_supports hx (hYS (φ n)) hw (hAsub _ (hYS (φ n)) (hV (φ n)))
      rw [hn] at hm
      have he (z : Parameter) : pDot z (X (φ n)-x) = ε (φ n)*pDot z ξ := by dsimp [pDot,X]; ring
      rw [he,he] at hm
      change pDot w ξ ≤ pDot (V (φ n)) ξ
      exact (mul_le_mul_iff_right₀ (hε (φ n))).mp (by simpa only [mul_comm] using hm)
    have hLv := hL v (subset_closedConvexHull hvA)
    have he (z : Parameter) : L z = pDot z ξ := by exact linear_parameter_eq L z
    rw [he] at hLv hc
    linarith
  · exact closedConvexHull_min (hAsub x hx) (subgradients_convex S F x) (subgradients_closed S F x)

end ContinuumTemperature
end
end

end OAI
