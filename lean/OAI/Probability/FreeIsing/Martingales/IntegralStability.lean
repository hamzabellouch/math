import OAI.Probability.FreeIsing.Brownian.ContinuousAssociativity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.MartingaleIntegralStability

open BrownianGrid BrownianContinuousAssociativity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
  {M N K : ℝ≥0 → Ω → ℝ}

theorem uniformSum_difference_sq_le_terminal
    (hM : Martingale M F P) (hN : Martingale N F P)
    (hM2 : ∀ t, MemLp (M t) 2 P) (hN2 : ∀ t, MemLp (N t) 2 P)
    (hK : StronglyAdapted F K) {D : ℝ} (hD : 0 ≤ D)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, (uniformSum M K T n ω - uniformSum N K T n ω) ^ 2 ∂P) ≤
      D ^ 2 * ∫ ω, (M T ω - N T ω) ^ 2 ∂P := by
  by_cases hn : n = 0
  · subst n
    simp only [uniformSum, integralSum, Finset.range_zero, Finset.sum_empty,
      sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero]
    positivity
  have h := MartingaleTransformL2.integral_sq_grid_transform_le_terminal
    (hM.sub hN) (fun t => (hM2 t).sub (hN2 t))
    (uniformGrid T n) (uniformGrid_mono T n) (fun j => K (uniformGrid T n j))
    (fun j => hK _) hD (fun j => hbK.mono (fun ω hω => hω _)) n
  rw [uniformGrid_end T (Nat.pos_of_ne_zero hn)] at h
  simp only [Pi.sub_apply] at h
  convert h using 1
  congr 1
  funext ω
  simp only [uniformSum, integralSum]
  rw [← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem uniformSum_limit_of_integrator_limits
    {α : Type*} {l : Filter α} [l.NeBot]
    {A : α → ℝ≥0 → Ω → ℝ} {Zs : α → Ω → ℝ} {Z : Ω → ℝ}
    (hM : Martingale M F P) (hA : ∀ k, Martingale (A k) F P)
    (hM2 : ∀ t, MemLp (M t) 2 P) (hA2 : ∀ k t, MemLp (A k t) 2 P)
    (hK : StronglyAdapted F K) {D : ℝ} (hD : 0 ≤ D)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (hZs : ∀ k, MemLp (Zs k) 2 P) (hZ : MemLp Z 2 P) (T : ℝ≥0)
    (hterminal : Tendsto (fun k => ∫ ω, (A k T ω - M T ω) ^ 2 ∂P) l (𝓝 0))
    (hendpoints : Tendsto (fun k => ∫ ω, (Zs k ω - Z ω) ^ 2 ∂P) l (𝓝 0))
    (hinner : ∀ k, Tendsto (fun n => ∫ ω,
      (uniformSum (A k) K T n ω - Zs k ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (uniformSum M K T n ω - Z ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (16 * (D ^ 2 + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨k, hkM, hkZ⟩ := ((hterminal.eventually (gt_mem_nhds hη)).and
    (hendpoints.eventually (gt_mem_nhds hη))).exists
  obtain ⟨L, hL⟩ := ((hinner k).eventually (gt_mem_nhds hη)).exists_forall_of_atTop
  refine ⟨L, ?_⟩
  intro n hn
  have hnerr := hL n hn
  have houterM := uniformSum_memLp hM2 hK hbK T n
  have houterA := uniformSum_memLp (hA2 k) hK hbK T n
  have htriangle := integral_sq_sub_le_two houterM hZ houterA
  have htriangle' := integral_sq_sub_le_two hZ houterA (hZs k)
  have hcontract := uniformSum_difference_sq_le_terminal hM (hA k) hM2 (hA2 k)
    hK hD hbK T n
  have hsymM : (∫ ω, (M T ω - A k T ω) ^ 2 ∂P) =
      ∫ ω, (A k T ω - M T ω) ^ 2 ∂P := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => sub_sq_comm _ _)
  have hsymZ : (∫ ω, (Z ω - Zs k ω) ^ 2 ∂P) =
      ∫ ω, (Zs k ω - Z ω) ^ 2 ∂P := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => sub_sq_comm _ _)
  rw [hsymM] at hcontract
  rw [hsymZ] at htriangle'
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => sq_nonneg _))]
  have hbound : (∫ ω, (uniformSum M K T n ω - Z ω) ^ 2 ∂P) <
      (2 * D ^ 2 + 8) * η := by
    have hmBound := mul_le_mul_of_nonneg_left hkM.le (sq_nonneg D)
    nlinarith
  apply hbound.trans
  dsimp only [η]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity : 0 < 16 * (D ^ 2 + 1))).mpr
  nlinarith [sq_nonneg D]

end Problem367.MartingaleIntegralStability

end

end OAI
