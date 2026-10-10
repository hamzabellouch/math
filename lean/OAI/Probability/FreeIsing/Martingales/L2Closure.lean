import OAI.Probability.FreeIsing.Martingales.ContinuousL2Limit

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.MartingaleSquareMaximal

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Preorder ι]
  {μ : Measure Ω} [IsFiniteMeasure μ] {F : Filtration ι mΩ}

theorem condExp_ae_eq_of_L2_limits {M : ℕ → ι → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F μ)
    (h2 : ∀ n t, MemLp (M n t) 2 μ)
    {s t : ι} (hst : s ≤ t) {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hs : Tendsto (fun n => (h2 n s).toLp (M n s)) atTop (𝓝 (hX.toLp X)))
    (ht : Tendsto (fun n => (h2 n t).toLp (M n t)) atTop (𝓝 (hY.toLp Y))) :
    μ[Y | F s] =ᵐ[μ] X := by
  let C := condExpL2 ℝ ℝ (F.le s) (μ := μ)
  have hC : Continuous (fun f : Lp ℝ 2 μ => (C f : Lp ℝ 2 μ)) :=
    continuous_subtype_val.comp C.continuous
  have heq (n : ℕ) : (C ((h2 n t).toLp (M n t)) : Lp ℝ 2 μ) =
      (h2 n s).toLp (M n s) := by
    apply Lp.ext
    exact ((h2 n t).condExpL2_ae_eq_condExp (𝕜 := ℝ) (F.le s)).trans
      (((hM n).condExp_ae_eq hst).trans (h2 n s).coeFn_toLp.symm)
  have hclass : (C (hY.toLp Y) : Lp ℝ 2 μ) = hX.toLp X := by
    apply tendsto_nhds_unique ((hC.tendsto _).comp ht)
    convert hs using 1
    funext n
    exact heq n
  have hae : (C (hY.toLp Y) : Ω → ℝ) =ᵐ[μ] X := by
    change ((C (hY.toLp Y) : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] X
    rw [hclass]
    exact hX.coeFn_toLp
  exact (hY.condExpL2_ae_eq_condExp (𝕜 := ℝ) (F.le s)).symm.trans hae

theorem martingale_of_L2_limits {M : ℕ → ι → Ω → ℝ} {L : ι → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F μ) (h2 : ∀ n t, MemLp (M n t) 2 μ)
    (hL : StronglyAdapted F L) (hL2 : ∀ t, MemLp (L t) 2 μ)
    (hlim : ∀ t, Tendsto (fun n => (h2 n t).toLp (M n t)) atTop
      (𝓝 ((hL2 t).toLp (L t)))) : Martingale L F μ := by
  refine ⟨hL, fun s t hst => ?_⟩
  exact condExp_ae_eq_of_L2_limits hM h2 hst (hL2 s) (hL2 t) (hlim s) (hlim t)

theorem exists_predictable_continuous_L2_limit_condExp
    {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F μ)
    (h2 : ∀ n t, MemLp (M n t) 2 μ)
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => M n t ω)) (T : ℝ≥0)
    (hC : CauchySeq (fun n => (h2 n T).toLp (M n T))) :
    ∃ L : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F L ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => L t ω) (Iic T)) ∧
      (∀ t ≤ T, ∃ hL2 : MemLp (L t) 2 μ,
        Tendsto (fun n => (h2 n t).toLp (M n t)) atTop (𝓝 (hL2.toLp (L t)))) ∧
      ∀ s t, s ≤ t → t ≤ T → μ[L t | F s] =ᵐ[μ] L s := by
  obtain ⟨L, hpred, hc, hlim⟩ := exists_predictable_continuous_L2_limit hM h2 hc T hC
  refine ⟨L, hpred, hc, hlim, fun s t hst ht => ?_⟩
  obtain ⟨hLs, hs⟩ := hlim s (hst.trans ht)
  obtain ⟨hLt, ht'⟩ := hlim t ht
  exact condExp_ae_eq_of_L2_limits hM h2 hst hLs hLt hs ht'

end Problem367.MartingaleSquareMaximal

end

end OAI
