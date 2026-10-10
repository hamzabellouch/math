import OAI.Probability.InvariantIsing.Cavity.CavityHaarBoundedLimit
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianContinuity

namespace OAI

/-! The inverse square-root compression is bounded with probability
tending to one. No global inverse moment is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_inverse_sqrt_tendsto_pos {q : ℕ}
    (G : ℕ → Matrix (Fin q) (Fin q) ℝ) (hG : ∀ k, (G k).PosSemidef)
    {ρ : ℝ} (hρ : 0 < ρ) (hlim : Tendsto G atTop (𝓝 (ρ • 1))) :
    Tendsto (fun k => (CFC.sqrt (G k))⁻¹) atTop
      (𝓝 ((CFC.sqrt (ρ • (1 : Matrix (Fin q) (Fin q) ℝ)))⁻¹)) := by
  have hp : (ρ • (1 : Matrix (Fin q) (Fin q) ℝ)).PosDef := Matrix.PosDef.one.smul hρ
  have hu := cavity_sqrt_det_isUnit _ hp
  have hc : ContinuousAt (Inv.inv : Matrix (Fin q) (Fin q) ℝ → _)
      (CFC.sqrt (ρ • (1 : Matrix (Fin q) (Fin q) ℝ))) := by
    apply continuousAt_matrix_inv
    have he : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext (fun x => Ring.inverse_eq_inv x)
    rw [he]
    exact continuousAt_inv₀ hu.ne_zero
  exact hc.tendsto.comp (cavity_sqrt_tendsto G _ hG hp.posSemidef hlim)

theorem cavityHaarWindow_correction_probability {q : ℕ}
    (N l u : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hu : Tendsto u atTop atTop) (hl : (∀ k, l k = 0) ∨ Tendsto l atTop atTop)
    (hlu : ∀ k, l k ≤ u k) (hle : ∀ k, l k ≤ N k) (hue : ∀ k, u k ≤ N k)
    (ρl ρu : ℝ) (hρ : 0 < ρu - ρl)
    (hρl : Tendsto (fun k => (l k : ℝ) / N k) atTop (𝓝 ρl))
    (hρu : Tendsto (fun k => (u k : ℝ) / N k) atTop (𝓝 ρu))
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin q) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1)
    {L : ℝ} (hL : ‖(CFC.sqrt ((ρu - ρl) • (1 : Matrix (Fin q) (Fin q) ℝ)))⁻¹‖ < L) :
    Tendsto (fun k => (μ k).real {U | ‖(CFC.sqrt (cavityWindowGram
      ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l k) (u k)))⁻¹‖ ≤ L})
      atTop (𝓝 1) := by
  let F := fun G : Matrix (Fin q) (Fin q) ℝ => if ‖(CFC.sqrt G)⁻¹‖ ≤ L then (1 : ℝ) else 0
  have hmnorm : Measurable (fun G : Matrix (Fin q) (Fin q) ℝ => ‖(CFC.sqrt G)⁻¹‖) :=
    (cavity_matrix_inverse_measurable.comp CFC.measurable_sqrt).norm
  have hmF : Measurable F :=
    Measurable.ite (measurableSet_le hmnorm measurable_const) measurable_const measurable_const
  have hb : ∀ G, |F G| ≤ 1 := by intro G; dsimp only [F]; split_ifs <;> norm_num
  have hlim := cavityWindowGram_tendsto_ae q N l u hN hu hl hle hue ρl ρu hρl hρu
  have hFae : ∀ᵐ x ∂cavityGaussianRows q, Tendsto (fun k => F (cavityWindowGram
      (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k) (u k))) atTop (𝓝 1) := by
    filter_upwards [hlim] with x hx
    have hc := cavity_inverse_sqrt_tendsto_pos _
      (fun k => cavityWindowGram_posSemidef _ _ _ (hlu k)) hρ hx
    have he := hc.norm.eventually (Iio_mem_nhds hL)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with k hk
    simp only [F, hk.le, ite_true]
  have ht := cavityHaarWindowGram_bounded_limit N l u hN μ A₀ hA₀
    (fun _ => F) (fun _ => hmF) (fun _ => hb) hFae
  have he (k : ℕ) : (∫ U, F (cavityWindowGram
      ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l k) (u k)) ∂μ k) =
      (μ k).real {U | ‖(CFC.sqrt (cavityWindowGram
        ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l k) (u k)))⁻¹‖ ≤ L} := by
    have hm : Measurable (fun U : Orthogonal (N k) => ‖(CFC.sqrt (cavityWindowGram
        ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l k) (u k)))⁻¹‖) :=
      hmnorm.comp (((continuous_cavityWindowGram (N k) q (l k) (u k)).comp
        (continuous_subtype_val.matrix_mul continuous_const)).measurable)
    simpa only [F, Set.indicator, mem_ofPred_eq, Pi.one_apply] using
      (integral_indicator_one (μ := μ k) (measurableSet_le hm measurable_const))
  simpa only [he] using ht

end InvariantIsing

end

end OAI
