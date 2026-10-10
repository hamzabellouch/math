import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Minimizers.CriticalEnergy
import OAI.Geometry.CAT0Fillings.Sobolev.Completion

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry

lemma ground_state_pointwise {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D ξ : E) (w d : ℝ) :
    ‖w • D+d • ξ‖^2 = inner ℝ D (w^2 • D+(2*w*d) • ξ)+d^2*‖ξ‖^2 := by
  rw [norm_add_sq_real,inner_add_right,real_inner_smul_right,real_inner_smul_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
    norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,mul_pow,mul_pow,sq_abs,sq_abs]
  ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ground_state (v P Q : q.Sobolev) {w d : X → ℝ} {ξ : ℕ × Euc (k+1) → Euc (k+1)}
    {β : ℝ} (hb : 0 < β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hP : (q.inclusion P : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => q.inclusion v x*w x))
    (hQ : (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => q.inclusion v x*(w x)^2))
    (hDP : (q.closedGradient P : _ → _) =ᵐ[q.atlasMeasure]
      (fun z => w (q.atlasParam z) • q.closedGradient v z+d (q.atlasParam z) • ξ z))
    (hDQ : (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
      (fun z => (w (q.atlasParam z))^2 • q.closedGradient v z+
        (2*w (q.atlasParam z)*d (q.atlasParam z)) • ξ z))
    (heuler : 4*β*inner ℝ (q.closedGradient v) (q.closedGradient Q) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion Q) =
      (k+1:ℝ)*(∫ x, (q.inclusion v x)^(1+4*β)*(q.inclusion Q x) ∂MassMeasure.currentMassMeasure hT)) :
    Integrable (fun z => (d (q.atlasParam z))^2*‖ξ z‖^2) q.atlasMeasure ∧
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P =
        (k+1:ℝ)*(∫ x, (q.inclusion v x)^(2+4*β)*(w x)^2 ∂MassMeasure.currentMassMeasure hT)+
          4*β*(∫ z, (d (q.atlasParam z))^2*‖ξ z‖^2 ∂q.atlasMeasure) := by
  have hg : (fun z => ‖q.closedGradient P z‖^2-inner ℝ (q.closedGradient v z) (q.closedGradient Q z))
      =ᵐ[q.atlasMeasure] (fun z => (d (q.atlasParam z))^2*‖ξ z‖^2) := by
    filter_upwards [hDP,hDQ] with z hp hq
    rw [hp,hq,ground_state_pointwise]
    ring
  have hi : Integrable (fun z => ‖q.closedGradient P z‖^2) q.atlasMeasure := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) (q.closedGradient P) (q.closedGradient P)
  have hj := L2.integrable_inner (𝕜 := ℝ) (q.closedGradient v) (q.closedGradient Q)
  have hf := (hi.sub hj).congr hg
  refine ⟨hf,?_⟩
  have hG : ‖q.closedGradient P‖^2 = inner ℝ (q.closedGradient v) (q.closedGradient Q)+
      (∫ z, (d (q.atlasParam z))^2*‖ξ z‖^2 ∂q.atlasMeasure) := by
    have h := integral_congr_ae hg
    rw [integral_sub hi hj] at h
    have hn := L2.inner_def (𝕜 := ℝ) (q.closedGradient P) (q.closedGradient P)
    simp only [real_inner_self_eq_norm_sq] at hn
    rw [←hn,←L2.inner_def] at h
    linarith
  have hI : ‖q.inclusion P‖^2 = inner ℝ (q.inclusion v) (q.inclusion Q) := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hP,hQ] with x hp hq
    simp only [RCLike.inner_apply,conj_trivial,hp,hq]
    ring
  have hR : (∫ x, (q.inclusion v x)^(1+4*β)*(q.inclusion Q x) ∂MassMeasure.currentMassMeasure hT) =
      ∫ x, (q.inclusion v x)^(2+4*β)*(w x)^2 ∂MassMeasure.currentMassMeasure hT := by
    apply integral_congr_ae
    filter_upwards [hv,hQ] with x hv hq
    rw [hq,←mul_assoc]
    conv_lhs => lhs; rhs; rw [←Real.rpow_one (q.inclusion v x)]
    rw [←Real.rpow_add' hv (by linarith : 1+4*β+1 ≠ 0)]
    congr 2
    ring
  rw [hR] at heuler
  unfold AnalyticMinimizer.energy
  rw [hG,hI]
  nlinarith [heuler]
end CAT0Fillings.ChartGeometry
end

end OAI
