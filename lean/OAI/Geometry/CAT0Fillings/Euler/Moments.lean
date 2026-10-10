import Mathlib
import OAI.Geometry.CAT0Fillings.Chord.NonnegativeMeasure
import OAI.Geometry.CAT0Fillings.Powers.PolynomialBound

namespace OAI

section
open Set Filter MeasureTheory

namespace CAT0Fillings.ChordMeasure
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ σ : X → ℝ}
lemma total_congr (h : ρ =ᵐ[μ] σ) : total μ ρ = total μ σ := integral_congr_ae h
lemma probability_congr (h : ρ =ᵐ[μ] σ) : probability μ ρ = probability μ σ := by
  rw [probability,probability,total_congr h]
  apply withDensity_congr_ae
  filter_upwards [h] with x hx
  rw [hx]
lemma ae_of_ae (h : ∀ᵐ x ∂μ, ρ x = σ x) (w : X → ℝ) :
    ρ =ᵐ[probability μ w] σ := withDensity_absolutelyContinuous _ _ h
end CAT0Fillings.ChordMeasure
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma inner_power_inclusion (v ψ : q.Sobolev) {β : ℝ} (hb : 0 < β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hψ : (q.inclusion ψ : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => (q.inclusion v x)^(1+2*β))) :
    inner ℝ (q.inclusion v) (q.inclusion ψ) =
      ∫ x, (q.inclusion v x)^(2+2*β) ∂MassMeasure.currentMassMeasure hT := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hψ,hv] with x hx hp
    simp only [RCLike.inner_apply,conj_trivial,hx]
    conv_lhs => rhs; rw [←Real.rpow_one (q.inclusion v x)]
    rw [←Real.rpow_add' hp (by linarith : 1+2*β+1 ≠ 0)]
    congr 1
    ring

lemma power_pair_integral (v ψ : q.Sobolev) {β : ℝ} (hb : 0 < β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hψ : (q.inclusion ψ : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => (q.inclusion v x)^(1+2*β))) :
    (∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT) =
      ∫ x, (q.inclusion v x)^(2+6*β) ∂MassMeasure.currentMassMeasure hT := by
    apply integral_congr_ae
    filter_upwards [hψ,hv] with x hx hp
    rw [hx,←Real.rpow_add' hp (by linarith : 1+4*β+(1+2*β) ≠ 0)]
    congr 1
    ring

lemma inner_power_gradient (v ψ : q.Sobolev) {β : ℝ}
    (hDψ : (q.closedGradient ψ : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => ((1+2*β)*(q.inclusion v (q.atlasParam w))^((1+2*β)-1)) • q.closedGradient v w)) :
    inner ℝ (q.closedGradient v) (q.closedGradient ψ) =
      (1+2*β)*(∫ w, (q.inclusion v (q.atlasParam w))^(2*β)*‖q.closedGradient v w‖^2 ∂q.atlasMeasure) := by
    rw [L2.inner_def,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hDψ] with w hw
    rw [hw,real_inner_smul_right,real_inner_self_eq_norm_sq]
    simp only [add_sub_cancel_left]
    ring

lemma euler_weighted_moment (v : q.Sobolev) {β : ℝ} (hb : 0 < β)
    (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => (q.inclusion v x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion v (q.atlasParam w))^(γ-1)) • q.closedGradient v w))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT)) :
    (∫ w, (q.inclusion v (q.atlasParam w))^(2+2*β)+
      4*β^2*(q.inclusion v (q.atlasParam w))^(2*β)*‖q.closedGradient v w‖^2 ∂q.atlasMeasure) =
      ∫ x, (q.inclusion v x)^(2+6*β) ∂MassMeasure.currentMassMeasure hT := by
  obtain ⟨ψ,hψ,hDψ⟩ := hpow (1+2*β) (by linarith)
  have he := heuler ψ
  have hI := q.inner_power_inclusion v ψ hb hv hψ
  have hR := q.power_pair_integral v ψ hb hv hψ
  have hD := q.inner_power_gradient v ψ hDψ
  rw [hI,hR,hD] at he
  have hi := (ClosedCalculus.power_memLp_two hv hm (a := 2+2*β) (by positivity)).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hiA := q.atlas_preserving.integrable_comp_of_integrable hi
  change Integrable (fun w => (q.inclusion v (q.atlasParam w))^(2+2*β)) q.atlasMeasure at hiA
  have hw := q.polynomial_weighted_energy v hv (fun γ hγ => by
    obtain ⟨R,_,hR⟩ := hpow γ hγ
    exact ⟨R,hR⟩) (show 0 ≤ 2*β by positivity)
  rw [integral_add hiA ((hw.const_mul (4*β^2)).congr (Eventually.of_forall fun _ => by ring)),
    show (∫ w, 4*β^2*(q.inclusion v (q.atlasParam w))^(2*β)*‖q.closedGradient v w‖^2 ∂q.atlasMeasure) =
      4*β^2*(∫ w, (q.inclusion v (q.atlasParam w))^(2*β)*‖q.closedGradient v w‖^2 ∂q.atlasMeasure) by
        rw [←integral_const_mul]; congr 1; funext w; ring]
  have hAt := integral_map (μ := q.atlasMeasure) (f := (fun x => (q.inclusion v x)^(2+2*β))) q.atlas_preserving.measurable.aemeasurable
    (by rw [q.atlas_preserving.map_eq]; exact hi.aestronglyMeasurable)
  rw [q.atlas_preserving.map_eq] at hAt
  rw [←hAt]
  have hn0 : (k+1:ℝ) ≠ 0 := by positivity
  have hc : 4*β*(1+2*β) = (k+1:ℝ)*(4*β^2) := by rw [←hn]; ring
  rw [←mul_assoc,hc] at he
  apply (mul_left_cancel₀ hn0)
  nlinarith [he]
end CAT0Fillings.ChartGeometry
end

end OAI
