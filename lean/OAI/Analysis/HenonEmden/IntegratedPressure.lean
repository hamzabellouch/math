import OAI.Analysis.HenonEmden.AngularLoss

namespace OAI

universe uα

section IntegratedPressure

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents LayerTonelli

lemma integrate_pressure_sum {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    {F G P Q L J D H : α → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    (hP : Measurable P) (hQ : Measurable Q) (hL : Measurable L) (hJ : Measurable J)
    (hD : Measurable D) (hH : Measurable H) {a b c d : ℝ≥0∞}
    (hh : ∀ x, a*F x+b*G x ≤ P x+Q x+2*(L x+J x)+(c*D x+d*H x)) :
    a*(∫⁻ x, F x ∂μ)+b*(∫⁻ x, G x ∂μ) ≤
      (∫⁻ x, P x ∂μ)+(∫⁻ x, Q x ∂μ)+2*((∫⁻ x, L x ∂μ)+(∫⁻ x, J x ∂μ))+
        (c*(∫⁻ x, D x ∂μ)+d*(∫⁻ x, H x ∂μ)) := by
  have hPQ : Measurable (fun x => P x+Q x) := hP.add hQ
  have hLJ : Measurable (fun x => L x+J x) := hL.add hJ
  have hAll : Measurable (fun x => P x+Q x+2*(L x+J x)) := hPQ.add (hLJ.const_mul 2)
  have hb := lintegral_mono (μ := μ) hh
  rw [lintegral_add_left (hF.const_mul a),lintegral_const_mul _ hF,lintegral_const_mul _ hG,
    lintegral_add_left hAll,
    lintegral_add_left hPQ,lintegral_add_left hP,
    lintegral_const_mul _ hLJ,lintegral_add_left hL,
    lintegral_add_left (hD.const_mul c),lintegral_const_mul _ hD,lintegral_const_mul _ hH] at hb
  exact hb

lemma IsSolution.integrated_directional_pressure {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (1/(q+1))*weightedEnergyN (w n) u q B+
      ENNReal.ofReal (1/(p+1))*weightedEnergyN (w n) v p A ≤
      (∫⁻ e : sphere (0:Space n) 1, capPressureIntegral (source u q B) (source v p A) κ e ∂volume.toSphere)+
      (∫⁻ e : sphere (0:Space n) 1, capMismatchIntegral (source u q B) (source v p A) κ e ∂volume.toSphere)+
      2*((∫⁻ e : sphere (0:Space n) 1, lossIntegral u (source u q B) κ δ e ∂volume.toSphere)+
        (∫⁻ e : sphere (0:Space n) 1, lossIntegral v (source v p A) κ δ e ∂volume.toSphere))+
      (ENNReal.ofReal (endpointConstant q B*δ)*weightedEnergyN (fun x => d x*w n x) u q B+
      ENNReal.ofReal (endpointConstant p A*δ)*weightedEnergyN (fun x => d x*w n x) v p A) := by
  have hn1 : 1 ≤ n := by omega
  have hb := integrate_pressure_sum (μ := (volume : Measure (Space n)).toSphere)
    (measurable_cap_energy hn1 hκ hκ1 h.continuous_u q B)
    (measurable_cap_energy hn1 hκ hκ1 h.continuous_v p A)
    (measurable_cap_pressure hn1 hκ hκ1 _ _) (measurable_cap_mismatch hn1 hκ hκ1 _ _)
    (measurable_cap_loss hn1 hκ hκ1 h.continuous_u.measurable (isOpen_source_subgraph h.regular_u h.positive_u q B))
    (measurable_cap_loss hn1 hκ hκ1 h.continuous_v.measurable (isOpen_source_subgraph h.regular_v h.positive_v p A))
    (measurable_cap_d_energy hn1 hκ hκ1 h.continuous_u q B)
    (measurable_cap_d_energy hn1 hκ hκ1 h.continuous_v p A)
    (IsSolution_directional_pressure hn h hp hq hκ hκ1 hδ)
  rw [lintegral_angular_energy hn1 hκ hκ1 h.continuous_u,
    lintegral_angular_energy hn1 hκ hκ1 h.continuous_v,
    lintegral_angular_d_energy hn1 hκ hκ1 h.continuous_u,
    lintegral_angular_d_energy hn1 hκ hκ1 h.continuous_v] at hb
  exact hb

end HenonLaneEmden
end
end IntegratedPressure

end OAI
