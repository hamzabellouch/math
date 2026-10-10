import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Quadratic transport costs of the two legs of a geodesic triplet law -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {A X : Type*} [MeasurableSpace A] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X]

theorem transportCost_map_scale (P : Measure A) {a b c d : A → X}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hd : Measurable d)
    {r : ℝ} (hr : 0 ≤ r) (he : ∀ᵐ z ∂P, dist (a z) (b z)=r*dist (c z) (d z)) :
    transportCost (P.map (fun z => (a z,b z)))=
      ENNReal.ofReal r^2*transportCost (P.map (fun z => (c z,d z))) := by
  have hm : Measurable (fun z : X × X => ENNReal.ofReal (dist z.1 z.2)^2) := by fun_prop
  rw [transportCost,transportCost,lintegral_map hm (ha.prodMk hb),
    lintegral_map hm (hc.prodMk hd),← lintegral_const_mul _ ((hc.dist hd).ennreal_ofReal.pow_const 2)]
  apply lintegral_congr_ae
  filter_upwards [he] with z hz
  simp only [hz,ENNReal.ofReal_mul hr,mul_pow]

end RegularPointCoordinates

end

end OAI
