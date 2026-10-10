import OAI.Geometry.RCD.Harmonic.HarmonicModelCompactness

namespace OAI

/-! # Discharging the published finite harmonic-moment compactness input -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonicMomentCompactnessInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) :
    LocalHarmonicMomentCompactnessInput hX := by
  intro S hS p r ε hr hcurv hε hεlim u v w hv hrep hw hnorm _
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hεlim.eventually (Iio_mem_nhds zero_lt_one))
  obtain ⟨a,ha,model,_,_,hmom,_⟩ := hX.harmonic_model_compactness hn hS
    (fun k => p (k+N)) (fun k => r (k+N)) (fun k => ε (k+N))
    (fun k => hr (k+N)) (fun k => hcurv (k+N))
    (fun k => (hε (k+N)).le) (fun k => (hN (k+N) (Nat.le_add_left N k)).le)
    (hεlim.comp (tendsto_add_atTop_nat N))
    (fun k => u (k+N)) (fun k => v (k+N)) (fun k => w (k+N))
    (fun k => hv (k+N)) (fun k j => hrep (k+N) j)
    (fun k => hw (k+N)) (fun k => hnorm (k+N))
  refine ⟨fun k => a k+N,fun i j hij => Nat.add_lt_add_right (ha hij) N,model,?_⟩
  intro ρ hρ hρS i j
  exact hmom ρ hρ hρS i j

end RegularPointCoordinates

end

end OAI
