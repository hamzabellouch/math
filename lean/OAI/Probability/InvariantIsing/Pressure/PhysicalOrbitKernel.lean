import OAI.Probability.InvariantIsing.Core.InvariantOrbitLaw
import OAI.Probability.InvariantIsing.Pressure.RandomOrbitLaw

namespace OAI

/-! Fixed-data sections of the physical pressure and right-Haar transport. -/
noncomputable section
open MeasureTheory
namespace InvariantIsing

lemma measurable_dataPhysicalPressure_section {N : ℕ} (hN : 0 < N)
    (d : FieldSpectralData N) : Measurable (dataPhysicalPressure d) := by
  exact Measurable.of_uncurry_left (f := dataPhysicalPressure) (x := d)
    (measurable_dataPhysicalPressure hN)

lemma physical_orbit_kernel {N : ℕ} (hN : 0 < N)
    (H : Measure (Orthogonal N)) [H.IsMulRightInvariant]
    (d : FieldSpectralData N) (Y : Orthogonal N → ℝ) (V : Orthogonal N)
    (hY : ∀ U, Y U=dataPhysicalPressure d (U*V)) :
    H.map (fun U => (d,Y U))=H.map (fun U => (d,dataPhysicalPressure d U)) := by
  exact paired_map_eq_of_comp H d (dataPhysicalPressure d) Y (fun U => U*V)
    (measurable_dataPhysicalPressure_section hN d) (measurable_id.mul_const V)
    (map_mul_right_eq_self H V) hY

end InvariantIsing

end

end OAI
