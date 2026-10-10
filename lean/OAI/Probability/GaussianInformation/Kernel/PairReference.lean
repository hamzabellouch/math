import Mathlib
import OAI.Probability.GaussianInformation.Kernel.RowConcatenation

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.PairReference
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Sphere Coercivity Scale ReferenceGaussian GaussianTools RowConcat
noncomputable def density {k d L : ℕ} (ν : Measure (Ambient d)) (r : Fin L → ℝ)
    (X Z : Mat k d) (y z : Fin k → ℝ) : ℝ :=
  mixture ν r (join k (X,Z)) (join k (y,z))

lemma density_pos {k d L : ℕ} (hL : 0 < L) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (r : Fin L → ℝ) (hr : ∀ j,0 < r j)
    (X Z : Mat k d) (y z : Fin k → ℝ) : 0 < density ν r X Z y z :=
  mixture_pos hL ν r hr _ _

lemma density_measurable {k d L : ℕ} (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (r : Fin L → ℝ) : Measurable (fun t : (Mat k d × Mat k d) × ((Fin k → ℝ) × (Fin k → ℝ)) =>
      density ν r t.1.1 t.1.2 t.2.1 t.2.2) := by
  have hM := measurable_mixture (p := 2*k) ν r
  have hX := (join (E := Fin d → ℝ) k).measurable
  have hY := (join (E := ℝ) k).measurable
  unfold density
  fun_prop

lemma density_probability {k d L : ℕ} (hL : 0 < L) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (X Z : Mat k d) :
    (∫⁻ yz : (Fin k → ℝ) × (Fin k → ℝ),ENNReal.ofReal (density ν r X Z yz.1 yz.2)
      ∂(volume : Measure (Fin k → ℝ)).prod volume)=1 := by
  have hm : Measurable (fun y : Fin (2*k) → ℝ => ENNReal.ofReal (mixture ν r (join k (X,Z)) y)) :=
    ((measurable_mixture ν r).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have h := (join_volume_measurePreserving k).lintegral_comp hm
  change (∫⁻ yz,ENNReal.ofReal (mixture ν r (join k (X,Z)) (join k yz)) ∂volume.prod volume)=1
  rw [h]
  exact lintegral_mixture hL ν r hr _

lemma rows_integral {k d L : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (r : Fin L → ℝ) (s : Ambient d) (e e' : Fin k → ℝ) :
    (∫ XZ : Mat k d × Mat k d,Real.log (density ν r XZ.1 XZ.2
      (applyRows XZ.1 s+e) (applyRows XZ.2 s+e'))
      ∂(Measure.pi (fun _ : Fin k => scalarRow d)).prod (Measure.pi (fun _ : Fin k => scalarRow d)))=
        ∫ X : Mat (2*k) d,Real.log (mixture ν r X (applyRows X s+join k (e,e')))
          ∂Measure.pi (fun _ : Fin (2*k) => scalarRow d) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have he (X Z : Mat k d) : join k (applyRows X s+e,applyRows Z s+e')=
      applyRows (join k (X,Z)) s+join k (e,e') := by
    rw [join_add,show join k (applyRows X s,applyRows Z s)=applyRows (join k (X,Z)) s from join_rows k d X Z s]
  simp only [density,he]
  exact (join_measurePreserving k (scalarRow d)).integral_comp (join k).measurableEmbedding
    (fun X => Real.log (mixture ν r X (applyRows X s+join k (e,e'))))

lemma reference_J_lower_pair {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (s : Ambient d) (hs : ‖s‖=1) (L : ℕ) (hL : 0 < L)
    (hcut : ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
      ENNReal.ofReal ((2:ℝ)^(2*(d/16)+1))*ENNReal.ofReal ((1/2:ℝ)^L) ≤ 1)
    (e e' : Fin (d/16) → ℝ) (he : ∀ i,|e i| ≤ radius L) (he' : ∀ i,|e' i| ≤ radius L) :
    Real.log (J ν s).toReal-10*(d:ℝ)-2*Real.log ((L:ℝ)+2) ≤
      (∫ XZ : Mat (d/16) d × Mat (d/16) d,
        Real.log (density ν (fun j : Fin L => radius j) XZ.1 XZ.2
          (applyRows XZ.1 s+e) (applyRows XZ.2 s+e'))
        ∂(Measure.pi (fun _ : Fin (d/16) => scalarRow d)).prod
          (Measure.pi (fun _ : Fin (d/16) => scalarRow d))) := by
  rw [rows_integral]
  exact reference_J_lower hd ν hH hν s hs L hL hcut _
    (join_bound _ _ _ (fun x : ℝ => |x| ≤ radius L) he he')
end KernelPotential.PairReference

end OAI
