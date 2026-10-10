import OAI.Analysis.IrrationalRotation.Sampling.CirclePhaseSummability
import OAI.Analysis.IrrationalRotation.Rotation.CircleRepresentative
import OAI.Analysis.IrrationalRotation.Rotation.CocycleSupport
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem measurePreserving_coordinate (i : ℕ) :
    MeasurePreserving (p.coordinate i) circleMeasure
      (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  have hq : (p.q i : ℤ) ≠ 0 := by exact_mod_cast (hp.q_pos i).ne'
  have hchar := Measure.measurePreserving_zsmul (volume : Measure Circle) hq
  change MeasurePreserving
    (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 (p.q i • x) : ℝ))
    (volume : Measure Circle) (volume.restrict (Set.Ico (0 : ℝ) 1))
  convert CocycleSupport.measurePreserving_circleRepresentative.comp hchar using 1
  funext x
  simp only [Function.comp_def, natCast_zsmul]

theorem ae_all_int_finite_floor_support :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, Function.HasFiniteSupport
      (fun n : ℕ => ⌊p.coordinate (n + 1) x + (k : ℝ) * p.alpha θ (n + 1)⌋) := by
  exact CocycleSupport.ae_all_int_finite_floor_support circleMeasure
    (fun n => p.coordinate (n + 1))
    (fun n => (hp.measurePreserving_coordinate (n + 1)).measurable)
    (fun n => (hp.measurePreserving_coordinate (n + 1)).map_eq)
    (fun n => p.alpha θ (n + 1)) (fun _ => Int.fract_nonneg _) hp.summable_phases

theorem ae_all_int_finite_floor_support_of_ac {ν : Measure Circle}
    (hν : ν ≪ circleMeasure) :
    ∀ᵐ x ∂ν, ∀ k : ℤ, Function.HasFiniteSupport
      (fun n : ℕ => ⌊p.coordinate (n + 1) x + (k : ℝ) * p.alpha θ (n + 1)⌋) :=
  hν.ae_le hp.ae_all_int_finite_floor_support

theorem ae_endpoint_all_int_finite_floor_support
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (x : Ω → Circle) (hx : AEMeasurable x μ)
    (hν : μ.map x ≪ circleMeasure) :
    ∀ᵐ ω ∂μ, ∀ k : ℤ, Function.HasFiniteSupport
      (fun n : ℕ => ⌊p.coordinate (n + 1) (x ω) + (k : ℝ) * p.alpha θ (n + 1)⌋) := by
  exact ae_of_ae_map hx (hp.ae_all_int_finite_floor_support_of_ac hν)

theorem ae_pair_all_int_finite_floor_support
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (x y : Ω → Circle) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hνx : μ.map x ≪ circleMeasure) (hνy : μ.map y ≪ circleMeasure) :
    ∀ᵐ ω ∂μ, ∀ k : ℤ,
      Function.HasFiniteSupport
        (fun n : ℕ => ⌊p.coordinate (n + 1) (x ω) + (k : ℝ) * p.alpha θ (n + 1)⌋) ∧
      Function.HasFiniteSupport
        (fun n : ℕ => ⌊p.coordinate (n + 1) (y ω) + (k : ℝ) * p.alpha θ (n + 1)⌋) := by
  filter_upwards [hp.ae_endpoint_all_int_finite_floor_support x hx hνx,
    hp.ae_endpoint_all_int_finite_floor_support y hy hνy] with ω hωx hωy
  exact fun k => ⟨hωx k, hωy k⟩

end Invariant233.CircleParameterLaws

end

end OAI
