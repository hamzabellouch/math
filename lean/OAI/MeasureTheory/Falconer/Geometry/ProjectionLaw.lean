import OAI.MeasureTheory.Falconer.Fourier.HalfDimensionalFourier
import OAI.MeasureTheory.Falconer.Fourier.DistanceSincCollision

namespace OAI

/-! # The actual scalar projection law and its sinc collision bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

noncomputable def scalarProjectionLaw (μ : Measure (Space d)) (w : Space d) : Measure ℝ :=
  μ.map (fun x => inner ℝ x w)

instance scalarProjectionLaw_finite (μ : Measure (Space d)) [IsFiniteMeasure μ] (w : Space d) :
    IsFiniteMeasure (scalarProjectionLaw μ w) := by unfold scalarProjectionLaw; infer_instance

theorem charFun_scalarProjectionLaw (μ : Measure (Space d)) (w : Space d) (r : ℝ) :
    charFun (scalarProjectionLaw μ w) r = charFun μ (r • w) := by
  rw [charFun_apply,scalarProjectionLaw,integral_map (by fun_prop) (by fun_prop),charFun_apply]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_smul_right,real_inner_eq_re_inner]
  congr 2

theorem norm_charFun_scalarProjectionLaw (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (w : Space d) (r : ℝ) :
    ‖charFun (scalarProjectionLaw μ w) (2*Real.pi*r)‖ =
      ‖PlanarFalconer.sourceFourier μ (r • w)‖ := by
  rw [charFun_scalarProjectionLaw,PlanarFalconer.sourceFourier]
  have he : (-(2*Real.pi)) • (r • w) = -((2*Real.pi*r) • w) := by module
  rw [he,charFun_neg]
  exact (Complex.norm_conj _).symm

noncomputable def projectionCollision (μ : Measure (Space d)) (w : Space d) (ε : ℝ) : ℝ≥0∞ :=
  (μ.prod μ) {z : Space d × Space d | |inner ℝ (z.1-z.2) w| ≤ ε}

theorem scalarProjectionLaw_collision (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (w : Space d) (ε : ℝ) :
    ((scalarProjectionLaw μ w).prod (scalarProjectionLaw μ w))
      {z : ℝ × ℝ | |z.1-z.2| ≤ ε} = projectionCollision μ w ε := by
  have hm : Measurable (fun x : Space d => inner ℝ x w) := by fun_prop
  rw [scalarProjectionLaw,Measure.map_prod_map μ μ hm hm,
    Measure.map_apply (hm.prodMap hm) (by measurability)]
  congr 1
  ext z
  simp only [mem_preimage,mem_ofPred_eq,Prod.map_fst,Prod.map_snd,inner_sub_left]

theorem projection_collision_fourier : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure (Space d)) [IsFiniteMeasure μ] (w : Space d) (A : ℝ), 0 < A →
      A*(projectionCollision μ w (100/A)).toReal ≤
        C*∫ r in Icc (-A) A, ‖charFun (scalarProjectionLaw μ w) r‖^2 := by
  obtain ⟨C,hC,hbound⟩ := PlanarFalconer.finite_measure_distance_collision_fourier
  refine ⟨C,hC,?_⟩
  intro μ _ w A hA
  have h := hbound (scalarProjectionLaw μ w) A hA
  simpa only [measureReal_def,scalarProjectionLaw_collision] using h

end Falconer

end OAI
