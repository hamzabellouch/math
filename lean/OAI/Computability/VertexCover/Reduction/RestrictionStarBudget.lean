import Mathlib
import OAI.Computability.VertexCover.Analysis.WeightEnergyBudget
import OAI.Computability.VertexCover.Analysis.ErasedSeedSeparatorAverage
import OAI.Computability.VertexCover.Reduction.ConditionNested
import OAI.Computability.VertexCover.Reduction.IntegralCoe

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Restriction.EnergyForm.Projection
open scoped BigOperators

theorem conditionMap_apply_function {S T X : Type*} [Fintype S]
    [TopologicalSpace X] (q : S → T) (f : S → C(X, ℝ)) (s : S) (x : X) :
    conditionMap q f s x = VertexCover.Average.fiberAverage q
      (fun _ t => f t x) (q s) := by
  classical
  simp only [conditionMap_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, fiberKernel, VertexCover.Average.fiberAverage, fiberSize]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  rw [div_eq_mul_inv, mul_comm]

end VertexCover.Restriction.EnergyForm.Projection

namespace VertexCover.Restriction.CompactCube

theorem realWeights_update {ι κ : Type*} [DecidableEq ι]
    (s : ι → κ → Interval) (j : ι) (x : κ → Interval) :
    realWeights (Function.update s j x) =
      Function.update (realWeights s) j (fun k => (x k).1) := by
  funext i k
  by_cases hi : i = j
  · subst i
    simp [realWeights]
  · simp [realWeights, Function.update_of_ne hi]

end VertexCover.Restriction.CompactCube

namespace VertexCover.LabelCover
open MeasureTheory
open VertexCover.Restriction
open EnergyForm.Projection

abbrev RestrictionWeights (Φ : LabelCover) (d : ℕ) :=
  Fin d → Fin (Φ.WeightDimension d) → CompactCube.Interval

abbrev RestrictionSpace (Φ : LabelCover) (d : ℕ) :=
  Φ.Seeds d → C(Φ.RestrictionWeights d, ℝ)

noncomputable def restrictionBase (Φ : LabelCover) (d : ℕ) :
    EnergyForm C(Φ.RestrictionWeights d, ℝ) :=
  EnergyForm.integral (CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))

noncomputable def restrictionForm (Φ : LabelCover) (d : ℕ) :
    EnergyForm (Φ.RestrictionSpace d) := (Φ.restrictionBase d).finite

noncomputable def restrictionFunction (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) : Φ.RestrictionSpace d :=
  fun seed => ⟨fun s => Φ.separator A hA (Φ.continuousSum seed (CompactCube.realWeights s)),
    (Φ.separator_continuousSum_continuous A hA seed).comp CompactCube.continuous_realWeights⟩

@[simp] theorem restrictionFunction_apply (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (seed : Φ.Seeds d) (s : Φ.RestrictionWeights d) :
    Φ.restrictionFunction A hA seed s =
      Φ.separator A hA (Φ.continuousSum seed (CompactCube.realWeights s)) := rfl

@[simp] theorem restrictionForm_energy (Φ : LabelCover) {d : ℕ} (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy f = VertexCover.finiteMean (fun seed =>
      ∫ s, (f seed s)^2 ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
  simp only [restrictionForm, EnergyForm.finite_energy, restrictionBase,
    EnergyForm.integral_energy, VertexCover.finiteMean, div_eq_mul_inv, mul_comm]

noncomputable def weightProjection (Φ : LabelCover) {d : ℕ} (k : Fin d) :
    (Φ.restrictionForm d).Projection :=
  (average (CompactCube.law (Fin (Φ.WeightDimension d))) k).lift

@[simp] theorem weightProjection_apply (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (f : Φ.RestrictionSpace d) (seed : Φ.Seeds d) (s : Φ.RestrictionWeights d) :
    Φ.weightProjection k f seed s =
      ∫ x, f seed (Function.update s k x) ∂CompactCube.law (Fin (Φ.WeightDimension d)) :=
  average_apply _ k (f seed) s

theorem weightProjection_commute (Φ : LabelCover) {d : ℕ} (k l : Fin d)
    (f : Φ.RestrictionSpace d) :
    Φ.weightProjection k (Φ.weightProjection l f) =
      Φ.weightProjection l (Φ.weightProjection k f) := by
  funext seed
  exact average_commute _ k l (f seed)

theorem restriction_full_mean_zero (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    productMap (Φ.weightProjection (d := d)) (List.finRange d)
      (Φ.restrictionFunction A hA) = 0 := by
  ext seed s
  change productMap (fun i => (average (CompactCube.law (Fin (Φ.WeightDimension d))) i).lift)
    (List.finRange d) (Φ.restrictionFunction A hA) seed s = 0
  rw [productMap_lift, product_average_apply _ _ (List.nodup_finRange d)]
  simp only [List.toFinset_finRange, plug_univ, restrictionFunction_apply]
  change (∫ t, Φ.separator A hA (Φ.continuousSum seed (CompactCube.realWeights t))
    ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) = 0
  rw [CompactCube.integral_realWeights
    (Φ.separator_continuousSum_continuous A hA seed).measurable.aestronglyMeasurable]
  exact Φ.separator_continuousSum_mean_zero A hA seed

noncomputable def weightGroup (Φ : LabelCover) {d : ℕ} (j : Fin d) :
    (Φ.restrictionForm d).Projection :=
  finDifference Φ.weightProjection Φ.weightProjection_commute j

theorem weightGroup_centered (Φ : LabelCover) {d : ℕ} (j : Fin d)
    (f : Φ.RestrictionSpace d) :
    (Φ.weightProjection j).residual (Φ.weightGroup j f) = Φ.weightGroup j f :=
  finDifference_centered _ _ _ _

theorem weightGroup_energy_sum (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ j : Fin d, (Φ.restrictionForm d).energy
      (Φ.weightGroup j (Φ.restrictionFunction A hA))) =
      (Φ.restrictionForm d).energy (Φ.restrictionFunction A hA) := by
  have he := finDifference_energy_sum Φ.weightProjection Φ.weightProjection_commute
    (Φ.restrictionFunction A hA)
  rw [Φ.restriction_full_mean_zero A hA, EnergyForm.energy_zero, add_zero] at he
  exact he

noncomputable def seedProjection (Φ : LabelCover) {d : ℕ} (e : PositionPair d) :
    (Φ.restrictionForm d).Projection :=
  condition (B := Φ.restrictionBase d)
    (fun seed : Φ.Seeds d => Function.update seed e ⟨0, Φ.M_pos⟩)

noncomputable def starProjection (Φ : LabelCover) {d : ℕ} (k : Fin d) :
    (Φ.restrictionForm d).Projection := condition (B := Φ.restrictionBase d) (Φ.starKey k)

noncomputable def oppositeProjection (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (e : PositionPair d) : (Φ.restrictionForm d).Projection :=
  condition (B := Φ.restrictionBase d) (Φ.oppositePairKey k e)

theorem oppositeProjection_charge (Φ : LabelCover) {d : ℕ} (k : Fin d)
    (e : PositionPair d) (he : e.1.1 = k ∨ e.1.2 = k) (f : Φ.RestrictionSpace d) :
    (Φ.restrictionForm d).energy ((Φ.oppositeProjection k e).residual f) ≤
      (Φ.restrictionForm d).energy ((Φ.starProjection k).residual f) := by
  apply residual_le_of_nested
  apply condition_nested
  intro s t h
  have hh := congrArg (Φ.starFromOppositePair k e) h
  simpa only [Φ.starFromOppositePair_key k e he] using hh

theorem condition_weightProjection_commute (Φ : LabelCover) {d : ℕ} {T : Type*}
    (q : Φ.Seeds d → T) (k : Fin d) (f : Φ.RestrictionSpace d) :
    condition (B := Φ.restrictionBase d) q (Φ.weightProjection k f) =
      Φ.weightProjection k (condition (B := Φ.restrictionBase d) q f) :=
  condition_lift_commute q _ f

theorem weightProjection_separator (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Φ.RestrictionWeights d) :
    Φ.weightProjection k (Φ.restrictionFunction A hA) seed s =
      Φ.weightMean A hA k seed (CompactCube.realWeights s) := by
  simp only [weightProjection_apply, restrictionFunction_apply, CompactCube.realWeights_update]
  unfold weightMean
  apply CompactCube.integral_coe (f := fun x =>
    Φ.separator A hA (Φ.continuousSum seed (Function.update (CompactCube.realWeights s) k x)))
  exact ((Φ.separator_continuousSum_continuous A hA seed).comp
    (continuous_const.update k continuous_id)).measurable.aestronglyMeasurable

theorem seedProjection_separator (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (e : PositionPair d)
    (seed : Φ.Seeds d) (s : Φ.RestrictionWeights d) :
    Φ.seedProjection e (Φ.restrictionFunction A hA) seed s =
      Φ.seedMean A hA e seed (CompactCube.realWeights s) := by
  change conditionMap _ (Φ.restrictionFunction A hA) seed s = _
  rw [conditionMap_apply_function]
  exact Φ.erasedSeed_separator_average A hA e seed (CompactCube.realWeights s)

theorem starProjection_separator (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (k : Fin d)
    (seed : Φ.Seeds d) (s : Φ.RestrictionWeights d) :
    Φ.starProjection k (Φ.restrictionFunction A hA) seed s =
      Φ.starMean A hA k seed (CompactCube.realWeights s) := by
  change conditionMap _ (Φ.restrictionFunction A hA) seed s = _
  rw [conditionMap_apply_function]
  exact (Φ.starMean_eq_fiberAverage A hA k seed (CompactCube.realWeights s)).symm

theorem restriction_weight_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ k : Fin d, (Φ.restrictionForm d).energy
      ((Φ.weightProjection k).residual (Φ.restrictionFunction A hA))) ≤ 4*d := by
  have he : ∀ k : Fin d, (Φ.restrictionForm d).energy
      ((Φ.weightProjection k).residual (Φ.restrictionFunction A hA)) =
      VertexCover.finiteMean (fun seed : Φ.Seeds d =>
        ∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.weightMean A hA k seed s)^2
          ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
    intro k
    rw [restrictionForm_energy]
    apply congrArg VertexCover.finiteMean
    funext seed
    simp only [residual_apply, Pi.sub_apply, ContinuousMap.sub_apply,
      restrictionFunction_apply, weightProjection_separator]
    exact CompactCube.integral_realWeights
      (((Φ.separator_continuousSum_continuous A hA seed).measurable.sub
        (Φ.weightMean_measurable A hA k seed)).pow_const 2).aestronglyMeasurable
  simp_rw [he]
  exact Φ.weight_energy_budget A hA

theorem restriction_seed_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ e : PositionPair d, (Φ.restrictionForm d).energy
      ((Φ.seedProjection e).residual (Φ.restrictionFunction A hA))) ≤ 8*(d:ℝ)^2 := by
  have he : ∀ e : PositionPair d, (Φ.restrictionForm d).energy
      ((Φ.seedProjection e).residual (Φ.restrictionFunction A hA)) =
      VertexCover.finiteMean (fun seed : Φ.Seeds d =>
        ∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.seedMean A hA e seed s)^2
          ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
    intro e
    rw [restrictionForm_energy]
    apply congrArg VertexCover.finiteMean
    funext seed
    simp only [residual_apply, Pi.sub_apply, ContinuousMap.sub_apply,
      restrictionFunction_apply, seedProjection_separator]
    exact CompactCube.integral_realWeights
      (((Φ.separator_continuousSum_continuous A hA seed).sub
        (Φ.seedMean_continuous A hA e seed)).pow 2).measurable.aestronglyMeasurable
  simp_rw [he]
  exact Φ.seed_energy_budget A hA

theorem restriction_star_budget (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ k : Fin d, (Φ.restrictionForm d).energy
      ((Φ.starProjection k).residual (Φ.restrictionFunction A hA))) ≤ 4*d := by
  have he : ∀ k : Fin d, (Φ.restrictionForm d).energy
      ((Φ.starProjection k).residual (Φ.restrictionFunction A hA)) =
      VertexCover.finiteMean (fun seed : Φ.Seeds d =>
        ∫ s, (Φ.separator A hA (Φ.continuousSum seed s) - Φ.starMean A hA k seed s)^2
          ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
    intro k
    rw [restrictionForm_energy]
    apply congrArg VertexCover.finiteMean
    funext seed
    simp only [residual_apply, Pi.sub_apply, ContinuousMap.sub_apply,
      restrictionFunction_apply, starProjection_separator]
    exact CompactCube.integral_realWeights
      (((Φ.separator_continuousSum_continuous A hA seed).sub
        (Φ.starMean_continuous A hA k seed)).pow 2).measurable.aestronglyMeasurable
  simp_rw [he]
  exact Φ.star_energy_budget A hA

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
