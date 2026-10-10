import Mathlib
import OAI.Computability.VertexCover.Analysis.OwnTotalVarianceNo
import OAI.Computability.VertexCover.Reduction.PrivateProjectionCoordinateVariance

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
namespace VertexCover.Restriction
open scoped BigOperators

def spliceSwap {ι X : Type*} [DecidableEq ι] (J : Finset ι) :
    ((ι → X) × (J → X)) ≃ ((ι → X) × (J → X)) where
  toFun p := (splice J p.1 p.2, fun i => p.1 i)
  invFun p := (splice J p.1 p.2, fun i => p.1 i)
  left_inv p := by
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ J <;> simp [splice, hi]
    · funext i
      simp [splice, i.2]
  right_inv p := by
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ J <;> simp [splice, hi]
    · funext i
      simp [splice, i.2]

theorem finiteMean_splice {ι X : Type*} [Fintype ι] [Fintype X] [Nonempty X]
    [DecidableEq ι] (J : Finset ι) (f : (ι → X) → ℝ) :
    VertexCover.finiteMean (fun s => VertexCover.finiteMean (fun t => f (splice J s t))) =
      VertexCover.finiteMean f := by
  rw [← VertexCover.finiteMean_product (fun p : (ι → X) × (J → X) => f (splice J p.1 p.2))]
  exact (VertexCover.finiteMean_equiv (spliceSwap J)
    (fun p : (ι → X) × (J → X) => f p.1)).trans (VertexCover.finiteMean_product_fst f)

end VertexCover.Restriction

namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

theorem ownVariance_frozen_continuous (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Continuous (fun s : Φ.RestrictionWeights d =>
      variance (Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s))
        A hA j (Φ.query seed j)) (VertexCover.Cube.law (Fin (Φ.WeightDimension d)))) := by
  let F : C(Φ.RestrictionWeights d, ℝ) :=
    ⟨fun s => (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed s)^2,
      (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed).continuous.pow 2⟩
  have he : (fun s : Φ.RestrictionWeights d =>
      variance (Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s))
        A hA j (Φ.query seed j)) (VertexCover.Cube.law (Fin (Φ.WeightDimension d)))) =
        (fun s => EnergyForm.Projection.average (CompactCube.law (Fin (Φ.WeightDimension d))) (j : Fin d) F s) := by
    funext s
    rw [EnergyForm.Projection.average_apply]
    exact (Φ.privateProjection_coordinate_variance J frozen j seed ho A hA s).symm
  rw [he]
  exact (EnergyForm.Projection.average (CompactCube.law (Fin (Φ.WeightDimension d))) (j : Fin d) F).continuous

theorem ownVariance_frozen_integrable (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Integrable (fun s : Φ.RestrictionWeights d =>
      variance (Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s))
        A hA j (Φ.query seed j)) (VertexCover.Cube.law (Fin (Φ.WeightDimension d))))
      (CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) :=
  (Φ.ownVariance_frozen_continuous J frozen j seed ho A hA).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem privateProjection_integral_variance (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∫ s, (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed s)^2
      ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) =
    ∫ s : Φ.RestrictionWeights d,
      variance (Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s))
        A hA j (Φ.query seed j)) (VertexCover.Cube.law (Fin (Φ.WeightDimension d)))
      ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)) := by
  classical
  calc
    _ = ∫ s, ∫ x, (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed
        (Function.update s j x))^2 ∂CompactCube.law (Fin (Φ.WeightDimension d))
        ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)) := by
      symm
      apply VertexCover.Product.integral_update_right
        (CompactCube.law (Fin (Φ.WeightDimension d))) (j : Fin d)
        (f := fun s => (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed s)^2)
      exact ((Φ.privateProjection J j (Φ.restrictionFunction A hA) seed).continuous.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall
      (Φ.privateProjection_coordinate_variance J frozen j seed ho A hA))

theorem finiteMean_spliceSeeds (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (f : Φ.Seeds d → ℝ) :
    VertexCover.finiteMean (fun frozen => VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
      f (Φ.spliceSeeds J frozen hidden))) = VertexCover.finiteMean f := by
  classical
  have : Nonempty (Fin Φ.M) := ⟨⟨0, Φ.M_pos⟩⟩
  exact finiteMean_splice (internalPairs J) f

theorem ownTotalVariance_frozen_integrable (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Integrable (fun s : Φ.RestrictionWeights d => Φ.ownTotalVariance J frozen
      (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA)
      (CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
  classical
  apply integrable_finsetSum
  intro j _
  apply VertexCover.integrable_finiteMean
  intro hidden
  exact Φ.ownVariance_frozen_integrable J frozen j (Φ.spliceSeeds J frozen hidden)
    (fun e he => (Φ.spliceSeeds_at_outside J frozen hidden e he).symm) A hA

theorem privateTotal_energy_law (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    (∑ j : J, (Φ.restrictionForm d).energy
      (Φ.privateProjection J j (Φ.restrictionFunction A hA))) =
      VertexCover.finiteMean (fun frozen : Φ.Seeds d =>
        ∫ s : Φ.RestrictionWeights d, Φ.ownTotalVariance J frozen
          (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA
          ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
  classical
  let V := fun (frozen : Φ.Seeds d) (j : J) (hidden : Φ.HiddenSeeds J)
      (s : Φ.RestrictionWeights d) =>
    variance (Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s))
      A hA j (Φ.query (Φ.spliceSeeds J frozen hidden) j))
      (VertexCover.Cube.law (Fin (Φ.WeightDimension d)))
  have hI : ∀ frozen j hidden, Integrable (V frozen j hidden)
      (CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
    intro frozen j hidden
    exact Φ.ownVariance_frozen_integrable J frozen j (Φ.spliceSeeds J frozen hidden)
      (fun e he => (Φ.spliceSeeds_at_outside J frozen hidden e he).symm) A hA
  have he : ∀ j : J, (Φ.restrictionForm d).energy
      (Φ.privateProjection J j (Φ.restrictionFunction A hA)) =
      VertexCover.finiteMean (fun frozen : Φ.Seeds d =>
        ∫ s, VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J => V frozen j hidden s)
          ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) := by
    intro j
    rw [restrictionForm_energy]
    calc
      _ = VertexCover.finiteMean (fun frozen : Φ.Seeds d =>
          VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
            ∫ s, (Φ.privateProjection J j (Φ.restrictionFunction A hA)
              (Φ.spliceSeeds J frozen hidden) s)^2
              ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))) :=
        (Φ.finiteMean_spliceSeeds J (fun seed : Φ.Seeds d =>
          ∫ s : Φ.RestrictionWeights d,
            (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed s)^2
            ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))).symm
      _ = VertexCover.finiteMean (fun frozen : Φ.Seeds d =>
          VertexCover.finiteMean (fun hidden : Φ.HiddenSeeds J =>
            ∫ s, V frozen j hidden s
              ∂CompactCube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))) := by
        apply congrArg VertexCover.finiteMean
        funext frozen
        apply congrArg VertexCover.finiteMean
        funext hidden
        exact Φ.privateProjection_integral_variance J frozen j (Φ.spliceSeeds J frozen hidden)
          (fun e he => (Φ.spliceSeeds_at_outside J frozen hidden e he).symm) A hA
      _ = _ := by
        apply congrArg VertexCover.finiteMean
        funext frozen
        exact (VertexCover.integral_finiteMean _ _ (hI frozen j)).symm
  simp_rw [he]
  rw [← VertexCover.finiteMean_sum]
  apply congrArg VertexCover.finiteMean
  funext frozen
  unfold ownTotalVariance
  exact (integral_finsetSum _ (fun j _ =>
    VertexCover.integrable_finiteMean _ _ (hI frozen j))).symm

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
