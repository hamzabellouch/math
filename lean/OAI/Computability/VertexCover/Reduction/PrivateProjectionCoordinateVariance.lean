import Mathlib
import OAI.Computability.VertexCover.Analysis.SeparatorBoundCube
import OAI.Computability.VertexCover.Reduction.PrivateProjectionGroupLower

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
namespace VertexCover.LabelCover
open MeasureTheory
open VertexCover.Restriction
open EnergyForm.Projection
open scoped BigOperators

theorem spliceSeeds_at_inside (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (hidden : Φ.HiddenSeeds J) (e : ↥(internalPairs J)) :
    Φ.spliceSeeds J frozen hidden e = hidden e := by
  simp only [spliceSeeds, dite_eq_left e.2]

theorem spliceSeeds_at_outside (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (hidden : Φ.HiddenSeeds J) (e : PositionPair d)
    (he : e ∉ internalPairs J) : Φ.spliceSeeds J frozen hidden e = frozen e := by
  simp only [spliceSeeds, dite_eq_right he]

noncomputable def privateFiber (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (j : Fin d) (seed : Φ.Seeds d) : Finset (Φ.Seeds d) := by
  classical
  exact Finset.univ.filter (fun t => Φ.privateSeedKey J j t = Φ.privateSeedKey J j seed)

@[simp] theorem mem_privateFiber (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (j : Fin d) (seed t : Φ.Seeds d) : t ∈ Φ.privateFiber J j seed ↔
      Φ.privateSeedKey J j t = Φ.privateSeedKey J j seed := by
  classical
  simp only [privateFiber, Finset.mem_filter, Finset.mem_univ, true_and]

theorem spliceSeeds_restrict_of_outside (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen seed : Φ.Seeds d) (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e) :
    Φ.spliceSeeds J frozen (fun e : ↥(internalPairs J) => seed e) = seed := by
  funext e
  by_cases he : e ∈ internalPairs J
  · simp only [spliceSeeds, dite_eq_left he]
  · simpa only [spliceSeeds, dite_eq_right he] using ho e he

noncomputable def privateFiberEquiv (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e) :
    Φ.ownFiber J frozen j (Φ.query seed j) ≃ Φ.privateFiber J j seed := by
  classical
  have reconstruct : ∀ t : Φ.privateFiber J j seed,
      Φ.spliceSeeds J frozen (fun e : ↥(internalPairs J) => t.1 e) = t.1 := by
    intro t
    apply Φ.spliceSeeds_restrict_of_outside
    intro e he
    have ht := (Φ.privateSeedKey_eq_iff J j t.1 seed).mp ((Φ.mem_privateFiber J j seed t.1).mp t.2)
    exact (ho e he).trans (ht.1 e he).symm
  exact {
    toFun := fun hidden => ⟨Φ.spliceSeeds J frozen hidden.1, by
      apply (Φ.mem_privateFiber J j seed _).mpr
      apply (Φ.privateSeedKey_eq_iff J j _ _).mpr
      exact ⟨fun e he => (Φ.spliceSeeds_at_outside J frozen hidden.1 e he).trans (ho e he),
        (Φ.mem_ownFiber J frozen j (Φ.query seed j) hidden.1).mp hidden.2⟩⟩
    invFun := fun t => ⟨fun e => t.1 e, by
      apply (Φ.mem_ownFiber J frozen j (Φ.query seed j) _).mpr
      rw [reconstruct t]
      exact ((Φ.privateSeedKey_eq_iff J j t.1 seed).mp
        ((Φ.mem_privateFiber J j seed t.1).mp t.2)).2⟩
    left_inv := fun hidden => by
      apply Subtype.ext
      funext e
      exact Φ.spliceSeeds_at_inside J frozen hidden.1 e
    right_inv := fun t => Subtype.ext (reconstruct t) }

theorem fiberAverage_eq_finiteMean {S T : Type*} [Fintype S]
    (q : S → T) (f : S → ℝ) (i : T) (ts : Finset S)
    (ht : ∀ s, s ∈ ts ↔ q s = i) :
    VertexCover.Average.fiberAverage q (fun _ => f) i =
      VertexCover.finiteMean (fun s : ts => f s) := by
  classical
  have he : Finset.univ.filter (fun s => q s = i) = ts := by
    ext s
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (ht s).symm
  unfold VertexCover.Average.fiberAverage
  rw [he, VertexCover.Average.finiteMean_finset ts f]

theorem privateSeedProjection_fiber (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (f : Φ.RestrictionSpace d) (s : Φ.RestrictionWeights d) :
    Φ.privateSeedProjection J j f seed s =
      VertexCover.finiteMean (fun hidden : Φ.ownFiber J frozen j (Φ.query seed j) =>
        f (Φ.spliceSeeds J frozen hidden.1) s) := by
  classical
  change conditionMap _ f seed s = _
  rw [conditionMap_apply_function]
  calc
    _ = VertexCover.finiteMean (fun t : Φ.privateFiber J j seed => f t.1 s) := by
      exact fiberAverage_eq_finiteMean (Φ.privateSeedKey J j) (fun t => f t s)
        (Φ.privateSeedKey J j seed) (Φ.privateFiber J j seed)
        (fun t => Φ.mem_privateFiber J j seed t)
    _ = _ := (VertexCover.finiteMean_equiv (Φ.privateFiberEquiv J frozen j seed ho)
      (fun t : Φ.privateFiber J j seed => f t.1 s)).symm

theorem otherWeightProjection_apply (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (j : J) (f : Φ.RestrictionSpace d)
    (seed : Φ.Seeds d) (s : Φ.RestrictionWeights d) :
    Φ.otherWeightProjection J j f seed s =
      ∫ t, f seed (splice J s (Function.update t j (s j)))
        ∂CompactCube.blockLaw J (Fin (Φ.WeightDimension d)) := by
  change productMap (fun i => (average (CompactCube.law (Fin (Φ.WeightDimension d))) i).lift)
    (J.erase j).toList f seed s = _
  rw [productMap_lift, product_average_apply _ _ (J.erase j).nodup_toList,
    Finset.toList_toFinset]
  exact integral_plug_erase _ J j (f seed) s

theorem realWeights_splice (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (s : Φ.RestrictionWeights d)
    (t : J → Fin (Φ.WeightDimension d) → CompactCube.Interval) :
    CompactCube.realWeights (splice J s t) =
      Φ.spliceWeights J (CompactCube.realWeights s) (CompactCube.realWeights t) := by
  classical
  funext i k
  by_cases hi : i ∈ J
  · simp only [splice, spliceWeights, CompactCube.realWeights, dite_eq_left hi]
  · simp only [splice, spliceWeights, CompactCube.realWeights, dite_eq_right hi]

theorem otherWeightProjection_separator_splice (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (hidden : Φ.HiddenSeeds J) (s : Φ.RestrictionWeights d) :
    Φ.otherWeightProjection J j (Φ.restrictionFunction A hA)
      (Φ.spliceSeeds J frozen hidden) s =
      ∫ other, Φ.batchFunction (Φ.spliceSeeds J frozen hidden) J
        (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA
        (Function.update other j (CompactCube.realWeights s j)) ∂Φ.batchLaw J := by
  classical
  rw [Φ.otherWeightProjection_apply]
  simp only [restrictionFunction_apply, Φ.realWeights_splice, CompactCube.realWeights_update]
  simp_rw [← Φ.batchFunction_is_restriction J frozen (CompactCube.realWeights s) A hA]
  apply CompactCube.integral_realWeights (f := fun other : Φ.BatchWeights J =>
    Φ.batchFunction (Φ.spliceSeeds J frozen hidden) J
      (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA
      (Function.update other j (CompactCube.realWeights s j)))
  exact ((Φ.batchFunction_continuous _ J _ A hA).comp
    (continuous_id.update j continuous_const)).measurable.aestronglyMeasurable

theorem privateAverageProjection_separator (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.RestrictionWeights d) :
    Φ.privateAverageProjection J j (Φ.restrictionFunction A hA) seed s =
      Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA
        j (Φ.query seed j) (CompactCube.realWeights s j) := by
  change Φ.privateSeedProjection J j
    (Φ.otherWeightProjection J j (Φ.restrictionFunction A hA)) seed s = _
  rw [Φ.privateSeedProjection_fiber J frozen j seed ho]
  unfold ownMean
  congr 1
  funext hidden
  exact Φ.otherWeightProjection_separator_splice J frozen j A hA hidden.1 s

theorem outsideSum_update (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) (j : J)
    (x : Fin (Φ.WeightDimension d) → ℝ) :
    Φ.outsideSum J frozen (Function.update s j x) = Φ.outsideSum J frozen s := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≠ j := by
    intro h
    exact (Finset.mem_compl.mp hk) (h ▸ j.2)
  rw [Function.update_of_ne hkj]

theorem privateProjection_separator (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.RestrictionWeights d) :
    Φ.privateProjection J j (Φ.restrictionFunction A hA) seed s =
      Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA
        j (Φ.query seed j) (CompactCube.realWeights s j) -
      ∫ x, Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA
        j (Φ.query seed j) x ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)) := by
  classical
  change Φ.privateAverageProjection J j (Φ.restrictionFunction A hA) seed s -
    Φ.weightProjection j (Φ.privateAverageProjection J j (Φ.restrictionFunction A hA)) seed s = _
  rw [Φ.privateAverageProjection_separator J frozen j seed ho,
    Φ.weightProjection_apply]
  simp_rw [Φ.privateAverageProjection_separator J frozen j seed ho,
    CompactCube.realWeights_update, Φ.outsideSum_update J frozen _ j,
    Function.update_self]
  congr 1
  exact CompactCube.integral_coe
    (Φ.ownMean_lipschitz J frozen _ A hA j (Φ.query seed j)).continuous.measurable.aestronglyMeasurable

theorem privateProjection_coordinate_variance (Φ : LabelCover) {d : ℕ}
    (J : Finset (Fin d)) (frozen : Φ.Seeds d) (j : J) (seed : Φ.Seeds d)
    (ho : ∀ e, e ∉ internalPairs J → frozen e = seed e)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.RestrictionWeights d) :
    (∫ x, (Φ.privateProjection J j (Φ.restrictionFunction A hA) seed
      (Function.update s j x))^2 ∂CompactCube.law (Fin (Φ.WeightDimension d))) =
      ProbabilityTheory.variance (Φ.ownMean J frozen
        (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA j (Φ.query seed j))
        (VertexCover.Cube.law (Fin (Φ.WeightDimension d))) := by
  classical
  simp_rw [Φ.privateProjection_separator J frozen j seed ho,
    CompactCube.realWeights_update, Φ.outsideSum_update J frozen _ j,
    Function.update_self]
  rw [ProbabilityTheory.variance_eq_integral
    (Φ.ownMean_lipschitz J frozen _ A hA j (Φ.query seed j)).continuous.measurable.aemeasurable]
  apply CompactCube.integral_coe (f := fun x =>
    (Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA j (Φ.query seed j) x -
      ∫ y, Φ.ownMean J frozen (Φ.outsideSum J frozen (CompactCube.realWeights s)) A hA j (Φ.query seed j) y
        ∂VertexCover.Cube.law (Fin (Φ.WeightDimension d)))^2)
  exact (((Φ.ownMean_lipschitz J frozen _ A hA j (Φ.query seed j)).continuous.sub
    continuous_const).pow 2).measurable.aestronglyMeasurable

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
