import OAI.NumberTheory.DukePrimeDegree.Dynamics.TwoBlockParabolicChart
import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralCoordinateMeasure

namespace OAI

/-!
# The measure in an open neutral-subgroup chart

Only an open subgroup of the neutral group is used. Thus the chart applies
to the actual subgroup proved to preserve the measure, without imposing
invariance under disconnected components of the neutral centralizer.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology Classical

namespace DukePrimeDegree

instance twoBlockSL_measurableSpace (a b : ℕ) : MeasurableSpace (TwoBlockSL a b) :=
  borel (TwoBlockSL a b)

instance twoBlockSL_borelSpace (a b : ℕ) : BorelSpace (TwoBlockSL a b) := ⟨rfl⟩

instance twoBlockSL_secondCountable (a b : ℕ) : SecondCountableTopology (TwoBlockSL a b) := by
  let : SecondCountableTopology (Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ) :=
    inferInstanceAs (SecondCountableTopology ((Fin a ⊕ Fin b) → (Fin a ⊕ Fin b) → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology

abbrev TwoBlockTransverse (a b : ℕ) :=
  Matrix (Fin b) (Fin a) ℝ × Matrix (Fin a) (Fin b) ℝ

instance twoBlockTransverse_borelSpace (a b : ℕ) : BorelSpace (TwoBlockTransverse a b) :=
  inferInstanceAs (BorelSpace ((Fin b → Fin a → ℝ) × (Fin a → Fin b → ℝ)))

instance twoBlockTransverse_secondCountable (a b : ℕ) :
    SecondCountableTopology (TwoBlockTransverse a b) :=
  inferInstanceAs (SecondCountableTopology ((Fin b → Fin a → ℝ) × (Fin a → Fin b → ℝ)))

def twoBlockLocalNeutralParam {a b : ℕ} (H : Subgroup (twoBlockNeutralGroup a b))
    (z : TwoBlockTransverse a b × H) : TwoBlockSL a b :=
  twoBlockParabolicParam (z.1.1, z.1.2, z.2.val)

theorem twoBlockLocalNeutralParam_isOpenEmbedding {a b : ℕ}
    (H : Subgroup (twoBlockNeutralGroup a b))
    (hH : IsOpen (H : Set (twoBlockNeutralGroup a b))) :
    Topology.IsOpenEmbedding (twoBlockLocalNeutralParam H) := by
  have hi := (Topology.IsOpenEmbedding.id (X := TwoBlockTransverse a b)).prodMap
    hH.isOpenEmbedding_subtypeVal
  have ha := (Homeomorph.prodAssoc
    (Matrix (Fin b) (Fin a) ℝ) (Matrix (Fin a) (Fin b) ℝ)
    (twoBlockNeutralGroup a b)).isOpenEmbedding
  exact (twoBlockParabolicParam_isOpenEmbedding a b).comp (ha.comp hi)

theorem twoBlockLocalNeutralParam_right {a b : ℕ}
    (H : Subgroup (twoBlockNeutralGroup a b))
    (z : TwoBlockTransverse a b × H) (h : H) :
    twoBlockLocalNeutralParam H (z.1, z.2 * h) =
      twoBlockLocalNeutralParam H z * h.val.val :=
  twoBlockParabolicParam_right_neutral (z.1.1, z.1.2, z.2.val) h.val

def twoBlockLocalNeutralMeasure {a b : ℕ}
    (H : Subgroup (twoBlockNeutralGroup a b)) (ν : Measure (TwoBlockSL a b)) :
    Measure (TwoBlockTransverse a b × H) :=
  ν.comap (twoBlockLocalNeutralParam H)

theorem twoBlockLocalNeutralMeasure_finiteOnCompacts {a b : ℕ}
    (H : Subgroup (twoBlockNeutralGroup a b))
    (hH : IsOpen (H : Set (twoBlockNeutralGroup a b)))
    (ν : Measure (TwoBlockSL a b)) [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (twoBlockLocalNeutralMeasure H ν) :=
  IsFiniteMeasureOnCompacts.comap' _
    (twoBlockLocalNeutralParam_isOpenEmbedding H hH).continuous
    (twoBlockLocalNeutralParam_isOpenEmbedding H hH).measurableEmbedding

theorem twoBlockLocalNeutralMeasure_right_invariant {a b : ℕ}
    (H : Subgroup (twoBlockNeutralGroup a b))
    (hH : IsOpen (H : Set (twoBlockNeutralGroup a b)))
    (ν : Measure (TwoBlockSL a b)) (h : H)
    (hinv : ν.map (fun g => g * h.val.val) = ν) :
    (twoBlockLocalNeutralMeasure H ν).map (fun z => (z.1, z.2 * h)) =
      twoBlockLocalNeutralMeasure H ν := by
  let e := ((Homeomorph.refl (TwoBlockTransverse a b)).prodCongr
    (Homeomorph.mulRight h)).toMeasurableEquiv
  let g := (Homeomorph.mulRight h.val.val).toMeasurableEquiv
  exact comap_map_eq_of_equivariant ν (twoBlockLocalNeutralParam H)
    (twoBlockLocalNeutralParam_isOpenEmbedding H hH).measurableEmbedding e g
    (fun z => by
      change twoBlockLocalNeutralParam H (z.1, z.2 * h) =
        twoBlockLocalNeutralParam H z * h.val.val
      exact twoBlockLocalNeutralParam_right H z h) hinv

end DukePrimeDegree

end

end OAI
