import OAI.Probability.InvariantIsing.Fields.FieldRootOrder
import OAI.Probability.InvariantIsing.Fields.FieldAffineScalarBridge

namespace OAI

/-! The adjacent and final height-variation families have the same
literal scalar transition lists used in the original finite field model. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldAdjacentAffineList (a b ζ η : ℝ) (L : List FieldAffineStep) : List FieldAffineStep :=
  ⟨a, 1, ζ⟩ :: ⟨b, -1, η⟩ :: L

lemma fieldAdjacentAffineList_positive (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) :
    ∀ av ∈ fieldAdjacentAffineList a b ζ η L, ∀ t ∈ Ioo (-a) b,
      0 < av.base + av.slope * t := by
  intro av hav t ht
  rcases List.mem_cons.mp hav with rfl | hav
  · change 0 < a + 1 * t
    linarith [ht.1]
  · rcases List.mem_cons.mp hav with rfl | hav
    · change 0 < b + (-1) * t
      linarith [ht.2]
    · rw [hs av hav, zero_mul, add_zero]
      exact hb av hav

lemma fieldAdjacentFamily_scalar (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) (t : ℝ) :
    (fun z => (fieldAdjacentFamily a b ζ η L hb hs).U (t, z)) =
      fieldScalarValue (fieldAffineIncrements (fieldAdjacentAffineList a b ζ η L) t)
        (fun z => Real.log (Real.cosh z)) := by
  let M := fieldAdjacentAffineList a b ζ η L
  let hM := fieldAdjacentAffineList_positive a b ζ η L hb hs
  have he : fieldAdjacentFamily a b ζ η L hb hs =
      fieldAffineFamily (Ioo (-a) b) isOpen_Ioo M hM := rfl
  rw [he, fieldAffineFamily_value]
  exact fieldAffineValue_scalar M t

lemma fieldAdjacentFamily_scalar_mean (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) (t : ℝ) :
    (fun z => (fieldAdjacentFamily a b ζ η L hb hs).X (t, z)) =
      fieldScalarMean (fieldAffineIncrements (fieldAdjacentAffineList a b ζ η L) t)
        (fun z => Real.log (Real.cosh z)) Real.tanh := by
  let M := fieldAdjacentAffineList a b ζ η L
  let hM := fieldAdjacentAffineList_positive a b ζ η L hb hs
  have he : fieldAdjacentFamily a b ζ η L hb hs =
      fieldAffineFamily (Ioo (-a) b) isOpen_Ioo M hM := rfl
  rw [he]
  exact fieldAffineFamily_mean (Ioo (-a) b) isOpen_Ioo M hM t

lemma fieldAdjacentAffineList_increments (a b ζ η : ℝ) (L : List FieldAffineStep) (t : ℝ) :
    fieldAffineIncrements (fieldAdjacentAffineList a b ζ η L) t =
      (ζ, Real.toNNReal (a + t)) :: (η, Real.toNNReal (b - t)) :: fieldAffineIncrements L t := by
  simp only [fieldAffineIncrements, fieldAdjacentAffineList, List.map_cons, one_mul,
    neg_one_mul, sub_eq_add_neg]

end InvariantIsing

end

end OAI
