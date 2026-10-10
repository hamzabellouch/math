import OAI.Probability.InvariantIsing.Fields.FieldSpatialParameterOrder
import OAI.Probability.InvariantIsing.Fields.FieldTangentOrder
import OAI.Probability.InvariantIsing.Fields.FieldAffineShape

namespace OAI

/-! The actual internal-height comparison in `fld:mixed`. The fixed
tail is the finite log-cosh recursion. Increasing one height adds its
parameter to one variance and subtracts it from the next variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldAdjacentTail (a b : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) :
    FieldSmoothFamily (Ioo (-a) b) :=
  fieldAffineFamily (Ioo (-a) b) isOpen_Ioo L (fun av hav _ _ => by
    rw [hs av hav, zero_mul, add_zero]
    exact hb av hav)

def fieldAdjacentInner (a b η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) :
    FieldSmoothFamily (Ioo (-a) b) :=
  (fieldAdjacentTail a b L hb hs).transform isOpen_Ioo b (-1) η (fun t ht => by
    have h := ht.2
    linarith)

def fieldAdjacentFamily (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) :
    FieldSmoothFamily (Ioo (-a) b) :=
  (fieldAdjacentInner a b η L hb hs).transform isOpen_Ioo a 1 ζ (fun t ht => by
    have h := ht.1
    linarith)

lemma fieldAdjacentTail_stationary (a b : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) (p : ℝ × ℝ) :
    (fieldAdjacentTail a b L hb hs).T p = 0 :=
  fieldAffineFamily_stationary (Ioo (-a) b) isOpen_Ioo L _ hs p

lemma fieldAdjacentInner_shape (a b η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0)
    (hη : 0 < η) (hζ : ∀ av ∈ L, 0 < av.exponent) (t : ℝ) :
    let G := fieldAdjacentInner a b η L hb hs
    Function.Even (fun z => G.U (t, z)) ∧
    Function.Odd (fun z => G.X (t, z)) ∧
    MonotoneOn (fun z => G.X (t, z)) (Ici 0) ∧
    (∀ z ∈ Ici (0 : ℝ), 0 ≤ G.X (t, z)) ∧ (∀ z, |G.X (t, z)| ≤ 1) := by
  let av : FieldAffineStep := ⟨b, -1, η⟩
  have hv : ∀ v ∈ av :: L, ∀ q ∈ Ioo (-a) b, 0 < v.base + v.slope * q := by
    intro v hv q hq
    rcases List.mem_cons.mp hv with rfl | hv
    · dsimp only [av]
      linarith [hq.2]
    · rw [hs v hv, zero_mul, add_zero]
      exact hb v hv
  have he : ∀ v ∈ av :: L, 0 < v.exponent := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hη
    · exact hζ v hv
  change Function.Even (fun z => (fieldAffineFamily (Ioo (-a) b) isOpen_Ioo (av :: L) hv).U (t, z)) ∧ _
  exact fieldAffineFamily_shape (Ioo (-a) b) isOpen_Ioo (av :: L) hv he t

lemma fieldAdjacentFamily_shape (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0)
    (hζ : 0 < ζ) (hη : 0 < η) (htail : ∀ av ∈ L, 0 < av.exponent) (t : ℝ) :
    let G := fieldAdjacentFamily a b ζ η L hb hs
    Function.Even (fun z => G.U (t, z)) ∧
    Function.Odd (fun z => G.X (t, z)) ∧
    MonotoneOn (fun z => G.X (t, z)) (Ici 0) ∧
    (∀ z ∈ Ici (0 : ℝ), 0 ≤ G.X (t, z)) ∧ (∀ z, |G.X (t, z)| ≤ 1) := by
  let av : FieldAffineStep := ⟨a, 1, ζ⟩
  let bv : FieldAffineStep := ⟨b, -1, η⟩
  have hv : ∀ v ∈ av :: bv :: L, ∀ q ∈ Ioo (-a) b, 0 < v.base + v.slope * q := by
    intro v hv q hq
    rcases List.mem_cons.mp hv with rfl | hv
    · dsimp only [av]
      linarith [hq.1]
    · rcases List.mem_cons.mp hv with rfl | hv
      · dsimp only [bv]
        linarith [hq.2]
      · rw [hs v hv, zero_mul, add_zero]
        exact hb v hv
  have he : ∀ v ∈ av :: bv :: L, 0 < v.exponent := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hζ
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact hη
      · exact htail v hv
  change Function.Even (fun z => (fieldAffineFamily (Ioo (-a) b) isOpen_Ioo (av :: bv :: L) hv).U (t, z)) ∧ _
  exact fieldAffineFamily_shape (Ioo (-a) b) isOpen_Ioo (av :: bv :: L) hv he t

theorem fieldAdjacentFamily_tangent_antitone (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0)
    (hη : 0 < η) (hζη : ζ ≤ η) (htail : ∀ av ∈ L, 0 < av.exponent)
    {t : ℝ} (ht : t ∈ Ioo (-a) b) :
    AntitoneOn (fun z => (fieldAdjacentFamily a b ζ η L hb hs).T (t, z)) (Ici 0) := by
  let F := fieldAdjacentTail a b L hb hs
  let G := fieldAdjacentInner a b η L hb hs
  have hg := fieldAdjacentInner_shape a b η L hb hs hη htail t
  have hU : Measurable (fun z => G.U (t, z)) := G.mU.comp (by fun_prop)
  have hX : Measurable (fun z => G.X (t, z)) := G.mX.comp (by fun_prop)
  have hshape := field_negative_square_average_shape (a + t) ζ ((η - ζ) / 2)
    (by linarith) hU hg.1 (G.growth t) hX hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2
  have heq : (fun z => (fieldAdjacentFamily a b ζ η L hb hs).T (t, z)) =
      (fun z => -((η - ζ) / 2) * gaussianTiltAverage (a + t) ζ
        (fun y => G.U (t, y)) (fun y => (G.X (t, y)) ^ 2) z) := by
    funext z
    have h := F.adjacent_tangent isOpen_Ioo a b ζ η
      (fun q hq => by linarith [hq.1]) (fun q hq => by linarith [hq.2])
      (p := (t, z)) ht (fun y => fieldAdjacentTail_stationary a b L hb hs (t, y))
    simpa only [F, G, fieldAdjacentFamily, fieldAdjacentInner, neg_div] using h
  rw [heq]
  exact hshape.2

theorem fieldAdjacent_earlier_squares_antitone (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0)
    (hζ : 0 < ζ) (hζη : ζ ≤ η) (htail : ∀ av ∈ L, 0 < av.exponent)
    (P : List (ℝ × ℝ≥0)) (hP : ∀ av ∈ P, 0 < av.1)
    {t s : ℝ} (ht : t ∈ Ioo (-a) b) (hss : s ∈ Ioo (-a) b) (hts : t ≤ s) :
    let G := fieldAdjacentFamily a b ζ η L hb hs
    ∀ i z, fieldScalarSquares P (fun y => G.U (s, y)) (fun y => G.X (s, y)) i z ≤
      fieldScalarSquares P (fun y => G.U (t, y)) (fun y => G.X (t, y)) i z := by
  have hη : 0 < η := lt_of_lt_of_le hζ hζη
  let G := fieldAdjacentFamily a b ζ η L hb hs
  have hshape (q : ℝ) := fieldAdjacentFamily_shape a b ζ η L hb hs hζ hη htail q
  exact G.earlier_squares_antitone_parameter (convex_Ioo (-a) b)
    (fun q hq => fieldAdjacentFamily_tangent_antitone a b ζ η L hb hs hη hζη htail hq)
    (fun q _ => (hshape q).1) (fun q _ => (hshape q).2.1)
    (fun q _ => (hshape q).2.2.1) (fun q _ => (hshape q).2.2.2.1)
    (fun p => (hshape p.1).2.2.2.2 p.2) P hP ht hss hts

end InvariantIsing

end

end OAI
