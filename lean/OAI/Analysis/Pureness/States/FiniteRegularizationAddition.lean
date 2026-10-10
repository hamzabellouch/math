import OAI.Analysis.Pureness.Operators.FiniteDimensionRegularization

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma positiveProduct_cut {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (ε : ℝ≥0) (a b : Positive D) :
    Positive.cut ε (positiveProduct a b) = positiveProduct (Positive.cut ε a) (Positive.cut ε b) := by
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val (Positive.map_cut (NonUnitalStarAlgHom.fst ℂ D D) ε (positiveProduct a b))
  · exact congrArg Subtype.val (Positive.map_cut (NonUnitalStarAlgHom.snd ℂ D D) ε (positiveProduct a b))

lemma finitePositiveClass_cut_add (n : ℕ) (M N : Positive (FinMatrix A n)) (ε : ℝ≥0) :
    finitePositiveClass (n*2) (Positive.cut ε (Positive.map (matrixInterleave n) (positiveProduct M N))) =
      finitePositiveClass n (Positive.cut ε M) + finitePositiveClass n (Positive.cut ε N) := by
  rw [← Positive.map_cut, positiveProduct_cut, finitePositiveClass_add]

theorem finiteRegularizedValue_add (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) (n : ℕ) (M N : Positive (FinMatrix A n)) :
    finiteRegularizedValue d (n*2) (Positive.map (matrixInterleave n) (positiveProduct M N)) =
      finiteRegularizedValue d n M + finiteRegularizedValue d n N := by
  apply le_antisymm
  · apply iSup_le
    intro ε
    apply iSup_le
    intro hε
    rw [finitePositiveClass_cut_add, map_add]
    exact add_le_add (cut_class_value_le_regularized d n M ε hε)
      (cut_class_value_le_regularized d n N ε hε)
  · apply ENNReal.biSup_add_biSup_le' (show ∃ ε : ℝ≥0, 0 < ε from ⟨1,zero_lt_one⟩)
      (show ∃ ε : ℝ≥0, 0 < ε from ⟨1,zero_lt_one⟩)
    intro ε hε δ hδ
    apply le_iSup_of_le (min ε δ)
    apply le_iSup_of_le (lt_min hε hδ)
    rw [finitePositiveClass_cut_add, map_add]
    exact add_le_add (finiteCutValue_antitone d hd n M (min_le_left _ _))
      (finiteCutValue_antitone d hd n N (min_le_right _ _))

lemma finiteClass_has_representative (x : finiteCuntzSubmonoid (A := A)) :
    ∃ r : Σ n : ℕ, Positive (FinMatrix A n), finitePositiveClass r.1 r.2 = x := by
  obtain ⟨n,M,h⟩ := x.2
  exact ⟨⟨n,M⟩,Subtype.ext h.symm⟩

def finiteClassRepresentative (x : finiteCuntzSubmonoid (A := A)) :
    Σ n : ℕ, Positive (FinMatrix A n) := Classical.choose (finiteClass_has_representative x)

lemma finiteClassRepresentative_spec (x : finiteCuntzSubmonoid (A := A)) :
    finitePositiveClass (finiteClassRepresentative x).1 (finiteClassRepresentative x).2 = x :=
  Classical.choose_spec (finiteClass_has_representative x)

def finiteRegularizedFunction (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (x : finiteCuntzSubmonoid (A := A)) : ℝ≥0∞ :=
  finiteRegularizedValue d (finiteClassRepresentative x).1 (finiteClassRepresentative x).2

theorem finiteRegularizedFunction_eval (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) (n : ℕ) (M : Positive (FinMatrix A n)) :
    finiteRegularizedFunction d (finitePositiveClass n M) = finiteRegularizedValue d n M := by
  apply le_antisymm
  · exact finiteRegularizedValue_mono d hd _ _ (finiteClassRepresentative_spec _).le
  · exact finiteRegularizedValue_mono d hd _ _ (finiteClassRepresentative_spec _).ge

lemma finiteRegularizedFunction_monotone (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) : Monotone (finiteRegularizedFunction d) := by
  intro x y h
  exact finiteRegularizedValue_mono d hd _ _ (by simpa only [finiteClassRepresentative_spec] using h)

lemma finiteRegularizedFunction_add (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) (x y : finiteCuntzSubmonoid (A := A)) :
    finiteRegularizedFunction d (x+y) = finiteRegularizedFunction d x + finiteRegularizedFunction d y := by
  obtain ⟨⟨n,M⟩,rfl⟩ := finiteClass_has_representative x
  obtain ⟨⟨m,N⟩,rfl⟩ := finiteClass_has_representative y
  have hM := finitePositiveClass_inclusion (le_max_left n m) M
  have hN := finitePositiveClass_inclusion (le_max_right n m) N
  rw [← hM, ← hN, ← finitePositiveClass_add]
  simp only [finiteRegularizedFunction_eval d hd]
  exact finiteRegularizedValue_add d hd _ _ _

def regularizedFiniteDimension (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞ where
  toFun := finiteRegularizedFunction d
  map_zero' := by
    rw [← finitePositiveClass_zero (A := A) 0, finiteRegularizedFunction_eval d hd,
      finiteRegularizedValue_zero]
  map_add' := finiteRegularizedFunction_add d hd

theorem regularizedFiniteDimension_monotone (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (hd : Monotone d) : Monotone (regularizedFiniteDimension d hd) := finiteRegularizedFunction_monotone d hd
end CuntzPureness

end

end OAI
