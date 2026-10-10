import OAI.Combinatorics.Progressions.Lattices.WeightedTranslationCentralLattice

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem centralRealLine_periodic
    (x : (weightedTranslationNilmanifold w d hw hwd).Space) :
    Function.Periodic (fun t => centralRealLine w d hw hd hwd t • x) 1 := by
  intro t
  simpa only [Int.cast_one] using centralRealLine_add_int_smul w d hw hd hwd t 1 x

noncomputable def centralCircleAct (t : CircleFourier.Circle)
    (x : (weightedTranslationNilmanifold w d hw hwd).Space) :
    (weightedTranslationNilmanifold w d hw hwd).Space :=
  CircleFourier.periodicFlowAct (fun r x => centralRealLine w d hw hd hwd r • x)
    (centralRealLine_periodic w d hw hd hwd) t x

@[simp] theorem centralCircleAct_coe (t : ℝ)
    (x : (weightedTranslationNilmanifold w d hw hwd).Space) :
    centralCircleAct w d hw hd hwd (t : CircleFourier.Circle) x =
      centralRealLine w d hw hd hwd t • x :=
  CircleFourier.periodicFlowAct_coe _ _ t x

@[simp] theorem centralCircleAct_zero
    (x : (weightedTranslationNilmanifold w d hw hwd).Space) :
    centralCircleAct w d hw hd hwd 0 x = x := by
  apply CircleFourier.periodicFlowAct_zero
  intro y
  rw [centralRealLine_zero, one_smul]

theorem centralCircleAct_add (t u : CircleFourier.Circle)
    (x : (weightedTranslationNilmanifold w d hw hwd).Space) :
    centralCircleAct w d hw hd hwd (t + u) x =
      centralCircleAct w d hw hd hwd t (centralCircleAct w d hw hd hwd u x) := by
  apply CircleFourier.periodicFlowAct_add
  intro r s y
  rw [centralRealLine_add, mul_smul]

@[instance_reducible] noncomputable def centralCircleAddAction :
    AddAction CircleFourier.Circle (weightedTranslationNilmanifold w d hw hwd).Space where
  vadd := centralCircleAct w d hw hd hwd
  zero_vadd := centralCircleAct_zero w d hw hd hwd
  add_vadd := centralCircleAct_add w d hw hd hwd

end Erdos3.PolynomialTranslationLie

end

end OAI
