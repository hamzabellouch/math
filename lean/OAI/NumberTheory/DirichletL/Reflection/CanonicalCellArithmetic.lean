import OAI.NumberTheory.DirichletL.Reflection.CellArithmetic
import OAI.NumberTheory.DirichletL.Reflection.OriginalRetainedSlots

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma canonical_retained_slot_not_excluded {α σ : Type*} [Fintype σ]
    (tuples : Finset α) (S : α→PrimeFamily σ) (q : ℕ) (m : Eis)
    (p : α) (hp : p∈punctureRetainedTuples tuples S (ActualFiber.maskElement q m)) (i : σ) :
    (S p).ideal i∉reflectionExcludedPrimes q := by
  intro hi
  have hm : ActualFiber.maskElement q m∈(S p).ideal i :=
    Ideal.mul_mem_left _ m (excludedGenerator_mem _ hi)
  exact (Finset.mem_filter.mp hp).2 i hm

lemma canonical_retained_slot_free_period {α σ : Type*} [Fintype σ]
    (tuples : Finset α) (S : α→PrimeFamily σ) (q : ℕ) (hq : q≠0) (m : Eis)
    (p : α) (hp : p∈punctureRetainedTuples tuples S (ActualFiber.maskElement q m)) (i : σ) :
    IsCoprime (ActualFiber.freeConductor q) ((S p).ideal i) := by
  have hc := reflectionConductor_coprime_of_not_excluded q hq ((S p).ideal i)
    (canonical_retained_slot_not_excluded tuples S q m p hp i)
  rw [reflectionConductor_ideal] at hc
  exact hc.of_isCoprime_of_dvd_left (dvd_mul_left _ (Ideal.span {(9:Eis)}))

lemma canonical_retained_marked_period {α σ : Type*} [Fintype σ]
    (q : ℕ) (hq : q≠0) (m f z : Eis) (D : GoodMaskRowData (ActualFiber.maskElement q m) f z)
    (tuples : Finset α) (S : α→PrimeFamily σ)
    (p : α) (hp : p∈punctureRetainedTuples tuples S (ActualFiber.maskElement q m)) :
    ∀ i,IsCoprime (Ideal.span {(9:Eis)*reflectionConductor q})
      ((markedRowFamily D (S p) (CanonicalCoefficientClass.fixedBaseConductor q)).ideal i) := by
  exact markedRowFamily_period D (S p) (CanonicalCoefficientClass.fixedBaseConductor q)
    (fun i => canonical_retained_slot_free_period tuples S q hq m p hp i)
    (reflectionConductor q) (reflectionConductor_ideal q)

theorem canonical_original_cell_conditions (q : ℕ) (hq : q≠0) (m : Eis) (hm : m≠0)
    (rows : Finset (Ideal Eis)) (J F : Ideal Eis) (hJ : J≠0) (hF : F≠0)
    (hrows : ∀ I∈rows,I≠0)
    (A : Finset (FreeReflection.pool J (ActualFiber.maskIdeal q m F) (ActualFiber.freeConductor q))) :
    ∀ K∈originalResidualRows rows J (ActualFiber.maskIdeal q m F),
      Admissible K ∧
      (∀ b : A,IsCoprime (((poolPrimeFamily J (ActualFiber.maskIdeal q m F)
        (ActualFiber.freeConductor q)).restrict A).ideal b) K) ∧
      IsCoprime (Ideal.span {(9:Eis)*reflectionConductor q}) K := by
  intro K hK
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp hK
  subst K
  obtain ⟨hi,hp,hmask⟩ := Finset.mem_filter.mp hI
  have hk := rowResidualPart_admissible I _ (ActualFiber.mask_bad q m F)
  refine ⟨hk,?_,?_⟩
  · intro b
    exact poolPrimeFamily_fiber_row_coprime J I _ _ hJ (hrows I hi)
      (ActualFiber.maskIdeal_ne_zero q m hm F hF) hp.symm hmask.symm b.val
  · exact residual_level_coprime _ (ActualFiber.freeConductor q) hk (reflectionConductor q)
      (reflectionConductor_ideal q) (residual_coprime_free_base q hq m F I)

end
end SevenEighths.InverseReflectedPhase

end OAI
