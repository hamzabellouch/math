import OAI.NumberTheory.DirichletL.Reflection.OriginalCellBounds
import OAI.NumberTheory.DirichletL.Reflection.PoolArithmetic
import OAI.NumberTheory.DirichletL.Reflection.MarkedLevel
import OAI.NumberTheory.DirichletL.Reflection.ChoiceTransport
import OAI.NumberTheory.DirichletL.Reflection.TupleSectors

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma residual_level_coprime (K Q₀ : Ideal Eis) (hK : Admissible K)
    (c : Eis) (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) (hcop : IsCoprime Q₀ K) :
    IsCoprime (Ideal.span {(9:Eis)*c}) K := by
  rw [←PrimeFamily.residual_product K hK]
  apply IsCoprime.prod_right_iff.mpr
  intro i hi
  exact (PrimeFamily.residual K hK).level_coprime Q₀ c hc
    (fun i => hcop.of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK i)) i

lemma original_residual_completion_conditions (rows : Finset (Ideal Eis)) (J Q Q₀ : Ideal Eis)
    (hJ : J≠0) (hQ : Q≠0) (hrows : ∀ I∈rows,I≠0)
    (hbad : ∀ P∈fixedBadPrimes,P∣Q) (hperiod : Q₀∣Q)
    (A : Finset (FreeReflection.pool J Q Q₀)) (c : Eis)
    (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) :
    ∀ K∈originalResidualRows rows J Q,
      Admissible K ∧
      (∀ b : A,IsCoprime (((poolPrimeFamily J Q Q₀).restrict A).ideal b) K) ∧
      IsCoprime (Ideal.span {(9:Eis)*c}) K := by
  intro K hK
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp hK
  subst K
  obtain ⟨hi,hp,hm⟩ := Finset.mem_filter.mp hI
  have hk := rowResidualPart_admissible I Q hbad
  refine ⟨hk,?_,?_⟩
  · intro b
    exact poolPrimeFamily_fiber_row_coprime J I Q Q₀ hJ (hrows I hi) hQ hp.symm hm.symm b.val
  · apply residual_level_coprime _ Q₀ hk c hc
    exact (squarefreeResidualPart_coprime (rowSimplePart I) Q).symm.of_isCoprime_of_dvd_left hperiod

variable {φ σ : Type*} [Fintype σ] [DecidableEq σ]

theorem original_tuple_cell_conditions (Frozen : PrimeFamily φ)
    (hFrozen : Pairwise (Function.onFun IsCoprime Frozen.ideal))
    (L : σ→Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hsub : tuples⊆fixedSlotTupleSet L Frozen.ideal)
    (N : Eis) (hFN : ∀ b,IsCoprime (Ideal.span {N}) (Frozen.ideal b))
    (hFodd : ∀ b,ringChar (Eis⧸Frozen.ideal b)≠2)
    (hLN : ∀ i,∀ P∈L i,IsCoprime (Ideal.span {N}) P)
    (hLodd : ∀ i,∀ P∈L i,ringChar (Eis⧸P)≠2) :
    let S := tuplePrimeFamily tuples hne
      (fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1 i))
      (fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1 i))
    ∀ P∈tuples.image slotTupleProduct,
      (∏ i,(S P).ideal i)=P ∧
      Pairwise (Function.onFun IsCoprime (Frozen.sum (S P)).ideal) ∧
      (∀ b,IsCoprime (Ideal.span {N}) ((Frozen.sum (S P)).ideal b)) ∧
      (∀ b,ringChar (Eis⧸(Frozen.sum (S P)).ideal b)≠2) := by
  dsimp only
  let hm := fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1 i)
  let hg := fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1 i)
  have hs : ∀ p∈tuples,∀ i,p i∈L i := fun p hp => ((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1
  intro P hP
  refine ⟨tuplePrimeFamily_product tuples hne hm hg P hP,?_,?_,?_⟩
  · exact tuplePrimeFamily_sum_pairwise Frozen hFrozen L hL tuples hne hs hm hg
      (fun p hp => ((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).2) P
  · intro b
    cases b with
    | inl b => exact hFN b
    | inr b => exact hLN b _ (hs _ (tupleRepresentative_mem tuples hne P) b)
  · intro b
    cases b with
    | inl b => exact hFodd b
    | inr b => exact hLodd b _ (hs _ (tupleRepresentative_mem tuples hne P) b)

end
end SevenEighths.InverseReflectedPhase

end OAI
