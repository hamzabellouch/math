import OAI.InformationTheory.Entanglement.HilbertCoarsegrain

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory InnerProductSpace ComplexOrder
open MeasureTheory ContinuousLinearMap
namespace SecretKey
variable {T : Type*} [MeasurableSpace T]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι a : Type*} [Fintype a] [DecidableEq a]

def uniformKeyLaw (b : HilbertBasis ι ℂ H) (σ : PositiveHilbertMeasure T H b) :
    (a×a)→PositiveHilbertMeasure T H b := fun p =>
  σ.scale (if p.1=p.2 then (Fintype.card a : ℝ)⁻¹ else 0) (by
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · rfl)
lemma uniformKeyLaw_value (b : HilbertBasis ι ℂ H) (σ : PositiveHilbertMeasure T H b)
    (p : a×a) (s : Set T) :
    (uniformKeyLaw b σ p).value s=
      if p.1=p.2 then ((Fintype.card a : ℂ)⁻¹) • σ.value s else 0 := by
  simp only [uniformKeyLaw,PositiveHilbertMeasure.scale_value]
  split_ifs <;> simp
omit [DecidableEq a] in
lemma firstBitPush_value (b : HilbertBasis ι ℂ H)
    (W : ((Fin 2×a)×(Fin 2×a))→PositiveHilbertMeasure T H b) (i j : Fin 2) (s : Set T) :
    (localClassicalPush b Prod.fst Prod.fst W (i,j)).value s=
      ∑ x : a, ∑ y : a, (W ((i,x),(j,y))).value s := by
  simp only [localClassicalPush,classicalPush_value,Finset.sum_filter,Fintype.sum_prod_type,
    Prod.map_apply,Prod.mk.injEq]
  fin_cases i <;> fin_cases j <;> simp
lemma firstBitPush_ideal_value [Nonempty a] (b : HilbertBasis ι ℂ H)
    (σ : PositiveHilbertMeasure T H b) (i j : Fin 2) (s : Set T) :
    (localClassicalPush b Prod.fst Prod.fst (uniformKeyLaw b σ (a := Fin 2×a)) (i,j)).value s=
      hilbertIdeal σ.value i j s := by
  rw [firstBitPush_value]
  simp only [uniformKeyLaw_value,Prod.mk.injEq,Fintype.card_prod,Fintype.card_fin]
  by_cases hij : i=j
  · simp only [hij,true_and,Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,
      hilbertIdeal]
    rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
    congr 1
    have hn : (Fintype.card a : ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
    push_cast
    field_simp
  · simp [hij,hilbertIdeal]

theorem first_bit_contract [Nonempty a] (b : HilbertBasis ι ℂ H)
    (W : ((Fin 2×a)×(Fin 2×a))→PositiveHilbertMeasure T H b)
    (σ : PositiveHilbertMeasure T H b) :
    hilbertCQDistance b (fun i j => localClassicalPush b Prod.fst Prod.fst W (i,j)) σ≤
      hilbertClassicalDistance b W (uniformKeyLaw b σ) := by
  have h := classicalPush_contract b (Prod.map Prod.fst Prod.fst) W (uniformKeyLaw b σ)
  apply le_trans ?_ h
  apply le_of_eq
  simp only [hilbertCQDistance,hilbertClassicalDistance,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply hilbertVariation_congr
  intro s hs
  change _ = (localClassicalPush b Prod.fst Prod.fst W (i,j)).value s -
    (localClassicalPush b Prod.fst Prod.fst (uniformKeyLaw b σ) (i,j)).value s
  rw [firstBitPush_ideal_value]

end SecretKey

end

end OAI
