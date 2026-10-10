import OAI.NumberTheory.TotientAsymptotic.CollisionCanceled

namespace OAI

/-! Exact block values and bounds for both surviving shifted-prime lists. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def witnessBlockValue {x : ℝ} {H : ℕ} (p : ℕ) (η : RemainderDatum (L x H)) (i k : ℕ) : ℕ :=
  (suffixPreimage η k).totient*∏ j ∈ Finset.Icc i k, (wholeWitnessPrime p η j-1)

lemma witnessBlockValue_zero {x : ℝ} {H k p : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hL : L x H < m x) (hR : R x H < L x H) (hk : k < L x H) :
    witnessBlockValue p η 0 k=tupleValue (witnessTuple p η) :=
  (witness_tuple_value_at_cut hη hL hR hk).symm

lemma witnessBlockValue_positive {x : ℝ} {H i k p : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hL : L x H < m x) (hi : 1 ≤ i)
    (hik : i ≤ k) (hk : k < L x H) :
    witnessBlockValue p η i k=(remainderPrime η i-1)*(suffixPreimage η i).totient := by
  have hp : (∏ j ∈ Finset.Icc i k, (wholeWitnessPrime p η j-1)) =
      ∏ j ∈ Finset.Icc i k, (remainderPrime η j-1) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [wholeWitnessPrime,ite_eq_right (by have := (Finset.mem_Icc.mp hj).1; omega : j ≠ 0)]
  have he : Finset.Icc i k=insert i (Finset.Icc (i+1) k) := by
    ext j
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  rw [witnessBlockValue,hp,he,Finset.prod_insert (by simp)]
  rw [basic_suffix_totient_split hη hL hik hk]
  ring

/-- A dyadic bound on the full block bounds every surviving shift on either
side, after cancellation and with both residual factors retained. -/
theorem surviving_shift_le_block {x y : ℝ} {H i k p q : ℕ}
    {η ξ : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hξ : IsBasicRemainder x H ξ) (hp : p.Prime)
    (hL : L x H < m x) (hR : R x H < L x H) (hk : k < L x H) (hik : i ≤ k)
    (hv : tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ))
    (hfirst : wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i)
    (hcommon : ∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j)
    (hsize : (witnessBlockValue p η i k : ℝ) ≤ y) :
    ∀ r : Fin (collisionSurvivors p q η ξ i k).card,
      ((survivingPair p q η ξ i k).left r-1 : ℕ) ≤ y ∧
      ((survivingPair p q η ξ i k).right r-1 : ℕ) ≤ y := by
  have heq := surviving_collision_identity hη hξ hp hL hR hk hik hv hfirst hcommon
  have hrpos := collisionCanceledProduct_pos hη hp hk.le (q := q) (ξ := ξ) (i := i)
  have hDpos := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := k))
  have hprodpos : 0 < (suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left := by
    apply Nat.mul_pos hDpos
    apply Finset.prod_pos
    intro r _
    have hj := (Finset.mem_filter.mp (survivingIndex_mem p q η ξ i k r)).1
    have hjk := (Finset.mem_Icc.mp hj).2
    change 0 < wholeWitnessPrime p η (survivingIndex p q η ξ i k r)-1
    by_cases hz : survivingIndex p q η ξ i k r=0
    · simpa only [wholeWitnessPrime,hz,ite_true] using Nat.sub_pos_of_lt hp.one_lt
    · simp only [wholeWitnessPrime,ite_eq_right hz]
      exact Nat.sub_pos_of_lt (hη.2.1 _ (Finset.mem_Icc.mpr ⟨by omega,hjk.trans hk.le⟩)).1.one_lt
  have hfactor : collisionCanceledProduct p q η ξ i k*
      ((suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left)=
      witnessBlockValue p η i k := by
    rw [mul_left_comm,canceled_surviving_product]
    rfl
  have hnat : (suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left ≤
      witnessBlockValue p η i k := by
    rw [← hfactor]
    exact Nat.le_mul_of_pos_left _ hrpos
  have hle : (((suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left : ℕ) : ℝ) ≤ y :=
    (show (((suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left : ℕ) : ℝ) ≤
      witnessBlockValue p η i k by exact_mod_cast hnat).trans hsize
  intro r
  constructor
  · exact (show (((survivingPair p q η ξ i k).left r-1 : ℕ) : ℝ) ≤
      (((suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left : ℕ) : ℝ) by
        exact_mod_cast Nat.le_of_dvd hprodpos ((shifted_factor_dvd _ r).trans (dvd_mul_left _ _))).trans hle
  · rw [heq] at hprodpos hle
    exact (show (((survivingPair p q η ξ i k).right r-1 : ℕ) : ℝ) ≤
      (((survivingPair p q η ξ i k).remainder*shiftedProduct (survivingPair p q η ξ i k).right : ℕ) : ℝ) by
        exact_mod_cast Nat.le_of_dvd hprodpos ((shifted_factor_dvd _ r).trans (dvd_mul_left _ _))).trans hle

end TotientAsymptotic

end

end OAI
