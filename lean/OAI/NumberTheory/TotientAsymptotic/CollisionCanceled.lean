import OAI.NumberTheory.TotientAsymptotic.SurvivingCollision
import OAI.NumberTheory.TotientAsymptotic.CollisionDyadicSize

namespace OAI

/-! The canceled product and the residual integer satisfy Ford's size bounds. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def collisionCanceledProduct {x : ℝ} {H : ℕ} (p q : ℕ)
    (η ξ : RemainderDatum (L x H)) (i k : ℕ) : ℕ :=
  ∏ j ∈ (Finset.Icc i k).filter (fun j => wholeWitnessPrime p η j=wholeWitnessPrime q ξ j),
    (wholeWitnessPrime p η j-1)

lemma canceled_surviving_product {x : ℝ} {H i k p q : ℕ}
    (η ξ : RemainderDatum (L x H)) :
    collisionCanceledProduct p q η ξ i k *
      shiftedProduct (survivingPair p q η ξ i k).left =
        ∏ j ∈ Finset.Icc i k, (wholeWitnessPrime p η j-1) := by
  unfold shiftedProduct
  change collisionCanceledProduct p q η ξ i k *
    (∏ j : Fin (collisionSurvivors p q η ξ i k).card,
      (wholeWitnessPrime p η (survivingIndex p q η ξ i k j)-1)) = _
  rw [prod_survivingIndex p q η ξ i k (fun j => wholeWitnessPrime p η j-1)]
  exact Finset.prod_filter_mul_prod_filter_not (Finset.Icc i k)
    (fun j => wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) _

lemma collisionCanceledProduct_pos {x : ℝ} {H i k p q : ℕ}
    {η ξ : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hp : p.Prime) (hk : k ≤ L x H) : 0 < collisionCanceledProduct p q η ξ i k := by
  apply Finset.prod_pos
  intro j hj
  obtain ⟨hji,_⟩ := Finset.mem_filter.mp hj
  by_cases hj0 : j=0
  · simp only [wholeWitnessPrime,hj0,ite_true]
    exact Nat.sub_pos_of_lt hp.one_lt
  · simp only [wholeWitnessPrime,ite_eq_right hj0]
    exact Nat.sub_pos_of_lt (hη.2.1 j (Finset.mem_Icc.mpr
      ⟨by omega,(Finset.mem_Icc.mp hji).2.trans hk⟩)).1.one_lt

lemma collisionCanceledProduct_le_suffix {x : ℝ} {H i k p q : ℕ}
    {η ξ : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hk : k ≤ L x H)
    (hfirst : wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i) :
    collisionCanceledProduct p q η ξ i k ≤ suffixPreimage η i := by
  let I := (Finset.Icc i k).filter (fun j => wholeWitnessPrime p η j=wholeWitnessPrime q ξ j)
  have hsub : I ⊆ Finset.Icc (i+1) (L x H) := by
    intro j hj
    obtain ⟨hj,he⟩ := Finset.mem_filter.mp hj
    have hji := Finset.mem_Icc.mp hj
    have hne : j ≠ i := by intro hh; subst j; exact hfirst he
    exact Finset.mem_Icc.mpr ⟨by omega,hji.2.trans hk⟩
  have hle : collisionCanceledProduct p q η ξ i k ≤ ∏ j ∈ I, remainderPrime η j := by
    apply Finset.prod_le_prod
    intro j hj
    have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp (hsub hj)).1; omega
    simpa only [wholeWitnessPrime,ite_eq_right hj0] using Nat.sub_le (remainderPrime η j) 1
  have hrest : (∏ j ∈ I, remainderPrime η j) ≤ ∏ j ∈ Finset.Icc (i+1) (L x H), remainderPrime η j := by
    apply Finset.prod_le_prod_of_subset_of_one_le hsub
    intro j hj _
    exact (hη.2.1 j (Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hj).1; omega,(Finset.mem_Icc.mp hj).2⟩)).1.pos
  exact (hle.trans hrest).trans (Nat.le_mul_of_pos_left _ hη.1)

lemma small_suffix_factor_size {p n N : ℕ} {y : ℝ} (hp : 3 ≤ p)
    (hn : 0 < n) (hnN : n ≤ N) (hy : ((p-1 : ℕ) : ℝ) ≤ y)
    (hsmall : Real.log (N : ℝ) ≤ (1/1000 : ℝ)*Real.log p) :
    (n : ℝ) ≤ y^(1/100 : ℝ) := by
  have hp1 : (1 : ℝ) < (p-1 : ℕ) := by exact_mod_cast (show 2 ≤ p-1 by omega)
  have hy1 : 1 < y := hp1.trans_le hy
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpbound : p ≤ (p-1)^2 := by
    have he : p-1+1=p := by omega
    have hh : 2 ≤ p-1 := by omega
    nlinarith
  have hl := Real.log_le_log hp0 (show (p : ℝ) ≤ ((p-1 : ℕ) : ℝ)^2 by exact_mod_cast hpbound)
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hly := Real.log_le_log (zero_lt_one.trans hp1) hy
  have hln := Real.log_le_log (by exact_mod_cast hn : (0 : ℝ) < n)
    (show (n : ℝ) ≤ N by exact_mod_cast hnN)
  apply (Real.log_le_log_iff (by exact_mod_cast hn : (0 : ℝ) < n)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hy1) _)).mp
  rw [Real.log_rpow (zero_lt_one.trans hy1)]
  linarith [Real.log_pos hy1]

/-- Both the fixed residual totient and the product of canceled shifts are
small enough for the original published Ford lemma. No new counting input is
used for these hypotheses. -/
theorem collision_small_factors : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i k p q : ℕ, 1 ≤ i → i ≤ R x H → i+2 ≤ L x H → L x H < m x →
    i ≤ k → k < L x H → ∀ η ξ : RemainderDatum (L x H),
    IsBasicRemainder x H η → 3 ≤ remainderPrime η i →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i → ∀ y : ℝ,
    ((remainderPrime η i-1 : ℕ) : ℝ) ≤ y →
    ((suffixPreimage η k).totient : ℝ) ≤ y^(1/100 : ℝ) ∧
    (collisionCanceledProduct p q η ξ i k : ℝ) ≤ y^(1/100 : ℝ) := by
  filter_upwards [collision_tail_log_small] with H hH
  filter_upwards [hH] with x hx
  intro i k p q hi hiR hiL hL hik hk η ξ hη hp hfirst y hy
  have ht := hx i hi hiR hiL hL η hη
  have hDpos := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := k))
  have hDdvd : (suffixPreimage η k).totient ∣ (suffixPreimage η i).totient := by
    rw [basic_suffix_totient_split hη hL hik hk]
    exact dvd_mul_right _ _
  have hDle := (Nat.le_of_dvd (Nat.totient_pos.mpr (suffixPreimage_pos hη)) hDdvd).trans
    (Nat.totient_le (suffixPreimage η i))
  refine ⟨small_suffix_factor_size hp hDpos hDle hy ht,?_⟩
  have hrpos : 0 < collisionCanceledProduct p q η ξ i k := by
    apply Finset.prod_pos
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).1
    have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj').1; omega
    simp only [wholeWitnessPrime,ite_eq_right hj0]
    exact Nat.sub_pos_of_lt (hη.2.1 j (Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hj').1; omega,(Finset.mem_Icc.mp hj').2.trans hk.le⟩)).1.one_lt
  exact small_suffix_factor_size hp hrpos (collisionCanceledProduct_le_suffix hη hk.le hfirst) hy ht

end TotientAsymptotic

end

end OAI
