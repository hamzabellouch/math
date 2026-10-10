import OAI.NumberTheory.TotientAsymptotic.CollisionCanceled
import OAI.NumberTheory.TotientAsymptotic.ComparisonLargePart

namespace OAI

/-! Assemble Ford's pointwise comparison hypotheses for actual surviving lists. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma normal_prime_omega_below {S y : ℝ} {p : ℕ} (hp : IsNormalPrime S p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSy : S ≤ y) (hpy : (p-1 : ℕ) ≤ y) :
    ((p-1).primeFactorsList.length : ℝ) ≤ 4*B y := by
  have hSb : B S ≤ B y := Real.log_le_log (Real.log_pos hS)
    (Real.log_le_log (zero_lt_one.trans hS) hSy)
  have hBy := hBS.trans hSb
  by_cases hp3 : 3 ≤ p
  · have hp1 : (1 : ℝ) < (p-1 : ℕ) := by exact_mod_cast (show 2 ≤ p-1 by omega)
    have hpb : B (p-1 : ℕ) ≤ B y := Real.log_le_log (Real.log_pos hp1)
      (Real.log_le_log (zero_lt_one.trans hp1) hpy)
    exact (normality_total_uniform hp hS hBS hSb hpb).trans (by linarith)
  · have he : p=2 := by have := hp.1.two_le; omega
    simp only [he, Nat.reduceSub, Nat.primeFactorsList_one, List.length_nil, Nat.cast_zero]
    positivity

/-- All pointwise hypotheses, including the large-prime-part condition, follow
for the actual canceled lists once their ordered factor intervals are chosen.
The remaining interval construction and summation are separate obligations. -/
theorem surviving_comparison_conditions : ∀ᶠ y : ℝ in atTop,
    ∀ {x : ℝ} {H i p q : ℕ} {η ξ : RemainderDatum (L x H)},
    IsBasicRemainder x H η → IsBasicRemainder x H ξ → p.Prime →
    L x H < m x → R x H < L x H → i ≤ R x H → collisionLastIndex x i < L x H →
    tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ) →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i →
    (∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ →
    ∀ Y U : ℕ → ℝ,
    1 < normalityScale x i → 0 ≤ B (normalityScale x i) → normalityScale x i ≤ y →
    Y (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card=collisionSmoothCutoff x i →
    (∀ j : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      U j ≤ largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left j-1) ∧
      (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left j-1) : ℝ) ≤ Y j ∧
      U j ≤ largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right j-1) ∧
      (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right j-1) : ℝ) ≤ Y j) →
    ((suffixPreimage η (collisionLastIndex x i)).totient *
      (∏ j ∈ Finset.Icc i (collisionLastIndex x i), (wholeWitnessPrime p η j-1)) : ℕ) ≤ y →
    (largestPrimeFactor (collisionResidual ξ i) : ℝ) ≤ collisionSmoothCutoff x i →
    y^(9/10 : ℝ) ≤ wholeWitnessPrime p η i → 1 ≤ Y 1 →
    Y 1 ≤ Real.exp (Real.exp ((4/5 : ℝ)*B y)) →
    FordComparisonConditions (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
      y (normalityScale x i) (collisionResidual η i)
      (collisionCanceledProduct p q η ξ i (collisionLastIndex x i)) Y U
      (survivingPair p q η ξ i (collisionLastIndex x i)) := by
  filter_upwards [comparison_large_prime_part] with y hlarge
  intro x H i p q η ξ hη hξ hp hL hR hi hk hv hfirst hcommon hgη hgξ Y U hS hBS hSy hYb hinterval hsize hres hhead hY1 hY1u
  have hik : i ≤ collisionLastIndex x i := Nat.le_add_right _ _
  have heq := surviving_collision_identity hη hξ hp hL hR hk hik hv hfirst hcommon
  have hgood := surviving_good_conditions hi hgη hgξ
  have hrpos := collisionCanceledProduct_pos hη hp hk.le (q := q) (ξ := ξ) (i := i)
  have hDpos := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := collisionLastIndex x i))
  have hrempos := Nat.totient_pos.mpr (suffixPreimage_pos hξ (i := collisionLastIndex x i))
  have hprodpos : 0 < (collisionResidual η i)*
      shiftedProduct (survivingPair p q η ξ i (collisionLastIndex x i)).left := by
    apply Nat.mul_pos hDpos
    apply Finset.prod_pos
    intro j _
    exact Nat.sub_pos_of_lt (hgood j).1.1.one_lt
  have hfactor : collisionCanceledProduct p q η ξ i (collisionLastIndex x i) *
      ((collisionResidual η i)*shiftedProduct (survivingPair p q η ξ i (collisionLastIndex x i)).left) =
      (collisionResidual η i)*∏ j ∈ Finset.Icc i (collisionLastIndex x i), (wholeWitnessPrime p η j-1) := by
    rw [mul_left_comm, canceled_surviving_product]
  have hprodsize : ((collisionResidual η i)*shiftedProduct
      (survivingPair p q η ξ i (collisionLastIndex x i)).left : ℕ) ≤ y := by
    have hh := Nat.le_mul_of_pos_left
      ((collisionResidual η i)*shiftedProduct (survivingPair p q η ξ i (collisionLastIndex x i)).left) hrpos
    rw [hfactor] at hh
    exact (show (((collisionResidual η i)*shiftedProduct
      (survivingPair p q η ξ i (collisionLastIndex x i)).left : ℕ) : ℝ) ≤
      ((collisionResidual η i)*∏ j ∈ Finset.Icc i (collisionLastIndex x i),
        (wholeWitnessPrime p η j-1) : ℕ) by exact_mod_cast hh).trans hsize
  have hshift (j : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card) :
      (((survivingPair p q η ξ i (collisionLastIndex x i)).left j-1 : ℕ) : ℝ) ≤ y := by
    exact (show (((survivingPair p q η ξ i (collisionLastIndex x i)).left j-1 : ℕ) : ℝ) ≤
      ((collisionResidual η i)*shiftedProduct (survivingPair p q η ξ i (collisionLastIndex x i)).left : ℕ) by
        exact_mod_cast Nat.le_of_dvd hprodpos
          ((shifted_factor_dvd _ j).trans (dvd_mul_left _ _))).trans hprodsize
  refine ⟨hrempos,?_,heq,?_,?_,?_,?_⟩
  · intro j
    exact ⟨(hgood j).1,(hgood j).2.1,(hgood j).2.2.1,
      (hinterval j).1,(hinterval j).2.1,(hinterval j).2.2.1,(hinterval j).2.2.2,
      hYb.symm ▸ (hgood j).2.2.2.1,hYb.symm ▸ (hgood j).2.2.2.2⟩
  · apply (le_div_iff₀ (by exact_mod_cast hrpos : (0 : ℝ) < collisionCanceledProduct p q η ξ i (collisionLastIndex x i))).mpr
    rw [mul_comm,← Nat.cast_mul,hfactor]
    exact hsize
  · simpa only [hYb,survivingPair,collisionResidual] using hres
  · intro hb
    obtain ⟨hb',hfirstidx⟩ := survivingIndex_first hik hfirst
    have hfirstp : (survivingPair p q η ξ i (collisionLastIndex x i)).left ⟨0,hb⟩ =
        wholeWitnessPrime p η i := by
      change wholeWitnessPrime p η (survivingIndex p q η ξ i (collisionLastIndex x i) ⟨0,hb⟩)=_
      rw [hfirstidx]
    apply hlarge _ _ (hgood ⟨0,hb⟩).1.1 (by simpa only [hfirstp] using hhead) hY1 hY1u
    exact normal_prime_omega_below (hgood ⟨0,hb⟩).1 hS hBS hSy (hshift ⟨0,hb⟩)

  · rw [hYb]
    apply squarefreeAbove_of_dvd ?_
      ((hgη i (Finset.mem_Icc.mpr ⟨Nat.zero_le _,hi⟩)).2.2.1)
    refine ⟨collisionCanceledProduct p q η ξ i (collisionLastIndex x i),?_⟩
    rw [mul_comm,canceled_surviving_product]

end TotientAsymptotic

end

end OAI
