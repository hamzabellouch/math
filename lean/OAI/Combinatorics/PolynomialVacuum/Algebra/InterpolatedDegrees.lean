import OAI.Combinatorics.PolynomialVacuum.Algebra.SpectatorDegree
import OAI.Combinatorics.PolynomialVacuum.Algebra.LagrangeDegree
import OAI.Combinatorics.PolynomialVacuum.Algebra.LastPolynomial

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem zeroNodeProduct_spectator_degree {m : ℕ} (j : Fin m) :
    (∏ i : Fin m, (X i.castSucc-C T⁻¹*X (Fin.last m)) : MvPolynomial (Fin (m+1)) ℂ).degreeOf j.castSucc ≤ 1 := by
  apply (degreeOf_prod_le _ _ _).trans
  calc
    _ ≤ ∑ i : Fin m, if i=j then 1 else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      have hz : (-(C T⁻¹*X (Fin.last m)) : MvPolynomial (Fin (m+1)) ℂ).degreeOf j.castSucc≤0 := by
        rw [degreeOf_neg]
        exact dconst_mul _ (le_of_eq (degreeOf_X_of_ne (Fin.castSucc_ne_last j)))
      rw [sub_eq_add_neg]
      by_cases h : i=j
      · subst i; simp only [ite_true]; exact dadd (by simp) (hz.trans (by omega))
      · simp only [ite_eq_right h]
        exact dadd (le_of_eq (degreeOf_X_of_ne (by
          intro he; exact h (Fin.castSucc_injective _ he.symm)))) hz
    _ = 1 := by simp

 

theorem interpolateState_spectator_degrees {n : ℕ} (hn : 2≤n)
    (ψ : State n) (χ : State (n+1)) (hψ : LowerExchange (liftState ψ) n)
    (hd : ∀ s l, (ψ s).degreeOf l≤n-1)
    (hf : ∀ s l, s l=Spin.plus → (ψ s).degreeOf l≤n-2)
    (hχd : ∀ s l, (χ s).degreeOf l≤n)
    (hχf : ∀ s l, s l=Spin.plus → (χ s).degreeOf l≤n-1)
    (s : Fin (n+2) → Spin) (j : Fin (n+1)) :
    (interpolateState ψ χ s).degreeOf j.castSucc≤n+1 ∧
    (s j.castSucc=Spin.plus → (interpolateState ψ χ s).degreeOf j.castSucc≤n) := by
  have hlo : ∀ s l, (ψ s).degreeOf l≤(n-2)+1 := by
    intro s l; have:=hd s l; omega
  have hc (i) (hi : i≠j) := cupPrescription_spectator_degrees ψ hlo hf i j (Ne.symm hi) s
  have hm := cupPrescription_marked_degrees ψ j s
  have hzm : (C T⁻¹*X (Fin.last (n+1)) : MvPolynomial (Fin (n+2)) ℂ).degreeOf j.castSucc≤0 :=
    dconst_mul _ (le_of_eq (degreeOf_X_of_ne (Fin.castSucc_ne_last j)))
  have hχ (d : ℕ) (h : (χ (s ∘ Fin.castSucc)).degreeOf j≤d) :
      ((∏ i : Fin (n+1), (X i.castSucc-C T⁻¹*X (Fin.last (n+1))))*
        rename Fin.castSucc (χ (s ∘ Fin.castSucc))).degreeOf j.castSucc≤d+1 := by
    have hh : (rename Fin.castSucc (χ (s ∘ Fin.castSucc))).degreeOf j.castSucc≤d := by
      rw [degreeOf_rename_of_injective (Fin.castSucc_injective _)]; exact h
    exact (dmul (zeroNodeProduct_spectator_degree j) hh).trans (by omega)
  unfold interpolateState
  dsimp only
  split_ifs with hs hs0
  · have hcan (d : ℕ) (hmark : (cupPrescription ψ j s).degreeOf j≤d+n)
        (ho : ∀ i, i≠j → (cupPrescription ψ i s).degreeOf j≤d) :=
      canonicalInterpolant_spectator_degree _ (cupPrescription_collision ψ hψ s) j d hmark ho
    constructor
    · exact hcan (n+1) (hm.1.trans (by omega)) (by
        intro i hi; exact (hc i hi).1.trans (by omega))
    · intro hj
      apply hcan n
      · exact (hm.2 hj (by simp [hs,charge])).trans (by omega)
      · intro i hi; exact ((hc i hi).2 hj).trans (by omega)
  · have hcan (d : ℕ) (hmark : (dividedCupPrescription ψ j s).degreeOf j≤d+n)
        (ho : ∀ i, i≠j → (cupPrescription ψ i s).degreeOf j≤d) :=
      canonicalInterpolant_spectator_degree _ (dividedCupPrescription_collision ψ hψ s) j d hmark
        (fun i hi => by rw [dividedCupPrescription_spectator_degree_eq ψ i j (Ne.symm hi)]; exact ho i hi)
    constructor
    · apply dadd
      · exact (dmul hzm (hcan (n+1) ((dividedCupPrescription_marked_degree ψ j s).trans (by omega))
          (by intro i hi; exact (hc i hi).1.trans (by omega)))).trans (by omega)
      · exact hχ n (hχd _ _)
    · intro hj
      apply dadd
      · exact (dmul hzm (hcan n ((dividedCupPrescription_marked_degree ψ j s).trans (by omega))
          (by intro i hi; exact ((hc i hi).2 hj).trans (by omega)))).trans (by omega)
      · exact (hχ (n-1) (hχf _ _ hj)).trans (by omega)
  · simp only [add_zero]
    have hcan (d : ℕ) (hdn : 2*n≤d+n)
        (ho : ∀ i, i≠j → (cupPrescription ψ i s).degreeOf j≤d) :=
      canonicalInterpolant_spectator_degree _ (dividedCupPrescription_collision ψ hψ s) j d
        ((dividedCupPrescription_marked_degree ψ j s).trans hdn)
        (fun i hi => by rw [dividedCupPrescription_spectator_degree_eq ψ i j (Ne.symm hi)]; exact ho i hi)
    constructor
    · exact (dmul hzm (hcan (n+1) (by omega) (by intro i hi; exact (hc i hi).1.trans (by omega)))).trans (by omega)
    · intro hj
      exact (dmul hzm (hcan n (by omega) (by intro i hi; exact ((hc i hi).2 hj).trans (by omega)))).trans (by omega)

end PolynomialVacuumAlgebra

end OAI
