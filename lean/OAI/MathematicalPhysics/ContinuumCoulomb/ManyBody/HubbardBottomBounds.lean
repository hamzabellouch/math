import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardVariationalWitness

namespace OAI

/-! Polynomial bounds on the actual half-filled Hubbard bottom. These
control its contribution to the full-continuum complement smallness test. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

theorem chargePenalty_abs_bound {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (o : Fin m → Fin 3) :
    |chargePenalty U V o| ≤ (m:ℝ)*|U|/2+(1/2:ℝ)*∑ i, ∑ j, |V i j| := by
  have hd (i : Fin m) : |occupationDeviation o i| ≤ 1 := by
    unfold occupationDeviation
    generalize o i = t
    fin_cases t <;> norm_num
  have hd2 (i : Fin m) : occupationDeviation o i^2 ≤ 1 := by
    nlinarith [abs_le.mp (hd i)]
  have hs : (∑ i, occupationDeviation o i^2) ≤ (m:ℝ) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hd2 i)
  have hnonneg : 0 ≤ ∑ i, occupationDeviation o i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have ht : |∑ i, ∑ j, V i j*occupationDeviation o i*occupationDeviation o j| ≤ ∑ i, ∑ j, |V i j| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul,abs_mul]
    calc
      _ ≤ |V i j| * 1 * 1 := by gcongr <;> apply hd
      _ = _ := by ring
  calc
    _ ≤ |U/2*(∑ i, occupationDeviation o i^2)|+
        |(1/2:ℝ)*(∑ i, ∑ j, V i j*occupationDeviation o i*occupationDeviation o j)| := abs_add_le _ _
    _ ≤ |U|/2*(m:ℝ)+(1/2:ℝ)*∑ i, ∑ j, |V i j| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hnonneg,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),
        abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hs (by positivity))
        (mul_le_mul_of_nonneg_left ht (by norm_num))
    _ = _ := by ring

theorem fockOperator_diagonal_norm {Q : ℕ} (f : Finset (Fin (Q+1)) → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ A, ‖f A‖ ≤ C) :
    ‖fockOperator (fockDiagonal f)‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  rw [fockOperator_diagonal_apply,norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hf A) 2) (sq_nonneg _)

theorem chargePenaltyFock_norm (m : ℕ) (U : ℝ) (V : Fin (m+1) → Fin (m+1) → ℝ) :
    ‖fockOperator (chargePenaltyFock m U V)‖ ≤
      (m+1:ℝ)*|U|/2+(1/2:ℝ)*∑ i, ∑ j, |V i j| := by
  apply fockOperator_diagonal_norm _ (by positivity)
  intro A
  simpa only [Complex.norm_real,Real.norm_eq_abs,Nat.cast_add,Nat.cast_one] using
    chargePenalty_abs_bound U V (occupationAt m A)

theorem hubbardFermionBottom_abs_bound {Edge : Type*} [Fintype Edge]
    (m : ℕ) (U : ℝ) (V : Fin (m+1) → Fin (m+1) → ℝ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℝ) :
    |hubbardFermionBottom m U V left right t| ≤
      (m+1:ℝ)*|U|/2+(1/2:ℝ)*∑ i, ∑ j, |V i j|+4*∑ e, |t e| := by
  let T := chargePenaltyFock m U V+graphHopping m left right (fun e => (t e:ℂ))
  have hop : ‖fockOperator T‖ ≤
      (m+1:ℝ)*|U|/2+(1/2:ℝ)*∑ i, ∑ j, |V i j|+4*∑ e, |t e| := by
    calc
      _ ≤ ‖fockOperator (chargePenaltyFock m U V)‖+
          ‖fockOperator (graphHopping m left right (fun e => (t e:ℂ)))‖ := by
        rw [show fockOperator T = fockOperator (chargePenaltyFock m U V)+
            fockOperator (graphHopping m left right (fun e => (t e:ℂ))) from fockOperator_add _ _]
        exact norm_add_le _ _
      _ ≤ _ := add_le_add (chargePenaltyFock_norm m U V) (by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using
          fockOperator_graphHopping_norm m left right (fun e => (t e:ℂ)))
  obtain ⟨x,hx,hm⟩ := exists_halfFilled_unit_mass m
  have hset : Set.Nonempty {e | ∃ y : Space (2*m+1), IsHalfFilled m y ∧ 0 < fockMass y ∧
      e = hubbardFermionForm m U V left right t y/fockMass y} :=
    ⟨_,x,hx,by rw [hm]; norm_num,rfl⟩
  have hlo : -‖fockOperator T‖ ≤ hubbardFermionBottom m U V left right t := by
    apply le_csInf hset
    rintro e ⟨y,_hy,hy,rfl⟩
    apply (le_div_iff₀ hy).mpr
    have h := (abs_le.mp (hubbardFermionForm_abs_bound m U V left right t y)).1
    linarith only [h]
  have hhi := (hubbardFermionBottom_lower m U V left right t x hx).trans
    (le_abs_self _ |>.trans (hubbardFermionForm_abs_bound m U V left right t x))
  rw [hm,mul_one,mul_one] at hhi
  exact (abs_le.mpr ⟨hlo,hhi⟩).trans hop

end ContinuumCoulomb.HubbardGlobal

end

end OAI
