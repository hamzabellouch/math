import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListIterateWeights
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathWeightBounds

namespace OAI

/-! The first odd subdivision satisfies the same polynomial envelope as
the subsequent fork rounds, with its actual rational coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initialScale_abs_bound (bs : List Bond) (c N : ℚ) (hN : 0 ≤ N)
    {M L T : ℝ} (hm : (bs.length:ℝ) ≤ M) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : |(c:ℝ)| ≤ L)
    (hw : ∀ b ∈ bs, |(b.2.2:ℝ)| ≤ L) :
    |(initialScale N bs c:ℝ)| ≤ forkRadius M L T := by
  have hM : 0 ≤ M := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hn0 : 0 ≤ (N:ℝ) := by exact_mod_cast hN
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hlin : (∑ e : Fin bs.length, (1+2*|((bs.get e).2.2:ℝ)|)) ≤ M*(1+4*L) := by
    calc
      _ ≤ ∑ _e : Fin bs.length, (1+4*L) :=
        Finset.sum_le_sum (fun e _ => by linarith [hw (bs.get e) (List.get_mem bs e)])
      _ = (bs.length:ℝ)*(1+4*L) := by simp [mul_add]
      _ ≤ M*(1+4*L) := mul_le_mul_of_nonneg_right hm (by positivity)
  have hsq : (∑ e : Fin bs.length, (1+|((bs.get e).2.2:ℝ)|)^2) ≤ M*(1+2*L)^2 := by
    calc
      _ ≤ ∑ _e : Fin bs.length, (1+2*L)^2 :=
        Finset.sum_le_sum (fun e _ => pow_le_pow_left₀ (by positivity)
          (by linarith [hw (bs.get e) (List.get_mem bs e)]) 2)
      _ = (bs.length:ℝ)*(1+2*L)^2 := by simp
      _ ≤ M*(1+2*L)^2 := mul_le_mul_of_nonneg_right hm (sq_nonneg _)
  let A := 3*∑ e : Fin bs.length, (1+2*|((bs.get e).2.2:ℝ)|)
  let D := |(c:ℝ)|+4*∑ e : Fin bs.length, (1+|((bs.get e).2.2:ℝ)|)^2
  have hAD0 : 0 ≤ A+D+1 := by dsimp [A,D]; positivity
  have hextra : 0 ≤ 3*M*L+8*M*(1+2*L)^2 := by positivity
  have hAD : A+D+1 ≤ forkBudget M L := by
    dsimp only [A,D,forkBudget]
    linarith
  have hcube := pow_le_pow_left₀ hAD0 hAD 3
  rw [initialScale_cast]
  change |16*(A+D+1)^3*(N:ℝ)+4*(A+D+1)+1| ≤ _
  rw [abs_of_nonneg (by positivity)]
  have hnT : (N:ℝ) ≤ T := by simpa only [abs_of_nonneg hn0] using hT
  have hprod := mul_le_mul hcube hnT hn0 (pow_nonneg (hAD0.trans hAD) 3)
  dsimp only [forkRadius]
  nlinarith

theorem initial_coefficientBound (n : ℕ) (bs : List Bond) (c N : ℚ) (hN : 0 ≤ N)
    {M L T : ℝ} (hm : (bs.length:ℝ) ≤ M) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : |(c:ℝ)| ≤ L)
    (hw : ∀ b ∈ bs, |(b.2.2:ℝ)| ≤ L) :
    CoefficientBound (initial n bs c N) (forkCoefficient M L T) := by
  let P := forkRadius M L T
  have hM : 0 ≤ M := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hB0 : 0 ≤ forkBudget M L := by unfold forkBudget; positivity
  have hLP : L ≤ P := by
    have hx : 0 ≤ 16*(forkBudget M L)^3*T := by positivity
    dsimp [P,forkRadius]
    linarith
  have hP : 1 ≤ P := hL.trans hLP
  have hP0 : 0 ≤ P := by linarith
  have hR : |(initialScale N bs c:ℝ)| ≤ P := initialScale_abs_bound bs c N hN hm hL hT hc hw
  have hR2 : (initialScale N bs c:ℝ)^2 ≤ P^2 := by
    nlinarith [mul_self_le_mul_self (abs_nonneg _) hR,sq_abs (initialScale N bs c:ℝ)]
  have hlarge : 2*P^2 ≤ forkCoefficient M L T := by
    dsimp [forkCoefficient]
    nlinarith [mul_nonneg hM (sq_nonneg P)]
  have hPP : P ≤ 2*P^2 := by nlinarith
  have hoff : (((bs.map (fun b => 3/4+3*b.2.2^2)).sum:ℚ):ℝ)=
      ∑ e : Fin bs.length, qmaPathOffset ((bs.get e).2.2:ℝ) := by
    rw [initial_list_sum]
    push_cast
    rfl
  have hsum : |∑ e : Fin bs.length, qmaPathOffset ((bs.get e).2.2:ℝ)| ≤
      (bs.length:ℝ)*(4*P^2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _e : Fin bs.length, 4*P^2 := Finset.sum_le_sum (fun e _ =>
        qmaPathOffset_abs_le hP ((hw _ (List.get_mem _ _)).trans hLP))
      _ = _ := by simp
  constructor
  · have heq : ((initial n bs c N).2.2.1:ℝ)=(c:ℝ)+
        (∑ e : Fin bs.length, qmaPathOffset ((bs.get e).2.2:ℝ))+
        3*(bs.length:ℝ)*(initialScale N bs c:ℝ)^2 := by
      change ((c+(bs.map (fun b => 3/4+3*b.2.2^2)).sum+
        3*(bs.length:ℚ)*(initialScale N bs c)^2:ℚ):ℝ)=_
      rw [Rat.cast_add,Rat.cast_add,hoff]
      push_cast
      rfl
    rw [heq]
    have ha := abs_add_le (c:ℝ) (∑ e : Fin bs.length, qmaPathOffset ((bs.get e).2.2:ℝ))
    have hb := abs_add_le ((c:ℝ)+(∑ e : Fin bs.length, qmaPathOffset ((bs.get e).2.2:ℝ)))
      (3*(bs.length:ℝ)*(initialScale N bs c:ℝ)^2)
    rw [abs_of_nonneg (by positivity : 0 ≤ 3*(bs.length:ℝ)*(initialScale N bs c:ℝ)^2)] at hb
    have hprod := mul_le_mul_of_nonneg_left hR2 (Nat.cast_nonneg bs.length)
    have hmprod := mul_le_mul_of_nonneg_right hm (sq_nonneg P)
    dsimp only [forkCoefficient]
    nlinarith [sq_nonneg P]
  · intro b hb
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
    change |(((initialScale N bs c)^2:ℚ):ℝ)| ≤ _
    push_cast
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hR2.trans ((by nlinarith [sq_nonneg P] : P^2 ≤ 2*P^2).trans hlarge)
  · intro ps hps p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hps
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have hj' := (initialIndices_mem bs i j hj).1
    have hmem : initialBond bs j ∈ bs := by
      have hq : j/2<bs.length := by omega
      unfold initialBond
      rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hq,Option.getD_some]
      exact List.getElem_mem hq
    change |(initialWeight bs (initialScale N bs c) j:ℝ)| ≤ _
    by_cases hj0 : j%2=0
    · simpa only [initialWeight,ite_eq_left hj0] using hR.trans (hPP.trans hlarge)
    · simp only [initialWeight,ite_eq_right hj0]
      push_cast
      exact (two_mul_abs_le hP0 hR ((hw _ hmem).trans hLP)).trans hlarge

end ContinuumCoulomb.QuantumForkList

end

end OAI
