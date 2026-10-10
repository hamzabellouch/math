import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListWeights
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkWeightBounds

namespace OAI

/-! The emitted ordinary bonds, active ports and constant have one explicit
polynomial envelope. The bound applies to the literal rational transition. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem two_mul_abs_le {a b P : ℝ} (hP : 0 ≤ P) (ha : |a| ≤ P) (hb : |b| ≤ P) :
    |2*a*b| ≤ 2*P^2 := by
  rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h := mul_le_mul ha hb (abs_nonneg b) hP
  nlinarith

theorem pairBonds_abs_le (n i : ℕ) (R : ℚ) (p : Pair) {P : ℝ}
    (hP : 0 ≤ P) (hR : |(R:ℝ)| ≤ P)
    (hJ : |(p.1.2:ℝ)| ≤ P) (hK : |(p.2.2:ℝ)| ≤ P)
    (b : Bond) (hb : b ∈ pairBonds n i R p) : |(b.2.2:ℝ)| ≤ 2*P^2 := by
  simp only [pairBonds,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · push_cast
    exact two_mul_abs_le hP hJ hK
  · push_cast
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := mul_self_le_mul_self (abs_nonneg (R:ℝ)) hR
    nlinarith [sq_abs (R:ℝ)]
  · push_cast
    exact two_mul_abs_le hP hR hJ
  · push_cast
    exact two_mul_abs_le hP hR hK

theorem next_scalar_abs_le (s : State) (N : ℚ) {L P : ℝ}
    (hc : CoefficientBound s L) (hP : 1 ≤ P) (hLP : L ≤ P)
    (hR : |(scale N s:ℝ)| ≤ P) :
    |((next N s).2.2.1:ℝ)| ≤ L+10*(pairCount s.2.2.2:ℝ)*P^2 := by
  have hP0 : 0 ≤ P := by linarith
  have hoff : ((((catalog s.2.2.2).map Prod.snd).map pairOffset).sum:ℝ) =
      ∑ e : Fin (pairCount s.2.2.2),
        qmaForkOffset (actualJ s.2.2.2 e:ℝ) (actualK s.2.2.2 e:ℝ) := by
    change (((((catalog s.2.2.2).map Prod.snd).map
      (fun p => 3/4+3*p.1.2^2+3*p.2.2^2)).sum:ℚ):ℝ)=_
    rw [catalog_weights_sum s.2.2.2 (fun J K => 3/4+3*J^2+3*K^2)]
    push_cast
    rfl
  have hsum : |∑ e : Fin (pairCount s.2.2.2),
      qmaForkOffset (actualJ s.2.2.2 e:ℝ) (actualK s.2.2.2 e:ℝ)| ≤
        (pairCount s.2.2.2:ℝ)*(7*P^2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _e : Fin (pairCount s.2.2.2), 7*P^2 :=
        Finset.sum_le_sum (fun e _ => qmaForkOffset_abs_le hP
          ((hc.actualJ s e).trans hLP) ((hc.actualK s e).trans hLP))
      _ = _ := by simp
  have hR2 : (scale N s:ℝ)^2 ≤ P^2 := by
    nlinarith [mul_self_le_mul_self (abs_nonneg (scale N s:ℝ)) hR,sq_abs (scale N s:ℝ)]
  have heq : ((next N s).2.2.1:ℝ)=(s.2.2.1:ℝ)+
      (∑ e : Fin (pairCount s.2.2.2),
        qmaForkOffset (actualJ s.2.2.2 e:ℝ) (actualK s.2.2.2 e:ℝ))+
      3*(pairCount s.2.2.2:ℝ)*(scale N s:ℝ)^2 := by
    change ((s.2.2.1+(((catalog s.2.2.2).map Prod.snd).map pairOffset).sum+
      3*(pairCount s.2.2.2:ℚ)*(scale N s)^2:ℚ):ℝ)=_
    rw [Rat.cast_add,Rat.cast_add,hoff]
    push_cast
    rfl
  rw [heq]
  have ha := abs_add_le (s.2.2.1:ℝ) (∑ e : Fin (pairCount s.2.2.2),
    qmaForkOffset (actualJ s.2.2.2 e:ℝ) (actualK s.2.2.2 e:ℝ))
  have hb := abs_add_le ((s.2.2.1:ℝ)+(∑ e : Fin (pairCount s.2.2.2),
    qmaForkOffset (actualJ s.2.2.2 e:ℝ) (actualK s.2.2.2 e:ℝ)))
    (3*(pairCount s.2.2.2:ℝ)*(scale N s:ℝ)^2)
  rw [abs_of_nonneg (by positivity : 0 ≤ 3*(pairCount s.2.2.2:ℝ)*(scale N s:ℝ)^2)] at hb
  nlinarith [hc.scalar,mul_le_mul_of_nonneg_left hR2
    (by positivity : 0 ≤ (pairCount s.2.2.2:ℝ))]

theorem next_coefficientBound (s : State) (hs : ValidPorts s.1 s.2.2.2) (N : ℚ)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (hN : 0 ≤ N)
    {M L T : ℝ} (hM : ((s.2.1.length+portMass s.2.2.2:ℕ):ℝ) ≤ M)
    (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : CoefficientBound s L) :
    CoefficientBound (next N s) (forkCoefficient M L T) := by
  let P := forkRadius M L T
  have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans hM
  have hL0 : 0 ≤ L := by linarith
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hB0 : 0 ≤ forkBudget M L := by unfold forkBudget; positivity
  have hLP : L ≤ P := by
    have hx : 0 ≤ 16*(forkBudget M L)^3*T := by positivity
    dsimp [P,forkRadius]
    linarith
  have hP : 1 ≤ P := hL.trans hLP
  have hP0 : 0 ≤ P := by linarith
  have hR : |(scale N s:ℝ)| ≤ P := scale_abs_bound s hb hn N hN hM hL hT hc
  have hp : (pairCount s.2.2.2:ℝ) ≤ M := by
    refine le_trans ?_ hM
    exact_mod_cast (show pairCount s.2.2.2 ≤ s.2.1.length+portMass s.2.2.2 by
      have := pairCount_le_portMass s.2.2.2
      omega)
  have hlarge : 2*P^2 ≤ forkCoefficient M L T := by
    dsimp [forkCoefficient]
    nlinarith [mul_nonneg hM0 (sq_nonneg P)]
  have hPL : P ≤ forkCoefficient M L T := by
    have hPP : P ≤ P^2 := by nlinarith
    calc
      P ≤ P^2 := hPP
      _ ≤ 2*P^2 := by nlinarith [sq_nonneg P]
      _ ≤ _ := hlarge
  constructor
  · have h := next_scalar_abs_le s N hc hP hLP hR
    have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg P)
    dsimp [forkCoefficient]
    nlinarith [sq_nonneg P]
  · intro b hmem
    change b ∈ s.2.1++addedBonds s (scale N s) at hmem
    rcases List.mem_append.mp hmem with hold | hnew
    · exact (hc.ordinary b hold).trans (hLP.trans hPL)
    obtain ⟨bs,hbs,hnew⟩ := List.mem_flatten.mp hnew
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
    have hi' : i < pairCount s.2.2.2 := by
      simpa only [catalog_length] using List.mem_range.mp hi
    rw [catalog_actualSite hs ⟨i,hi'⟩] at hnew
    exact (pairBonds_abs_le s.1 i (scale N s) _ hP0 hR
      ((hc.actualJ s _).trans hLP) ((hc.actualK s _).trans hLP) b hnew).trans hlarge
  · intro ps hps p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hps
    rcases List.mem_append.mp hp with hfresh | hold
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hfresh
      exact hR.trans hPL
    · exact (hc.active _ (groupAt_mem _ _ (List.mem_range.mp hi)) _
        (List.mem_of_mem_drop hold)).trans (hLP.trans hPL)

end ContinuumCoulomb.QuantumForkList

end

end OAI
