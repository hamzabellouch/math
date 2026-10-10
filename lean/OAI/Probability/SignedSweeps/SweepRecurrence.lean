import OAI.Probability.SignedSweeps.MarkedTrace
import OAI.Probability.SignedSweeps.OccupiedSweep

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma columnPowerCoefficient_action_fintype {a b : ℕ} (lam : Partition (2^(a+b))) (r : ℕ)
    (I : Fintype (SymmetricGroup (2^(a+b)))) :
    letI := I
    coefficientAction (spechtRepresentation lam) (columnPowerCoefficient a b r) =
      columnSquarePower lam r := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^(a+b))) (Fin (2^(a+b)))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact columnPowerCoefficient_action lam r

lemma rowPowerCoefficient_action_fintype {a b : ℕ} (lam : Partition (2^(a+b))) (r : ℕ)
    (I : Fintype (SymmetricGroup (2^(a+b)))) :
    letI := I
    coefficientAction (spechtRepresentation lam) (rowPowerCoefficient a b r) =
      rowSquarePower lam r := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^(a+b))) (Fin (2^(a+b)))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact rowPowerCoefficient_action lam r

theorem signed_sweep_recurrence {a b j q R : ℕ} (hq : 0 < q)
    {η τ κ : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1) (hκ : 0 ≤ κ) (hκτ : κ ≤ τ)
    (HA : ∀ (lam : Partition (2^a)) (u v l : ℕ) (h : u+v+l=2^a)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^a) l))
    (HB : ∀ (lam : Partition (2^b)) (u v l : ℕ) (h : u+v+l=2^b)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^b) l))
    (hR : 2*max (2^a) (2^b)+2*q+1 ≤ R)
    (lam : Partition (2^(a+b))) (u v l : ℕ) (h : u+v+l=2^(a+b))
    (α : Partition u) (β : Partition v) (γ : Partition l)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q)
    (ho : SignedOccurrence h α β γ lam) :
    weightedMoment lam (2^j) ≤ Real.exp (η*signedEntropy α β+
      τ*l*Real.log (2^(a+b) : ℕ)-(l:ℝ)*Real.log ((2^(a+b) : ℕ)/ (l:ℝ))+6*l+
      (2^b : ℕ)*typedLineError (2^a) q R+(2^a : ℕ)*typedLineError (2^b) q R+
      holeClippingError κ (2^a) (2^b)+((2^a : ℕ)+(2^b : ℕ) : ℝ)*Real.log (l+1)) := by
  let f := columnPowerCoefficient a b (2^j)
  let g := rowPowerCoefficient a b (2^j)
  have hf : (coefficientAction finiteRegularRepresentation f).IsPositive :=
    columnPowerCoefficient_positive_fintype a b (2^j) _
  have hg : (coefficientAction finiteRegularRepresentation g).IsPositive :=
    rowPowerCoefficient_positive_fintype a b (2^j) _
  let M := (LinearMap.trace ℂ (MarkedWordSpace (u+v) l (2^(a+b)) (Fin q))
      (markedTypeProjection rfl h α β (Fin q) *
        coefficientAction (markedWordRepresentation h (Fin q)) f *
        coefficientAction (markedWordRepresentation h (Fin q)) g)).re
  have ht : (spechtDimension γ:ℝ) *
      (LinearMap.trace ℂ (Specht lam) (sweepSquare lam^(2^j))).re ≤ M := by
    have hx := signed_occurrence_marked_trace rfl h h α β γ lam
      (Fin.castLEEmb hα) (Fin.castLEEmb hβ) ho
      (Fin.castLEEmb (show l ≤ 2^(a+b) by omega))
      ⟨Finset.univ.map (Fin.castLEEmb (show u ≤ u+v by omega)), by simp⟩ f g hf hg
    have hs := sweepSquare_dyadic_trace_split lam j
    rw [LinearMap.trace_mul_comm] at hs
    apply (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (spechtDimension γ))).trans
    simpa only [f, g, columnPowerCoefficient_action_fintype,
      rowPowerCoefficient_action_fintype] using hx
  have hd := signedOccurrence_dimension (by positivity : 0 < 2^(a+b)) ho
  have hJ : weightedMoment lam (2^j) ≤
      Real.exp (signedEntropy α β+(l:ℝ)*Real.log ((2^(a+b):ℕ)/(l:ℝ))+l)*M := by
    calc
      _ ≤ (Real.exp (signedEntropy α β+(l:ℝ)*Real.log ((2^(a+b):ℕ)/(l:ℝ))+l)*spechtDimension γ)*
          (LinearMap.trace ℂ (Specht lam) (sweepSquare lam^(2^j))).re :=
        mul_le_mul_of_nonneg_right hd (Complex.re_le_re (sweepSquare_pow_positive lam (2^j)).trace_nonneg)
      _ = Real.exp (signedEntropy α β+(l:ℝ)*Real.log ((2^(a+b):ℕ)/(l:ℝ))+l)*
          ((spechtDimension γ:ℝ)*(LinearMap.trace ℂ (Specht lam) (sweepSquare lam^(2^j))).re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
  let E : ℝ := (η-1)*signedEntropy α β+l+(2^b : ℕ)*typedLineError (2^a) q R+
      (2^a : ℕ)*typedLineError (2^b) q R
  have hM : M ≤ Real.exp E*holeTraceSum τ (2^a) (2^b) l := by
    dsimp only [M]
    rw [marked_positive_product_trace_split rfl h α β (sweepBoard a b) f g
      (columnPowerCoefficient_support a b (2^j)) (rowPowerCoefficient_support a b (2^j)), Complex.re_sum]
    calc
      _ ≤ ∑ z : MarkedAssignment l (2^(a+b)),
          holePrefactor (markedBoardPlacement (sweepBoard a b) z)*
            Real.exp (holeBudget τ (markedBoardPlacement (sweepBoard a b) z).1+E) := by
        apply Finset.sum_le_sum
        intro z _
        simpa only [E, add_assoc] using occupied_sweep_trace_bound hq h z hη hη' HA HB hR rfl α β hα hβ
      _ = Real.exp E * (∑ z : MarkedAssignment l (2^(a+b)),
          holePrefactor (markedBoardPlacement (sweepBoard a b) z)*
            Real.exp (holeBudget τ (markedBoardPlacement (sweepBoard a b) z).1)) := by
        simp only [Real.exp_add, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by
        congr 1
        change (∑ z : MarkedAssignment l (2^(a+b)),
            holePrefactor (markedBoardPlacement (sweepBoard a b) z) *
              Real.exp (holeBudget τ (markedBoardPlacement (sweepBoard a b) z).1)) =
          ∑ z : HolePlacement (2^a) (2^b) l,
            holePrefactor z * Real.exp (holeBudget τ z.1)
        exact Equiv.sum_comp (markedBoardPlacement (sweepBoard a b))
          (fun z : HolePlacement (2^a) (2^b) l => holePrefactor z * Real.exp (holeBudget τ z.1))
  have hh := holeTraceSum_bound (l:=l) hκ hκτ (by positivity : 0 < 2^a) (by positivity : 0 < 2^b)
  rw [← Nat.pow_add] at hh
  apply hJ.trans
  apply (mul_le_mul_of_nonneg_left hM (Real.exp_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)) (Real.exp_nonneg _)).trans_eq
  dsimp only [E]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end SignedSweeps
end

end OAI
