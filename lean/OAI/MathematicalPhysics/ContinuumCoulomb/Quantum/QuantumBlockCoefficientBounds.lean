import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBlockRational

namespace OAI

/-! Explicit polynomial magnitude bounds for the physical exchange list. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFieldEdgeWeight_bound (a : Fin 2) (t : ℝ) (k : Fin 3) :
    |qmaFieldEdgeWeight a t k| ≤ |t| := by
  have hs : 1 ≤ Real.sqrt 3 := by
    have hs0 := Real.sqrt_nonneg 3
    have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hd : |t/(2*Real.sqrt 3)| ≤ |t| := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 2*Real.sqrt 3)]
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.sqrt 3)).mpr
    nlinarith [abs_nonneg t]
  have hz : |t/2| ≤ |t| := by rw [abs_div]; norm_num
  by_cases ha : a = 0
  · subst a
    fin_cases k
    · simpa [qmaFieldEdgeWeight] using hd
    · simpa [qmaFieldEdgeWeight,neg_div] using hd
    · simp [qmaFieldEdgeWeight]
  · fin_cases k
    · simp [qmaFieldEdgeWeight,ha]
    · simp [qmaFieldEdgeWeight,ha]
    · simpa [qmaFieldEdgeWeight,ha,neg_div] using hz

theorem qmaFourAxisWeights_pointwise (a : Fin 2) (s : Bool) (p : Fin 4) :
    |qmaFourAxisWeights a s p| ≤ 28 :=
  (Finset.single_le_sum (fun q _ => abs_nonneg (qmaFourAxisWeights a s q))
    (Finset.mem_univ p)).trans (qmaFourAxisWeights_abs_sum a s)

theorem qmaFourCrossWeight_bound (r t : ℝ) (a b : Fin 2) (p q : Fin 4) :
    |r*qmaFourCouplingSize a b t*
      (qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign t) q)| ≤
        2352*|r| *(1+|t|) := by
  rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (qmaFourCouplingSize_nonneg a b t)]
  have hw : |qmaFourAxisWeights a true p| * |qmaFourAxisWeights b (qmaFourCouplingSign t) q| ≤ 784 := by
    have h := mul_le_mul (qmaFourAxisWeights_pointwise a true p)
      (qmaFourAxisWeights_pointwise b (qmaFourCouplingSign t) q)
      (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 28)
    norm_num at h
    exact h
  calc
    _ ≤ (|r| * (3*(1+|t|)))*784 := mul_le_mul
      (mul_le_mul_of_nonneg_left (qmaFourCouplingSize_bound a b t) (abs_nonneg r))
      hw (by positivity) (by positivity)
    _ = _ := by ring

theorem qmaFourEnergyOffset_bound (a b : Fin 2) (t : ℝ) :
    |qmaFourEnergyOffset a b t| ≤ 364800*|t| := by
  have ha := qmaFourAxisFieldShift_abs a (qmaFourCounterA a b t)
  have hb := qmaFourAxisFieldShift_abs b (qmaFourCounterB a b t)
  have hca := qmaFourCounterA_bound a b t
  have hcb := qmaFourCounterB_bound a b t
  have hm : |qmaFourCouplingFactor a b t*qmaFourAxisShift a true*
      qmaFourAxisShift b (qmaFourCouplingSign t)| ≤ 160000*|t| := by
    rw [abs_mul,abs_mul,abs_of_nonneg (qmaFourCouplingFactor_nonneg a b t)]
    calc
      _ ≤ (|t| * 400)*400 := mul_le_mul
        (mul_le_mul (qmaFourCouplingFactor_bound a b t) (qmaFourAxisShift_abs_bound a true)
          (abs_nonneg _) (abs_nonneg t)) (qmaFourAxisShift_abs_bound b _)
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hsum := abs_add_le (qmaFourAxisFieldShift a (qmaFourCounterA a b t))
    (qmaFourAxisFieldShift b (qmaFourCounterB a b t))
  have hsub := abs_sub
    (qmaFourAxisFieldShift a (qmaFourCounterA a b t)+qmaFourAxisFieldShift b (qmaFourCounterB a b t))
    (qmaFourCouplingFactor a b t*qmaFourAxisShift a true*qmaFourAxisShift b (qmaFourCouplingSign t))
  unfold qmaFourEnergyOffset
  linarith

variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

omit [Fintype κ] [Fintype τ] in
theorem qmaFourExchangeWeight_bound (r : ℝ) (a b : κ → Fin 2) (t : κ → ℝ)
    (axis : τ → Fin 2) (weight : τ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (ht : ∀ e, |t e| ≤ B) (hw : ∀ e, |weight e| ≤ B) (x : QMAFourExchangeIndex n κ τ) :
    |qmaFourExchangeWeight r a b t axis weight x| ≤
      r^2+2352*|r| *(1+B)+102400*B+B := by
  have hc0 : 0 ≤ 2352*|r| *(1+B) := by positivity
  cases x with
  | inl x =>
    change |r^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg r)]
    nlinarith
  | inr x =>
    cases x with
    | inl x =>
      have h := (qmaFourCrossWeight_bound r (t x.1) (a x.1) (b x.1) x.2.1 x.2.2).trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl (ht x.1)) (by positivity : 0 ≤ 2352*|r|))
      exact h.trans (by nlinarith [sq_nonneg r])
    | inr x =>
      cases x with
      | inl x =>
        change |if x.2.1 = 0 then _ else _| ≤ _
        split_ifs
        · have h := (qmaFieldEdgeWeight_bound (a x.1) (qmaFourCounterA (a x.1) (b x.1) (t x.1)) x.2.2).trans
            ((qmaFourCounterA_bound (a x.1) (b x.1) (t x.1)).trans
              (mul_le_mul_of_nonneg_left (ht x.1) (by norm_num)))
          exact h.trans (by nlinarith [sq_nonneg r])
        · have h := (qmaFieldEdgeWeight_bound (b x.1) (qmaFourCounterB (a x.1) (b x.1) (t x.1)) x.2.2).trans
            ((qmaFourCounterB_bound (a x.1) (b x.1) (t x.1)).trans
              (mul_le_mul_of_nonneg_left (ht x.1) (by norm_num)))
          exact h.trans (by nlinarith [sq_nonneg r])
      | inr x =>
        have h := (qmaFieldEdgeWeight_bound (axis x.1) (weight x.1) x.2).trans (hw x.1)
        exact h.trans (by nlinarith [sq_nonneg r])

omit [Fintype τ] in
theorem qmaSum_subtype_abs_le (p : κ → Prop) [DecidablePred p] (J : κ → ℝ) :
    (∑ e : {x // p x}, |J e.val|) ≤ ∑ e, |J e| := by
  have h := Fintype.sum_subtype_add_sum_subtype p (fun e => |J e|)
  have hn : 0 ≤ ∑ e : {x // ¬p x}, |J e.val| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  linarith

omit [Fintype τ] in
theorem qmaXZFamilyConstant_bound (t : κ → QMAXZTerm n) (J : κ → ℝ) :
    |qmaXZFamilyConstant t J| ≤ 364801*(∑ e, |J e|) := by
  have hp := qmaSum_subtype_abs_le (fun e => (t e).IsPair) J
  have hs := qmaSum_subtype_abs_le (fun e => (t e).IsScalar) J
  have hsp := Finset.abs_sum_le_sum_abs (fun e : QMAXZScalarIndex t => J e.val) Finset.univ
  have hpp := Finset.abs_sum_le_sum_abs (fun e : QMAXZPairIndex t =>
      qmaFourEnergyOffset (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val)) Finset.univ
  have he : (∑ e : QMAXZPairIndex t,
      |qmaFourEnergyOffset (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val)|) ≤
        364800*(∑ e : QMAXZPairIndex t, |J e.val|) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun _ _ => qmaFourEnergyOffset_bound _ _ _)
  have hd := abs_sub (∑ e : QMAXZScalarIndex t, J e.val)
    (∑ e : QMAXZPairIndex t, qmaFourEnergyOffset
      (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val))
  unfold qmaXZFamilyConstant
  linarith

omit [Fintype τ] in
theorem qmaXZBlock_exchange_count (t : κ → QMAXZTerm n) :
    Fintype.card (QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t)) ≤
      6*n+25*Fintype.card κ := by
  rw [qmaFourExchange_count]
  have hp := Fintype.card_subtype_le (fun e => (t e).IsPair)
  have hf := Fintype.card_subtype_le (fun e => (t e).IsField)
  change Fintype.card (QMAXZPairIndex t) ≤ Fintype.card κ at hp
  change Fintype.card (QMAXZFieldIndex t) ≤ Fintype.card κ at hf
  omega

end ContinuumCoulomb

end

end OAI
