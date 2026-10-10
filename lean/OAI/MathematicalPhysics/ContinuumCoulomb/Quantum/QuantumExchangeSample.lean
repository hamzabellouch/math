import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAxisSampleAccuracy
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOffsetProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBlockBudget

namespace OAI

/-! Certified rational values for every edge of the actual physical exchange family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped Classical BigOperators

def stencil (a : Fin 2) (s : Bool) : Fin 4 → ℚ :=
  if a = 0 then if s then ![11,-1,-13,3] else ![11,-1,3,-13]
  else if s then ![1,-1,0,0] else ![1,1,0,0]

theorem stencil_cast (a : Fin 2) (s : Bool) (p : Fin 4) :
    (stencil a s p:ℝ) = qmaFourAxisWeights a s p := by
  fin_cases a <;> cases s <;> fin_cases p <;>
    norm_num [stencil,qmaFourAxisWeights,qmaFourXWeights,qmaFourZWeights]

def crossValue (k : ℕ) (r : ℚ) (a b : Fin 2) (t : ℚ) (p q : Fin 4) : ℚ :=
  r*calibrated a b (k,t)*(stencil a true p*stencil b (decide (t ≤ 0)) q)

theorem crossValue_error (k : ℕ) (r : ℚ) (a b : Fin 2) (t : ℚ) (p q : Fin 4) :
    |(crossValue k r a b t p q:ℝ)-(r:ℝ)*qmaFourCouplingSize a b (t:ℝ)*
      (qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign (t:ℝ)) q)| ≤
        1568*|(r:ℝ)| *(1+|(t:ℝ)|)*(2:ℝ)⁻¹^k := by
  have hw : |qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign (t:ℝ)) q| ≤ 784 := by
    rw [abs_mul]
    exact (mul_le_mul (qmaFourAxisWeights_pointwise a true p)
      (qmaFourAxisWeights_pointwise b (qmaFourCouplingSign (t:ℝ)) q)
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  simp only [crossValue,Rat.cast_mul,stencil_cast,sign_cast]
  calc
    _ = |(r:ℝ)| *|(calibrated a b (k,t):ℝ)-qmaFourCouplingSize a b (t:ℝ)| *
        |qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign (t:ℝ)) q| := by
      rw [show (r:ℝ)*(calibrated a b (k,t):ℝ)*(qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign (t:ℝ)) q)-
          (r:ℝ)*qmaFourCouplingSize a b (t:ℝ)*(qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign (t:ℝ)) q) =
        ((r:ℝ)*((calibrated a b (k,t):ℝ)-qmaFourCouplingSize a b (t:ℝ)))*
          (qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign (t:ℝ)) q) by ring,
        abs_mul,abs_mul]
    _ ≤ (|(r:ℝ)| *(2*(1+|(t:ℝ)|)*(2:ℝ)⁻¹^k))*784 := mul_le_mul
      (mul_le_mul_of_nonneg_left (calibrated_error a b k t) (abs_nonneg _)) hw
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

variable {n : ℕ} {κ τ : Type*}

def weightValue (k : ℕ) (r : ℚ) (a b : κ → Fin 2) (t : κ → ℚ)
    (axis : τ → Fin 2) (weight : τ → ℚ) : QMAFourExchangeIndex n κ τ → ℚ
  | .inl _ => r^2
  | .inr (.inl (e,p,q)) => crossValue k r (a e) (b e) (t e) p q
  | .inr (.inr (.inl (e,s,j))) => if s = 0 then
      fieldValue k (a e) (counterA k (a e) (b e) (t e)) j else
      fieldValue k (b e) (counterB k (a e) (b e) (t e)) j
  | .inr (.inr (.inr (e,j))) => fieldValue k (axis e) (weight e) j

def weightErrorBudget (r B : ℝ) : ℝ := 1568*|r| *(1+B)+26064*B

theorem weightValue_error (k : ℕ) (r : ℚ) (a b : κ → Fin 2) (t : κ → ℚ)
    (axis : τ → Fin 2) (weight : τ → ℚ) (B : ℝ) (hB : 0 ≤ B)
    (ht : ∀ e, |(t e:ℝ)| ≤ B) (hw : ∀ e, |(weight e:ℝ)| ≤ B)
    (x : QMAFourExchangeIndex n κ τ) :
    |(weightValue k r a b t axis weight x:ℝ)-
      qmaFourExchangeWeight (r:ℝ) a b (fun e => (t e:ℝ)) axis (fun e => (weight e:ℝ)) x| ≤
        weightErrorBudget (r:ℝ) B*(2:ℝ)⁻¹^k := by
  have heps : 0 ≤ (2:ℝ)⁻¹^k := by positivity
  have hcross : 0 ≤ 1568*|(r:ℝ)| *(1+B)*(2:ℝ)⁻¹^k := by positivity
  cases x with
  | inl x =>
    simp only [weightValue,qmaFourExchangeWeight,Rat.cast_pow,sub_self,abs_zero,weightErrorBudget]
    positivity
  | inr x =>
    cases x with
    | inl x =>
      simp only [weightValue,qmaFourExchangeWeight]
      have h := crossValue_error k r (a x.1) (b x.1) (t x.1) x.2.1 x.2.2
      have hm := mul_le_mul_of_nonneg_right (ht x.1)
        (by positivity : 0 ≤ 1568*|(r:ℝ)| *(2:ℝ)⁻¹^k)
      unfold weightErrorBudget
      nlinarith
    | inr x =>
      cases x with
      | inl x =>
        simp only [weightValue,qmaFourExchangeWeight]
        split_ifs
        · have h := counterFieldA_error k (a x.1) (b x.1) (t x.1) x.2.2
          have hm := mul_le_mul_of_nonneg_right (ht x.1) heps
          unfold weightErrorBudget
          nlinarith
        · have h := counterFieldB_error k (a x.1) (b x.1) (t x.1) x.2.2
          have hm := mul_le_mul_of_nonneg_right (ht x.1) heps
          unfold weightErrorBudget
          nlinarith
      | inr x =>
        simp only [weightValue,qmaFourExchangeWeight]
        have h := fieldValue_error k (axis x.1) (weight x.1) x.2
        have hm := mul_le_mul_of_nonneg_right (hw x.1) heps
        unfold weightErrorBudget
        nlinarith

variable [Fintype κ] [Fintype τ]

theorem weightValue_ground_error (k : ℕ) (r : ℚ) (left right : κ → Fin n)
    (hne : ∀ e, left e ≠ right e) (a b : κ → Fin 2) (t : κ → ℚ)
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℚ)
    (s : ℚ) (c B D : ℝ) (hB : 0 ≤ B)
    (ht : ∀ e, |(t e:ℝ)| ≤ B) (hw : ∀ e, |(weight e:ℝ)| ≤ B)
    (hs : |(s:ℝ)-qmaFourExchangeScalar n (r:ℝ) axis (fun e => (weight e:ℝ)) c| ≤ D*(2:ℝ)⁻¹^k) :
    |MediatorGraph.normalizedBottom (qmaExchangeMatrix (qmaFourExchangeLeft left right site)
        (qmaFourExchangeRight left right site) (fun x => (weightValue k r a b t axis weight x:ℝ)) (s:ℝ))-
      MediatorGraph.normalizedBottom (qmaBlockSourceFull (r:ℝ) left right a b (fun e => (t e:ℝ))
        site axis (fun e => (weight e:ℝ)) c)| ≤
      (3*(Fintype.card (QMAFourExchangeIndex n κ τ):ℝ)*weightErrorBudget (r:ℝ) B+D)*(2:ℝ)⁻¹^k := by
  rw [qmaBlockSourceFull_exchange]
  apply (qmaExchangeMatrix_ground_error _ _ (qmaFourExchange_distinct left right site hne) _ _ _ _).trans
  have hsum : (∑ x : QMAFourExchangeIndex n κ τ,
      |(weightValue k r a b t axis weight x:ℝ)-
        qmaFourExchangeWeight (r:ℝ) a b (fun e => (t e:ℝ)) axis (fun e => (weight e:ℝ)) x|) ≤
      (Fintype.card (QMAFourExchangeIndex n κ τ):ℝ)*weightErrorBudget (r:ℝ) B*(2:ℝ)⁻¹^k := by
    calc
      _ ≤ ∑ _x : QMAFourExchangeIndex n κ τ, weightErrorBudget (r:ℝ) B*(2:ℝ)⁻¹^k :=
        Finset.sum_le_sum (fun x _ => weightValue_error k r a b t axis weight B hB ht hw x)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  nlinarith

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
