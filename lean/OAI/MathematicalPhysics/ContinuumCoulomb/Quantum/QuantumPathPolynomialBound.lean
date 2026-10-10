import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathWeightBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathSchedule

namespace OAI

/-! Explicit polynomial coefficient envelopes for the actual selected path
subdivision, uniform in the selected set and its parity choices. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaPathBudget (m L : ℝ) : ℝ :=
  3*m*L+L+3*m*(1+2*L)+4*m*(1+L)^2+1

def qmaPathRadiusBound (m L T : ℝ) : ℝ :=
  L+16*(qmaPathBudget m L)^3*T+4*qmaPathBudget m L+1

def qmaPathCoefficientBound (m L T : ℝ) : ℝ :=
  1+L+(7*m+2)*(qmaPathRadiusBound m L T)^2

namespace QMARationalExchangeGraph
variable (G : QMARationalExchangeGraph)

def CoefficientBound (L : ℝ) : Prop :=
  |(G.constant:ℝ)| ≤ L ∧ ∀ e, |(G.weight e:ℝ)| ≤ L

theorem pathScale_abs_bound (s : Finset G.Edge) {N : ℚ} (hN : 0 ≤ N)
    {m L T : ℝ} (hm : (Fintype.card G.Edge:ℝ) ≤ m) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : G.CoefficientBound L) :
    |(G.pathScale s N:ℝ)| ≤ qmaPathRadiusBound m L T := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hn0 : 0 ≤ (N:ℝ) := by exact_mod_cast hN
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hs0 : (s.card:ℝ) ≤ (Fintype.card G.Edge:ℝ) := by exact_mod_cast Finset.card_le_univ s
  have hs : (s.card:ℝ) ≤ m := hs0.trans hm
  have hr0 : (Fintype.card {e : G.Edge // e ∉ s}:ℝ) ≤ (Fintype.card G.Edge:ℝ) := by
    exact_mod_cast Fintype.card_subtype_le (fun e : G.Edge => e ∉ s)
  have hr : (Fintype.card {e : G.Edge // e ∉ s}:ℝ) ≤ m := hr0.trans hm
  have hret : (∑ e : {e : G.Edge // e ∉ s}, |(G.weight e.val:ℝ)|) ≤ m*L := by
    calc
      _ ≤ ∑ _e : {e : G.Edge // e ∉ s}, L := Finset.sum_le_sum (fun e _ => hc.2 e.val)
      _ = (Fintype.card {e : G.Edge // e ∉ s}:ℝ)*L := by simp
      _ ≤ m*L := mul_le_mul_of_nonneg_right hr hL0
  have ha : (∑ i : Fin s.card, (1+2*|(G.weight (qmaSelectedIndex s i):ℝ)|)) ≤ m*(1+2*L) := by
    calc
      _ ≤ ∑ _i : Fin s.card, (1+2*L) := Finset.sum_le_sum (fun i _ => by linarith [hc.2 (qmaSelectedIndex s i)])
      _ = (s.card:ℝ)*(1+2*L) := by simp [mul_add]
      _ ≤ m*(1+2*L) := mul_le_mul_of_nonneg_right hs (by positivity)
  have hd : (∑ i : Fin s.card, (1+|(G.weight (qmaSelectedIndex s i):ℝ)|)^2) ≤ m*(1+L)^2 := by
    calc
      _ ≤ ∑ _i : Fin s.card, (1+L)^2 := Finset.sum_le_sum (fun i _ =>
        pow_le_pow_left₀ (by positivity) (by linarith [hc.2 (qmaSelectedIndex s i)]) 2)
      _ = (s.card:ℝ)*(1+L)^2 := by simp
      _ ≤ m*(1+L)^2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  let A : ℝ := 3*∑ i : Fin s.card, (1+2*|(G.weight (qmaSelectedIndex s i):ℝ)|)
  let D : ℝ := 3*(∑ e : {e : G.Edge // e ∉ s}, |(G.weight e.val:ℝ)|)+
    |(G.constant:ℝ)|+4*∑ i : Fin s.card, (1+|(G.weight (qmaSelectedIndex s i):ℝ)|)^2
  have hAD0 : 0 ≤ A+D+1 := by dsimp [A,D]; positivity
  have hAD : A+D+1 ≤ qmaPathBudget m L := by dsimp [A,D,qmaPathBudget]; linarith [hc.1]
  have hcube := pow_le_pow_left₀ hAD0 hAD 3
  rw [G.pathScale_cast]
  change |16*(A+D+1)^3*(N:ℝ)+4*(A+D+1)+1| ≤ _
  rw [abs_of_nonneg (by positivity)]
  have hnT : (N:ℝ) ≤ T := by simpa only [abs_of_nonneg hn0] using hT
  have hprod := mul_le_mul hcube hnT
    hn0 (pow_nonneg (hAD0.trans hAD) 3)
  dsimp [qmaPathRadiusBound]
  nlinarith

theorem subdivide_coefficientBound (s : Finset G.Edge) (even : Fin s.card → Bool)
    {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ} (hm : (Fintype.card G.Edge:ℝ) ≤ m)
    (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : G.CoefficientBound L) :
    (G.subdivide s even N).CoefficientBound (qmaPathCoefficientBound m L T) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hb0 : 0 ≤ qmaPathBudget m L := by unfold qmaPathBudget; positivity
  have hrad : L ≤ qmaPathRadiusBound m L T := by
    unfold qmaPathRadiusBound
    have h : 0 ≤ 16*(qmaPathBudget m L)^3*T := by positivity
    linarith
  have hr1 : 1 ≤ qmaPathRadiusBound m L T := hL.trans hrad
  have hr := G.pathScale_abs_bound s hN hm hL hT hc
  have hw : ∀ e, |(G.weight e:ℝ)| ≤ qmaPathRadiusBound m L T :=
    fun e => (hc.2 e).trans hrad
  have hs0 : (s.card:ℝ) ≤ (Fintype.card G.Edge:ℝ) := by exact_mod_cast Finset.card_le_univ s
  have hs : (s.card:ℝ) ≤ m := hs0.trans hm
  constructor
  · have h := G.subdivide_constant_abs_le s even N hr1 hr hw
    have hm' := mul_le_mul_of_nonneg_right hs (sq_nonneg (qmaPathRadiusBound m L T))
    unfold qmaPathCoefficientBound
    nlinarith [hc.1]
  · intro e
    have h := G.subdivide_weight_abs_le s even N hr1 hr hw e
    unfold qmaPathCoefficientBound
    nlinarith [sq_nonneg (qmaPathRadiusBound m L T),
      mul_nonneg hm0 (sq_nonneg (qmaPathRadiusBound m L T))]

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
