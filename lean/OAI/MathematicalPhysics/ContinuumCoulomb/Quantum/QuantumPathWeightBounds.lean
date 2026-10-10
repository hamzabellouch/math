import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalPathStep

namespace OAI

/-! Uniform polynomial coefficient bounds for one physical path-subdivision layer. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaPathOffset_abs_le {J L : ℝ} (hL : 1 ≤ L) (hJ : |J| ≤ L) :
    |qmaPathOffset J| ≤ 4*L^2 := by
  have hJ2 : J^2 ≤ L^2 := by nlinarith [sq_abs J,mul_self_le_mul_self (abs_nonneg J) hJ]
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  rw [abs_of_nonneg (by unfold qmaPathOffset; positivity)]
  unfold qmaPathOffset
  nlinarith

theorem qmaPathAmplitude_abs_le {R J L : ℝ} (hL : 1 ≤ L) (hR : |R| ≤ L) (hJ : |J| ≤ L)
    (even : Bool) (a : Fin 2) : |qmaPathAmplitude even R J a| ≤ 2*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hL2 : L ≤ L^2 := by nlinarith
  have hp := mul_le_mul hR hJ (abs_nonneg J) hL0
  cases even <;> fin_cases a <;> simp [qmaPathAmplitude,abs_mul] <;> nlinarith

namespace QMARationalExchangeGraph

theorem subdivide_weight_abs_le (G : QMARationalExchangeGraph) (s : Finset G.Edge)
    (even : Fin s.card → Bool) (N : ℚ) {L : ℝ} (hL : 1 ≤ L)
    (hR : |(G.pathScale s N:ℝ)| ≤ L) (hw : ∀ e, |(G.weight e:ℝ)| ≤ L)
    (e : (G.subdivide s even N).Edge) : |((G.subdivide s even N).weight e:ℝ)| ≤ 2*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hL2 : L ≤ L^2 := by nlinarith
  rcases e with e | (i | ⟨i,a⟩)
  · exact (hw e.val).trans (by nlinarith)
  · change |(((G.pathScale s N)^2:ℚ):ℝ)| ≤ _
    push_cast
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (G.pathScale s N:ℝ),mul_self_le_mul_self (abs_nonneg _) hR]
  · change |(QuantumPathCode.coefficients (even i,G.pathScale s N,G.weight (qmaSelectedIndex s i))
        ⟨a.val+1,by omega⟩:ℝ)| ≤ _
    rw [QuantumPathCode.coefficients_spoke]
    exact qmaPathAmplitude_abs_le hL hR (hw _) _ _

theorem subdivide_constant_abs_le (G : QMARationalExchangeGraph) (s : Finset G.Edge)
    (even : Fin s.card → Bool) (N : ℚ) {L : ℝ} (hL : 1 ≤ L)
    (hR : |(G.pathScale s N:ℝ)| ≤ L) (hw : ∀ e, |(G.weight e:ℝ)| ≤ L) :
    |((G.subdivide s even N).constant:ℝ)| ≤ |(G.constant:ℝ)|+7*(s.card:ℝ)*L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hR2 : (G.pathScale s N:ℝ)^2 ≤ L^2 := by
    nlinarith [sq_abs (G.pathScale s N:ℝ),mul_self_le_mul_self (abs_nonneg _) hR]
  have hs : |∑ i : Fin s.card, qmaPathOffset (G.weight (qmaSelectedIndex s i):ℝ)| ≤
      (s.card:ℝ)*(4*L^2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _i : Fin s.card, 4*L^2 := Finset.sum_le_sum (fun i _ => qmaPathOffset_abs_le hL (hw _))
      _ = _ := by simp
  have hc := abs_add_le (G.constant:ℝ) (∑ i : Fin s.card, qmaPathOffset (G.weight (qmaSelectedIndex s i):ℝ))
  have hd := abs_add_le ((G.constant:ℝ)+∑ i : Fin s.card, qmaPathOffset (G.weight (qmaSelectedIndex s i):ℝ))
    (3*(s.card:ℝ)*(G.pathScale s N:ℝ)^2)
  rw [abs_of_nonneg (by positivity : 0 ≤ 3*(s.card:ℝ)*(G.pathScale s N:ℝ)^2)] at hd
  change |((((G.constant+∑ i : Fin s.card, (3/4+3*(G.weight (qmaSelectedIndex s i))^2))+
    3*(s.card:ℚ)*(G.pathScale s N)^2):ℚ):ℝ)| ≤ _
  push_cast
  change |((G.constant:ℝ)+∑ i : Fin s.card, qmaPathOffset (G.weight (qmaSelectedIndex s i):ℝ))+
    3*(s.card:ℝ)*(G.pathScale s N:ℝ)^2| ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hR2 (by positivity : 0 ≤ (s.card:ℝ))]

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
