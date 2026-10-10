import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialRealization

namespace OAI

/-! The literal initial scale has exactly the coefficient budget used in
the rational simultaneous path estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

theorem initial_list_sum {M : Type*} [AddCommMonoid M] (bs : List Bond) (f : Bond → M) :
    (bs.map f).sum=∑ e : Fin bs.length, f (bs.get e) := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map bs f).symm

theorem initialScale_eq (N : ℚ) (bs : List Bond) (c : ℚ) :
    initialScale N bs c=qmaRationalInitialScale (fun e : Fin bs.length => (bs.get e).2.2) c N := by
  unfold initialScale qmaRationalInitialScale
  rw [initial_list_sum,initial_list_sum]

theorem initialScale_cast (N : ℚ) (bs : List Bond) (c : ℚ) :
    (initialScale N bs c:ℝ)=
      qmaRoutingScale (3*∑ e : Fin bs.length, (1+2*|((bs.get e).2.2:ℝ)|))
        (|(c:ℝ)|+4*∑ e : Fin bs.length, (1+|((bs.get e).2.2:ℝ)|)^2) (N:ℝ) := by
  rw [initialScale_eq,qmaRationalInitialScale_cast]

end ContinuumCoulomb.QuantumForkList

end

end OAI
