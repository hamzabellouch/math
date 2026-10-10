import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.ReducedTensor
import OAI.Analysis.Kaplansky.StableFiniteness.SimpleRepresentation
import OAI.Analysis.Kaplansky.Regular.ReducedStable
import OAI.Analysis.Kaplansky.Regular.PowersSimple

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder BigOperators
open Kaplansky Regular
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem tensor_properlyInfinite_of_no_trace {A : Type*} [CStarAlgebra A] [Nontrivial A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hτ : IsEmpty (TracialState A)) :
    ProperlyInfinite (tensorAlgebra (G:=F2) ρ) := by
  obtain ⟨n,y,hcol,hrow⟩ := finite_trace_obstruction hτ
  apply tensor_two_isometries_of_row_contraction ρ y ‖∑ i, y i*star (y i)‖
    (norm_nonneg _) hrow hcol
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ => mul_star_self_nonneg (y i))).le_algebraMap_norm_self

theorem simple_stable_tensor_reduction
    (h : ∃ (M : Type) (inst : CStarAlgebra M),
      letI := inst
      Nontrivial M ∧ CStarSimple M ∧ StablyFinite M ∧ IsEmpty (TracialState M)) :
    SimpleStableTensorCounterexample := by
  obtain ⟨M,inst,hM,hs,hf,ht⟩ := h
  let := inst
  let := hM
  obtain ⟨H,instH,innerH,completeH,ρ,hρ⟩ := simple_faithful_representation hs
  let := instH
  let := innerH
  let := completeH
  refine ⟨algebra_F2_simple,algebra_stablyFinite (G:=F2),M,inst,hM,hs,hf,H,instH,
    innerH,completeH,ρ,hρ,tensor_properlyInfinite_of_no_trace ρ ht⟩


end KaplanskyConsequences

end

end OAI
