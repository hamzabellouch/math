import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Gram

namespace OAI

/-! Finite sums commute with the map from square-integrable functions
into L2. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [InnerProductSpace ℂ E] in
theorem finite_sum_toL2 (mu : Measure X) {ι : Type*} (S : Finset ι)
    (f : ι → X → E) (hf : ∀ i, MemLp (f i) 2 mu) :
    (memLp_finsetSum S (fun i _ => hf i)).toLp (fun x => ∑ i∈S, f i x)=
      ∑ i∈S, (hf i).toLp (f i) := by
  apply Lp.ext
  apply (MemLp.coeFn_toLp _).trans
  symm
  apply (Lp.coeFn_fun_finsetSum S (fun i => (hf i).toLp (f i))).trans
  filter_upwards [eventuallyEq_sum (s := S) (fun i _ => (hf i).coeFn_toLp)] with x hx
  simpa only [Finset.sum_apply] using hx

theorem finite_L2_sum_norm_sq (mu : Measure X) {ι : Type*} (S : Finset ι)
    (f : ι → X → E) (hf : ∀ i, MemLp (f i) 2 mu) :
    ‖∑ i∈S, (hf i).toLp (f i)‖^2=∫ x, ‖∑ i∈S, f i x‖^2 ∂mu := by
  rw [←finite_sum_toL2 mu S f hf]
  exact memLp_toL2_norm_sq mu _ _

end LipschitzHilbert

end

end OAI
