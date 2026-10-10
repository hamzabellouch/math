import OAI.Analysis.KadisonSimilarity.Representation.L2HilbertSum
import Mathlib.Topology.Algebra.Module.Basic

namespace OAI

/-! The countable coordinate Hilbert space used by the spectral model is
separable, by approximation with its finite-coordinate vectors. -/

noncomputable section
namespace KadisonSimilarity
open TopologicalSpace

instance scalarHilbertCoordinates_separable (ι : Type*) [Countable ι] :
    SeparableSpace (ScalarHilbertCoordinates ι) := by
  classical
  let s : Set (ScalarHilbertCoordinates ι) :=
    Set.range (fun i : ι => lp.single (E := fun _ : ι => ℂ) 2 i 1)
  have hs : IsSeparable (Submodule.span ℂ s : Set (ScalarHilbertCoordinates ι)) :=
    (Set.countable_range _).isSeparable.span
  have hd : closure (Submodule.span ℂ s : Set (ScalarHilbertCoordinates ι)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro f
    apply mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top f)
    apply Filter.Eventually.of_forall
    intro t
    apply Submodule.sum_mem
    intro i _
    have hi : lp.single (E := fun _ : ι => ℂ) 2 i 1 ∈ Submodule.span ℂ s :=
      Submodule.subset_span ⟨i, rfl⟩
    simpa only [← lp.single_smul, smul_eq_mul, mul_one] using
      (Submodule.smul_mem (Submodule.span ℂ s) (f i) hi)
  exact isSeparable_univ_iff.mp (hd ▸ hs.closure)

end KadisonSimilarity

end

end OAI
