import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.FinrankSpanAlgebraMapImage

namespace OAI

namespace SiegelZeros

open Module Submodule
namespace WeightedTorusJets.Geometry

theorem algebraMap_mem_span_image_iff {K L n : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype n] (s : Set (n → K)) (v : n → K) :
    (algebraMap K L ∘ v) ∈ span L ((fun w : n → K => algebraMap K L ∘ w) '' s) ↔
      v ∈ span K s := by
  let φ := Pi.algebraMap n K L
  constructor
  · intro hv
    have hd : finrank K (span K s) = finrank K (span K (insert v s)) := by
      rw [← finrank_span_algebraMap_image (L := L) s,
        ← finrank_span_algebraMap_image (L := L) (insert v s), Set.image_insert_eq,
        Submodule.span_insert_eq_span hv]
    have heq := Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_mono (Set.subset_insert v s)) hd
    rw [heq]
    exact Submodule.subset_span (Set.mem_insert v s)
  · intro hv
    exact Submodule.span_subset_span K L (φ '' s)
      (Submodule.apply_mem_span_image_of_mem_span φ hv)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

theorem greedyPivots_algebraMap {K L n : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype n] (v : ℕ → n → K) (T : ℕ) :
    greedyPivots L (fun i => algebraMap K L ∘ v i) T = greedyPivots K v T := by
  ext i
  rw [mem_greedyPivots_iff, mem_greedyPivots_iff]
  have h := Geometry.algebraMap_mem_span_image_iff (L := L)
    (v '' (Finset.range i : Set ℕ)) (v i)
  simpa only [Set.image_image, Function.comp_def] using and_congr_right (fun _ => not_congr h)

end WeightedTorusJets


end SiegelZeros

end OAI
