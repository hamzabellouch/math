import OAI.Algebra.Finitistic.Bar.DirectSumCoproduct
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum
noncomputable section
namespace DerivedBar
universe u
variable (D : Type u) [Ring D]
  (S : ℕ → ChainComplex (ModuleCat.{u} D) ℕ)

theorem directSumComplex_d (i j : ℕ) :
    ((directSumComplex S).d i j).hom = DirectSum.lmap (fun r => ((S r).d i j).hom) := by
  by_cases h : j+1=i
  · subst i
    simp only [directSumComplex, ChainComplex.of_d, ModuleCat.hom_ofHom]
    rfl
  · have hrel : ¬ (ComplexShape.down ℕ).Rel i j := h
    rw [(directSumComplex S).shape i j hrel]
    have hf : (fun r => ((S r).d i j).hom) = (fun r => (0 : (S r).X i →ₗ[D] (S r).X j)) := by
      funext r
      rw [(S r).shape i j hrel, ModuleCat.hom_zero]
    rw [hf]
    apply LinearMap.ext
    intro v
    apply DFinsupp.ext
    intro r
    rfl

/-- The original componentwise direct sum is exact at a degree whenever every
summand is exact there. This includes the degree-zero boundary. -/
theorem directSumComplex_exactAt (n : ℕ) (h : ∀ r, (S r).ExactAt n) :
    (directSumComplex S).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (((directSumComplex S).d ((ComplexShape.down ℕ).prev n) n).hom) =
    LinearMap.ker (((directSumComplex S).d n ((ComplexShape.down ℕ).next n)).hom)
  erw [directSumComplex_d, directSumComplex_d, DirectSum.range_lmap, DirectSum.ker_lmap]
  congr 2
  funext r
  exact ShortComplex.Exact.moduleCat_range_eq_ker (h r)

theorem directSumComplex_homology_zero (n : ℕ) (h : ∀ r, IsZero ((S r).homology n)) :
    IsZero ((directSumComplex S).homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact directSumComplex_exactAt D S n
    (fun r => (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (h r))
end DerivedBar

end

end OAI
