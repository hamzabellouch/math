import OAI.Algebra.Finitistic.Ordinary.OrdinaryProductProjective
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R] [Small.{v} L] [Small.{v} R]

omit [Small.{v} L] [Small.{v} R] in
/-- Exactness of actual inflation, with the module universe independent of the ring universe. -/
theorem firstInflation_preservesHomology :
    (firstInflation.{u,v} L R).PreservesHomology :=
  CategoryTheory.Functor.preservesHomology_of_map_exact _ (fun K hK => by
    rw [ShortComplex.moduleCat_exact_iff] at hK ⊢
    exact hK)

omit [Small.{v} R] in
/-- Inflation from a factor preserves finite projective-dimension bounds, via actual projective covers. -/
theorem firstInflation_dimensionLE (n : ℕ) (M : ModuleCat.{v} L) [HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE ((firstInflation L R).obj M) n := by
  induction n generalizing M with
  | zero =>
    have : Projective M := (projective_iff_hasProjectiveDimensionLT_one (X := M)).mpr inferInstance
    have := firstInflation_projective L R M
    infer_instance
  | succ n ih =>
    let S := M.projectiveShortComplex
    have hS := M.shortExact_projectiveShortComplex
    have : HasProjectiveDimensionLT S.X₁ (n+1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
    have hk := ih S.X₁
    have hp := firstInflation_projective L R S.X₂
    have := firstInflation_preservesHomology.{u,v} L R
    have : Mono ((firstInflation L R).map S.f) :=
      (ModuleCat.mono_iff_injective _).mpr ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
    have : Epi ((firstInflation L R).map S.g) :=
      (ModuleCat.epi_iff_surjective _).mpr ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)
    have hs : (S.map (firstInflation L R)).ShortExact := hS.map (firstInflation L R)
    exact (hs.hasProjectiveDimensionLT_X₃_iff n hp).mpr hk
end LittleFinitistic.ProductModules

end

end OAI
