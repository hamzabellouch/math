import OAI.Geometry.SingularHomology.HomologyConstant
import OAI.Geometry.SingularHomology.HomologyCycle

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

theorem realSingularChainComplex_exactAt_of_contractible
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    (realSingularChainComplex X).ExactAt n := by
  let := realSingularHomology_subsingleton_of_contractible n hn X
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (ModuleCat.isZero_of_subsingleton (RealSingularHomology n X))

theorem exists_realSingularChain_filling_of_contractible
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ)
    (z : (realSingularChainComplex X).X (n + 1))
    (hz : ((realSingularChainComplex X).d (n + 1) n).hom z = 0) :
    ∃ b : (realSingularChainComplex X).X (n + 2),
      ((realSingularChainComplex X).d (n + 2) (n + 1)).hom b = z := by
  let C := realSingularChainComplex X
  have h : (C.sc' (n + 2) (n + 1) n).Exact :=
    (C.exactAt_iff' (n + 2) (n + 1) n (ChainComplex.prev ℕ (n + 1))
      (ChainComplex.next_nat_succ n)).mp
        (realSingularChainComplex_exactAt_of_contractible X (n + 1) (by omega))
  exact (ShortComplex.moduleCat_exact_iff _).mp h z hz

abbrev realSingularCycles (X : Type) [TopologicalSpace X] (n : ℕ) :=
  LinearMap.ker ((realSingularChainComplex X).d (n + 1) n).hom

def realSingularBoundaryToCycles (X : Type) [TopologicalSpace X] (n : ℕ) :
    (realSingularChainComplex X).X (n + 2) →ₗ[ℝ] realSingularCycles X n :=
  ((realSingularChainComplex X).sc' (n + 2) (n + 1) n).moduleCatToCycles

@[simp] theorem realSingularBoundaryToCycles_val
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : (realSingularChainComplex X).X (n + 2)) :
    (realSingularBoundaryToCycles X n b).val =
      ((realSingularChainComplex X).d (n + 2) (n + 1)).hom b := rfl

theorem realSingularBoundaryToCycles_surjective_of_contractible
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) :
    Function.Surjective (realSingularBoundaryToCycles X n) := by
  intro z
  obtain ⟨b, hb⟩ := exists_realSingularChain_filling_of_contractible X n z.val z.property
  exact ⟨b, Subtype.ext hb⟩

theorem exists_linear_realSingularCycleFilling_of_contractible
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) :
    ∃ fill : realSingularCycles X n →ₗ[ℝ] (realSingularChainComplex X).X (n + 2),
      (realSingularBoundaryToCycles X n).comp fill = LinearMap.id := by
  exact (realSingularBoundaryToCycles X n).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr
      (realSingularBoundaryToCycles_surjective_of_contractible X n))

def realSingularCycleFilling (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) : realSingularCycles X n →ₗ[ℝ] (realSingularChainComplex X).X (n + 2) :=
  Classical.choose (exists_linear_realSingularCycleFilling_of_contractible X n)

@[simp] theorem realSingularBoundaryToCycles_filling
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ)
    (z : realSingularCycles X n) :
    realSingularBoundaryToCycles X n (realSingularCycleFilling X n z) = z := by
  exact LinearMap.congr_fun
    (Classical.choose_spec (exists_linear_realSingularCycleFilling_of_contractible X n)) z

@[simp] theorem realSingularCycleFilling_boundary
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ)
    (z : realSingularCycles X n) :
    ((realSingularChainComplex X).d (n + 2) (n + 1)).hom
      (realSingularCycleFilling X n z) = z.val :=
  congrArg Subtype.val (realSingularBoundaryToCycles_filling X n z)

theorem realSingularCycleFilling_map_boundary
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [ContractibleSpace X]
    (f : X → Y) (hf : Continuous f) (n : ℕ) (z : realSingularCycles X n) :
    ((realSingularChainComplex Y).d (n + 2) (n + 1)).hom
      (((realSingularChainMap f hf).f (n + 2)).hom (realSingularCycleFilling X n z)) =
        ((realSingularChainMap f hf).f (n + 1)).hom z.val := by
  have h := congrArg
    (fun k : (realSingularChainComplex X).X (n + 2) ⟶
      (realSingularChainComplex Y).X (n + 1) => k.hom (realSingularCycleFilling X n z))
    ((realSingularChainMap f hf).comm (n + 2) (n + 1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, realSingularCycleFilling_boundary]
    using h

end Problem340

end

end OAI
