import OAI.Geometry.PeriodicTiling.StackingContributions
import OAI.Geometry.PeriodicTiling.TilingTransport

namespace OAI

universe uH uK uι

namespace PeriodicTilingThree

section Stacking

variable {H : Type uH} {K : Type uK} {ι : Type uι} [AddCommGroup H] [AddCommGroup K]
variable [Fintype K] [Fintype ι]

theorem tiles_stack_lift
    {H : Type uH} {K : Type uK} {ι : Type uι}
    [AddCommGroup H] [AddCommGroup K] [Fintype K] [Fintype ι]
    {F : ι → Finset H} {E : ι → Finset K} {A : Set H}
    (hpart : IsColorPartition E) (hA : ∀ ν, Tiles (F ν) A) :
    Tiles (stack F E) (A ×ˢ ({0} : Set K)) := by
  classical
  apply tiles_iff_unique_tile.mpr
  intro x
  obtain ⟨ν, hν, _⟩ := hpart x.2
  obtain ⟨f, hf, huniq⟩ := tiles_iff_unique_tile.mp (hA ν) x.1
  refine ⟨⟨((f : H), x.2), mem_stack.mpr ⟨ν, f.property, hν⟩⟩, ?_, ?_⟩
  · change x.1 - (f : H) ∈ A ∧ x.2 - x.2 ∈ ({0} : Set K)
    exact ⟨hf, by simp⟩
  · intro y hy
    change x.1 - y.1.1 ∈ A ∧ x.2 - y.1.2 ∈ ({0} : Set K) at hy
    obtain ⟨μ, hyF, hyE⟩ := mem_stack.mp y.property
    have hy2 : y.1.2 = x.2 := (sub_eq_zero.mp (Set.mem_singleton_iff.mp hy.2)).symm
    have hμν : μ = ν := hpart.eq_of_mem (hy2 ▸ hyE) hν
    cases hμν
    have hy1 : (⟨y.1.1, hyF⟩ : ↥(F ν)) = f := huniq ⟨y.1.1, hyF⟩ hy.1
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val hy1) hy2

theorem fullyPeriodic_stack_lift {A : Set H} (hA : FullyPeriodic A) :
    FullyPeriodic (A ×ˢ ({0} : Set K)) :=
  hA.prod_singleton_zero

theorem fullyPeriodic_stack_project
    {H : Type uH} {K : Type uK}
    [AddCommGroup H] [AddCommGroup K] [Fintype K]
    {B : Set (H × K)} (hB : FullyPeriodic B) :
    FullyPeriodic (Prod.fst '' B) :=
  FullyPeriodic.image_of_surjective (AddMonoidHom.fst H K)
    (fun x => ⟨(x, 0), rfl⟩) hB

theorem exists_tiles_stack_iff {F : ι → Finset H} {E : ι → Finset K}
    (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty) :
    (∃ A : Set H, ∀ ν, Tiles (F ν) A) ↔
      ∃ B : Set (H × K), Tiles (stack F E) B := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A ×ˢ ({0} : Set K), tiles_stack_lift hpart hA⟩
  · rintro ⟨B, hB⟩
    exact ⟨Prod.fst '' B, tiles_of_tiles_stack hpart hfull hE hB⟩

theorem exists_fullyPeriodic_tiles_stack_iff
    {F : ι → Finset H} {E : ι → Finset K}
    (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty) :
    (∃ A : Set H, (∀ ν, Tiles (F ν) A) ∧ FullyPeriodic A) ↔
      ∃ B : Set (H × K), Tiles (stack F E) B ∧ FullyPeriodic B := by
  constructor
  · rintro ⟨A, hA, hperiod⟩
    exact ⟨A ×ˢ ({0} : Set K), tiles_stack_lift hpart hA,
      fullyPeriodic_stack_lift hperiod⟩
  · rintro ⟨B, hB, hperiod⟩
    exact ⟨Prod.fst '' B, tiles_of_tiles_stack hpart hfull hE hB,
      fullyPeriodic_stack_project hperiod⟩

theorem stack_counterexample_of_common_system [Nonempty ι]
    {F : ι → Finset H} {E : ι → Finset K}
    (hF : ∀ ν, (F ν).Nonempty) (hE : ∀ ν, (E ν).Nonempty)
    (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hcommon : ∃ A : Set H, ∀ ν, Tiles (F ν) A)
    (hnone : ∀ A : Set H, (∀ ν, Tiles (F ν) A) → ¬ FullyPeriodic A) :
    (stack F E).Nonempty ∧ (∃ B, Tiles (stack F E) B) ∧
      ∀ B, Tiles (stack F E) B → ¬ FullyPeriodic B := by
  refine ⟨stack_nonempty hF hE, (exists_tiles_stack_iff hpart hfull hE).mp hcommon, ?_⟩
  intro B hB hperiod
  exact hnone (Prod.fst '' B) (tiles_of_tiles_stack hpart hfull hE hB)
    (fullyPeriodic_stack_project hperiod)

end Stacking

end PeriodicTilingThree

end OAI
