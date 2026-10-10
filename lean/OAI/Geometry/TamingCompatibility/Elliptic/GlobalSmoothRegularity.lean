import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.LocalWeakPatch
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothPatchGlue

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

theorem weak_solution_smooth (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) :
    ∃ b : antiPre A J α hs ht, antiToEnergy A J α hs ht b = u := by
  classical
  choose V hV hxV w hw using exists_weak_patch A J α hs ht D hD f u heq
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion_of_mem x (hxV x))
  have hc : (univ : Set X) ⊆ ⋃ p : s, V p.val := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => V p.val) (fun p => hV p.val) hc
  apply glue_weak_patches A J α hs ht (fun p : s => ρ p) (fun p => (ρ p).contMDiff)
    (fun x => ?_) u (fun p : s => w p.val) (fun p => hw p.val (ρ p) (ρ p).contMDiff (hρ p))
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)

include hD in
lemma weak_kernel_smooth (u : antiEnergy A J α hs ht) (hu : weakDelta A J α hs ht u = 0) :
    ∃ b : antiPre A J α hs ht, antiToEnergy A J α hs ht b = u := by
  apply weak_solution_smooth A J α hs ht D hD 0 u
  intro v
  rw [hu,inner_zero_left]
  change 0 = ⟪smoothL2 A J α hs ht true 0,energyInclusion A J α hs ht v⟫
  rw [map_zero,inner_zero_left]

end TamingCompatibility.GeometricHilbert

end

end OAI
